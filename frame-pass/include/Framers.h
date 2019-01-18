
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ValueTracking.h"

#include "llvm/Transforms/FramerLoopOpt/CheckInfo.h"
#include "llvm/Transforms/FramerLoopOpt/Utility.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../../../../../llvm-4.0.0.src/lib/IR/ConstantsContext.h"
#include <utility>

#define NOTSAFESTATICALLY   0 //requiring runtime check
#define SAFESTATICALLY      1
#define COMPAREIDXATRUNTIME 2
#define OUTOFBOUNDATRUNTIME 3 //should not be called at runtime.
#define COMPTYPEATRUNTIME   4
#define COMPSIZEATRUNTIME   5 


//#define FRAMERDEBUG
#ifdef FRAMERDEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

static char * prefix_of_hookGV_name = "FRAMER_";
static char * prefix_of_hookfunc_name = "FRAMER_forall_";
static char * prefix_of_supplementary_funcName = "FRAMER_supplementary_";

struct FieldT 
{ 
   short offset, typeID, size; 
}; 

using namespace llvm;
using namespace std;

static unsigned 
getPrimTyBits (unsigned Typeid)
{
    unsigned bitnum;

    switch (Typeid) {
        case 1: bitnum = 16; break;
        case 2: bitnum = 32; break;
        case 3: bitnum = 64; break;
        case 4: bitnum = 80; break;
        case 5: bitnum = 128; break;
        case 6: bitnum = 128; break;
        default: errs()<<"?? \n"; exit(0);
    }
    return bitnum;
}

static uint64_t 
getBitwidthOfStruct (StructType * STy, const DataLayout * dlayout)
{
    if (!STy->isSized()) {
        errs()<<"structure "<<*STy<<"is not sized!! \n";
        exit(0);
    }
    const StructLayout * strtlayout = dlayout->getStructLayout (STy);
    return (unsigned)strtlayout->getSizeInBits();

}

static unsigned 
getNumBits (Type * allocatedType, 
             const DataLayout * dlayout)
{
    /// #Bits of element type. (e.g. int->32, struct->sum of member bits, 
    /// array->#bits of array element. 
    /// (outmost element, if the array is array of array...)
    unsigned allocatedTyID = allocatedType->getTypeID();
     
    if ((allocatedTyID > Type::VoidTyID 
         && allocatedTyID < Type::PPC_FP128TyID)){
        return getPrimTyBits (allocatedTyID); //TODO. maybe we can use llvm's func ?
    }
    else if (IntegerType * intTy= dyn_cast<IntegerType>(allocatedType)) {
        return intTy->getBitWidth();
    }
    else if (isa<CompositeType>(allocatedType)) {
        if (isa<PointerType>(allocatedType)) {
            return dlayout->getPointerSizeInBits(); //8 bytes..
        }
        else if (StructType * structTy = dyn_cast<StructType>(allocatedType)) {
            return (unsigned) getBitwidthOfStruct (structTy, dlayout);
        }
        else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
            return (unsigned)(arrayTy->getNumElements())*getNumBits(arrayTy->getElementType(), dlayout); 
        }
        else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {
            if (vecty->getBitWidth()!=0) {
                return vecty->getBitWidth();
            }
            else {
                return (unsigned)(vecty->getNumElements())*getNumBits(vecty->getElementType(), dlayout); 
            }
        }
        else {
            errs()<<"1. what type is this??\n";
            exit(0);
        }
    }
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else {
        errs()<<"2. What type is this?!\n";
        exit(0);
    }
}


static bool 
isHookFamilyFunction (Function * F ) 
{ /* False when this function is from static lib whose functions are added to target */ 
    StringRef funcName = F->getName();

    if ( funcName.startswith(prefix_of_hookfunc_name)  //if it's hook func
        || funcName.startswith ("FRAMER_") 
        || funcName.startswith(prefix_of_supplementary_funcName)
       // || funcName.equals( StringRef("do_initializing"))
        || funcName.startswith("__wrap_malloc")
        || funcName.startswith("__wrap_free")) 
        {
         dbg(errs()<<"HOOK FAMILY\n";)
         //or sumplementary hook
        
        return true; 
    }
    else {
        return false;
    }
}
template < typename T>
short getIdx(vector<T> & vecOfElements, T element)
{
	short result= -1;
	// Find given element in vector
	auto it = find(vecOfElements.begin(), vecOfElements.end(), element);

	if (it != vecOfElements.end())
	{
		result = (short)distance(vecOfElements.begin(), it);
	}
	return result;
}

static void
createAllTypeList(vector<Type*> & AllTypeList, Module & M)
{
    /// (1) insert BasicTypes and their Pointertype to the vector
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::VoidTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::HalfTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::FloatTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::DoubleTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::X86_FP80TyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::FP128TyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::PPC_FP128TyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::LabelTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::MetadataTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::X86_MMXTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::TokenTyID));
    
    /// (2) insert all inttypes.
    AllTypeList.push_back(IntegerType::get(M.getContext(), 8));       
    AllTypeList.push_back(IntegerType::get(M.getContext(), 16));
    AllTypeList.push_back(IntegerType::get(M.getContext(), 32));
    AllTypeList.push_back(IntegerType::get(M.getContext(), 64));      
    AllTypeList.push_back(IntegerType::get(M.getContext(), 128));      
    AllTypeList.push_back(IntegerType::get(M.getContext(), 1));    
    AllTypeList.push_back(IntegerType::get(M.getContext(), 48));       

    // (3) insert Struct types and its field types.
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    
    for (vector<StructType*>::iterator it=temp.begin(),
            ie=temp.end();it!=ie;++it) {

        StructType * sty= (*it);

        if (sty->isOpaque()) {
            errs()<<"OPAQUE:" <<*sty<<". Check what I should do. \n"; 
            exit(0);     
            continue; // hm..should I skip this?
        }
        
        // * in this vrsion of SpaceMiu, we do not deal with packedstructure.
        // * to handle them, we need to consider offsets in reference rules. 
        if (sty->isPacked()) continue;
        
        // * now identified types in llvm are not structurally uniqued.
        if (sty->getName().startswith("struct.FRAMER")) continue; 
        
      /////////  
        if (sty->getName().startswith("union.")) {
       
            const DataLayout * dlayout= &M.getDataLayout();
            const StructLayout * slayout= dlayout->getStructLayout(sty);
            
            errs()<<"UNION- "<<*sty<<"\n";
            
            for (unsigned x=0; x<sty->getNumElements(); x++) {
                errs()<<"\telem "<<x<<": "<<*sty->getElementType(x)<<"\n";
                errs()<<"\t  offset"<<slayout->getElementOffset(x)<<"\n";
            }
            errs()<<"  alignment: "<<slayout->getAlignment()<<"\n";
        }
      /////////
        
        if (getIdx(AllTypeList, (Type*)sty) < 0) {
            AllTypeList.push_back(sty);
        }
        
        for (unsigned i=0; i<sty->getNumElements(); i++) {
            if (0 > getIdx(AllTypeList, sty->getElementType(i))) {
                AllTypeList.push_back(sty->getElementType(i)); 
            }
        } 
    }
    // (4) insert types used in bitcast. 
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
        if (isHookFamilyFunction (&*mi)) {
            continue;
        }
        for (Function::iterator bit=(*mi).begin();bit!=(*mi).end();++bit) {
            for (BasicBlock::iterator iit=(*bit).begin();iit!=(*bit).end();++iit) {
                
                if (!isa<BitCastOperator>(iit)) continue;
                
                BitCastOperator * bc= cast<BitCastOperator>(iit);
                errs()<<"bitcast: "<<*bc<<"\n"; 
                assert (isa<PointerType>(bc->getSrcTy()) 
                        && isa<PointerType>(bc->getDestTy()));
                
                PointerType * spty= cast<PointerType>(bc->getSrcTy());
                PointerType * dpty= cast<PointerType>(bc->getDestTy());
                
                if (0 > getIdx(AllTypeList, spty->getElementType())) {
                    errs()<<"adding 1: "<<*spty->getElementType()<<"\n";
                    
                    AllTypeList.push_back(spty->getElementType());
                }
                
                if (0 > getIdx(AllTypeList, dpty->getElementType())) {
                    
                    errs()<<"adding 2: "<<*dpty->getElementType()<<"\n";
                    AllTypeList.push_back(dpty->getElementType());
                }
            }
        }
    }
}

static void 
buildFields (Type * ty, vector<short> & fields, vector<Type*> & tlist)
{
    if (ty->isVoidTy()) {
        return;
    }
    else if (isa<StructType>(ty)) {
        StructType * sty= cast<StructType>(ty);
        for (unsigned i=0;i<sty->getNumElements();i++) {
            buildFields(sty->getElementType(i), fields, tlist);    
        }
    }
    else if (isa<ArrayType>(ty)) {
        ArrayType * aty= cast<ArrayType>(ty);
        for (uint64_t i=0;i<aty->getNumElements();i++) {
            buildFields(aty->getElementType(), fields, tlist);    
        }
    }
    else {
        short result= getIdx(tlist, ty);
        assert(result>=0);
        fields.push_back(result);
        return;
    }
    return;
}

static bool 
isSafelyCastedTo (Type * src, Type * dest, 
                vector<Type*> & tlist,
                vector<vector<short>> & safecasts)
{
    short stid= getIdx(tlist, src);
    short dtid= getIdx(tlist, dest);
    
    for (unsigned i=0;i<(safecasts.at(stid)).size();i++) {
        short tyid= (safecasts.at(stid)).at(i); 
        if (tyid==dtid) {
        return true;
        }
    }
    return false;
}

static bool 
isVoidPtrCast(Type * VoidOrChar, Type * subty)
{
    // one of args is not pointers.
    if (!isa<PointerType>(VoidOrChar) || !isa<PointerType>(subty)) {
        return false;
    }
     
    Type * src= VoidOrChar; //should be a void or int8 ptr.
    Type * dest= subty;

    PointerType * ptsrc= nullptr;
    PointerType * ptdest= nullptr;

    /// strip off both type's pointers.

    while(true) {
        ptsrc= dyn_cast<PointerType>(src);
        ptdest= dyn_cast<PointerType>(dest);

        if (ptsrc==nullptr || ptdest==nullptr) {
            break;     
        }

        src= ptsrc->getElementType(); 
        dest= ptdest->getElementType(); 
    }
     
    if (src->isIntegerTy(8) || src->isVoidTy()) {
        return true;         
    }
    /*if (PointerType * srctemp= dyn_cast<PointerType>(ptsrc)) {
        if((srctemp->getElementType())->isIntegerTy(8) ||
                (srctemp->getElementType())->isVoidTy())
            return false; 
    }*/

    return false; 
}


static bool
isDownCast (Type * src, Type * dest, 
            vector<Type*> & tlist,
            vector<vector<short>> & downcasts)
{
    if (isVoidPtrCast(src, dest)) {
       return true;  
    }
    
    short srcid= getIdx(tlist, src);
    short destid= getIdx(tlist, dest);
  
    errs()<<"src: "<<*src<<", dest: "<<*dest<<"\n"; 
    
    //assert(srcid>=0 && destid>=0);

    // packed structures are not included in AllTypeList.
    if (srcid<0 || destid <0) return false;   

    short idx= getIdx(downcasts.at(srcid), destid);
    
    if (idx < 0) {
        return false;      
    }
    /* 
    for (unsigned i=0;i<(downcasts.at(srcid)).size();i++) {
        short tyid= (downcasts.at(srcid)).at(i); 
        if (tyid==destid) {
            return true;
        }
    }
    */
    return true;
}

/*  return 1: void ptr downcast (e.g. i8*->tau*, void*->tau*)
    2: void ptr upcast(SRC: tau*-> Dest: i8*)
    0: neither of them.   
*/

static bool
isConversibleTo(vector<short> & from, 
                vector<short> & to,
                vector <Type*> & tlist, 
                vector<vector<short>> & llist, 
                const DataLayout * dlayout) 
{
    if (from.size() < to.size()) return false;
    
    if (from.size()==0 && to.size()==0) return true;   //e.g. void?       
    
    for(unsigned i=0;i<to.size();i++) {
       
        Type* fromT= tlist.at(from.at(i)); 
        Type* toT= tlist.at(to.at(i));
        
        if (!fromT->isSized() || !toT->isSized()) {
            return false; 
        }
            
        if (isa<PointerType>(fromT) || isa<PointerType>(toT)){
            /// physicallyEqual(fromT,toT)-> physicallyEqual(fromT*,toT*)
            
            if (!isa<PointerType>(fromT) || !isa<PointerType>(toT)) {
                return false; 
            }
            // now both are pointers.
            
            Type * felemT= (cast<PointerType>(fromT))->getElementType(); 
            Type * telemT= (cast<PointerType>(toT))->getElementType(); 
            
            // result type is void --> valid conversion in C (not in C++)
            

            short f_idx= getIdx(tlist, felemT);             
            short to_idx= getIdx(tlist, telemT);             
            
            
            assert(f_idx>=0 && to_idx>=0);
             
            if( !isConversibleTo (llist.at(f_idx), llist.at(to_idx), 
                                    tlist, llist, dlayout)) {
                return false;
            }
        }
         
        uint64_t fsize= dlayout->getTypeSizeInBits(fromT);
        uint64_t tsize= dlayout->getTypeSizeInBits(toT);
        
        if (fsize!=tsize){ // TODO. pointertype? t1*, ty* 
            return false; 
        }

        if ((fromT->isIntegerTy() && toT->isFloatingPointTy())
            || (toT->isIntegerTy() && fromT->isFloatingPointTy())) {
            return false; 
        }
    }  
    return true; 
}

static void 
createLayOutList(vector<Type*> & tlist,
                 vector<vector<short>> & llist)
{
    for (unsigned i=0;i<tlist.size();i++){
        vector<short> fields;
        
        buildFields(tlist.at(i), fields, tlist); 
        llist.push_back(fields);
    }
}

static void
createSafeCastList (vector<Type*> & tlist, 
                    vector<vector<short>> & safecasts,
                    vector <vector<short>> & llist,
                    const DataLayout * dlayout) 
{
 for (unsigned i=0;i<tlist.size();i++) { 
        
        vector<short> inter; 
        
        for(unsigned j=0; j<tlist.size(); j++) {
        
            //if int8*->T* upcast
            if (isVoidPtrCast(tlist.at(j), tlist.at(i))) { 
                if (getIdx(inter,(short)j) >= 0) {
                    continue; 
                }
                inter.push_back((short)j);
            }
            if (isConversibleTo(llist.at(i), llist.at(j),
                                tlist, llist, dlayout)) {
                 
                if (getIdx(inter,(short)j) >= 0) {
                    continue; 
                }
                inter.push_back((short)j);               
            }
        }
        safecasts.push_back(inter);
    }
}

static void
getSubTyOffsets(Type * ty, 
                vector<Type*> & tlist, 
                pair<short, vector<short>> & tidsPerDist,
                short preoffset,
                vector <pair<short, vector<short>>> & onety,
                vector <vector<short>> & safecasts,
                const DataLayout * dlayout)
{
    short tidx= getIdx(tlist, ty);
    assert(tidx >= 0);
    
    /*(tidsPerDist.second).push_back(tidx); */
    
    // * for each ty, for each offset, we save a list of tyids, *
    // * that the type at the offset is safely casted to.
     
    for (unsigned i=0; i<(safecasts.at(tidx)).size(); i++) {
        
        short onesafe= (safecasts.at(tidx)).at(i);         
        
        if (getIdx(tidsPerDist.second, onesafe) < 0) {      
       
            (tidsPerDist.second).push_back(onesafe);   
        }
    }
    //
     
    if (StructType * sty= dyn_cast<StructType>(ty)) {  
        
        const StructLayout * slayout= dlayout->getStructLayout(sty); 
              
        for (unsigned j=0; j<sty->getNumElements(); j++) {
           
            Type * subty= sty->getElementType(j);
            
            short offset= slayout->getElementOffset(j); 
            short current_offset= preoffset+offset; 
             
            tidsPerDist.first= current_offset;
            
            getSubTyOffsets (subty, tlist, tidsPerDist,
                             current_offset, onety, safecasts, dlayout);           
            
        }
    }
    else if (ArrayType * aty= dyn_cast<ArrayType>(ty)) {
        
        Type * elty= aty->getElementType();
        short elsize= getNumBits(elty, dlayout)/8;
        
        for (unsigned j=0; j<aty->getNumElements(); j++) {
       
            short offset= elsize * (short)j; 
            short current_offset= preoffset + offset; 
            
            tidsPerDist.first= current_offset;
            
            getSubTyOffsets (elty, tlist, tidsPerDist,
                             current_offset, onety, safecasts, dlayout);           
        }
    }
    else {
        // bottom case: isAtomicTy (int,float, MMX, vector etc)
        
        onety.push_back(tidsPerDist);
         
        // * pair<offset, tidsPerOffset> creation at new offset.
        (tidsPerDist.second).clear();  
        
    }
}

static unsigned 
getMaxCount_offsets (vector <vector<pair<short, vector<short>>>> & offsets,
                     unsigned & totaloffsetcount, // total count of pairs
                     unsigned & maxtysperoff,
                     unsigned & maxoffsperty)  // the max of pair.second.size 
{
  unsigned maxoffval= 0;
   
  for(unsigned i=0; i<offsets.size(); i++) {
   
    unsigned offsetnumperty= (offsets.at(i)).size();
    
    if (maxoffsperty < offsetnumperty) {
        maxoffsperty= offsetnumperty;   
    }
   
    totaloffsetcount= totaloffsetcount + offsetnumperty;
     
    for (unsigned j=0; j<(offsets.at(i)).size(); j++) {
    
      unsigned val= (unsigned)((offsets.at(i)).at(j)).first;
      
      if (maxoffval < val) {
        maxoffval= val;
      }
      
      unsigned castscount= (((offsets.at(i)).at(j)).second).size();

      if (maxtysperoff < castscount) {
        maxtysperoff= castscount;  
      }
      
    }
  }
  assert(maxtysperoff!=0);
  return maxoffval;
}
static uint64_t
mergeKey (short tid, short offset, unsigned maxoffsetval, unsigned & divider)
{
    divider= 10;
      
    while(true) {
        unsigned remainder= maxoffsetval % divider;
        if (remainder==maxoffsetval) {
            break;
        }
        divider= divider*10;
    }
    
    return (tid*divider)+offset;

}

// ** backup for the rt table.. not used now.
/*
static void 
createRTOffsetTable_version1 (vector <Type*> & tlist, 
                     vector<vector<short>> & safecasts, 
                     vector <vector<pair<short, vector<short>>>> & offsets,
                     unsigned & totaloffsetcount,
                     unsigned & maxtysperoff, 
                     unsigned & maxoffsetval,
                     unsigned & tblentrysize,
                     unsigned & divider,
                     GlobalVariable * rtOffsetTbl, 
                     Module & M)
{
  assert(offsets.size()==tlist.size());
    
  const DataLayout * dlayout= &M.getDataLayout(); 
    
  maxoffsetval= getMaxCount_offsets (offsets, 
                                 totaloffsetcount, 
                                 maxtysperoff);
             
  errs()<<"totaloffsetcount: "<<totaloffsetcount<<"\n";
  errs()<<"maxtysperoff: "<<maxtysperoff<<"\n";
  errs()<<"maxoffsetval: "<<maxoffsetval<<"\n";

  Type* int64T= IntegerType::getInt64Ty(M.getContext());
  Type* int16T= IntegerType::getInt16Ty(M.getContext());

  // * a list of tids of types at the offset can be safely casted to * 
  // * create an array of tyids * 
  // * for each offset/tid {short[maxtysperoff]} *
   
  ArrayType* SafeTidsTy= ArrayType::get (int16T, maxtysperoff); 
  
  // * Desirable TypeTable entry type *
  // * {uint64_t, {short[maxtysperoff]}} *
 
  vector<Type*> entryTyList= {int64T, SafeTidsTy};
    
  StructType* tableEntryTy= StructType::create(M.getContext(), 
                          entryTyList,"EntryTyOffsetTable");

  vector<Constant*> rttable;
    
  for (unsigned tid=0; tid<offsets.size(); tid++) {

    for (unsigned ofs=0; ofs<(offsets.at(tid)).size(); ofs++) {
     
      vector<Constant*> entrylist;
      
      pair <short, vector<short>> onep= (offsets.at(tid)).at(ofs);
     
      // create a key from tid and onep.first(offset)
      uint64_t mergedKey= mergeKey(tid, onep.first, maxoffsetval, divider);
       
      Constant* cKey= ConstantInt::get(int64T, mergedKey); 
      
      entrylist.push_back(cKey);
      
      vector <Constant*> dataperkey; // key{tid,offset} 
         
      for (unsigned cst=0; cst< maxtysperoff; cst++) {
        
        short val= -1;

        if (cst < (onep.second).size()) {  
            val= (onep.second).at(cst);
        }
        Constant * conscst= ConstantInt::get(int16T, val);     
        dataperkey.push_back(conscst); 
      }
      
      // after adding all uptypes, now create one entry.
      
      Constant* cCst= ConstantArray::get(SafeTidsTy, dataperkey); 
      entrylist.push_back(cCst); // now {cKey,Ccst}
       
      Constant * cEntry= ConstantStruct::get(tableEntryTy, entrylist); 
      
      rttable.push_back(cEntry);
    }
  }
  
  ArrayType* tyIdArrT=  
        ArrayType::get(tableEntryTy, totaloffsetcount); 
  
  Constant *ctbl= ConstantArray::get (tyIdArrT, rttable);
    
  rtOffsetTbl= new GlobalVariable (M, 
                              tyIdArrT, 
                              true, 
                              GlobalValue::ExternalLinkage,
                              ctbl,
                              "FRAMER_Offset_Table");

  const StructLayout * stlo= dlayout->getStructLayout(tableEntryTy);

  tblentrysize= (unsigned)stlo->getSizeInBytes(); 

  errs()<<"### type table ##########\n";
  errs()<<*rtOffsetTbl<<"\n";

}
*/

static void 
createRTOffsetTable (vector <Type*> & tlist, 
                     vector<vector<short>> & safecasts, 
                     vector <vector<pair<short, vector<short>>>> & offsets,
                     unsigned & totaloffsetcount,
                     unsigned & maxtysperoff, 
                     unsigned & maxoffsetval,
                     unsigned & maxoffsperty,
                     unsigned & tblentrysize,
                     ArrayType * SafeTidsTy,
                     StructType* oneOffsetTy,
                     ArrayType* entryT,
                     ArrayType* tableT,
                     GlobalVariable* & rtOffsetTbl, 
                     Module & M)
{
  errs()<<"createRTOffsetTable start.....\n";

  assert(offsets.size()==tlist.size());
    
  const DataLayout * dlayout= &M.getDataLayout(); 
    
/*  maxoffsetval= getMaxCount_offsets (offsets, 
                                 totaloffsetcount, 
                                 maxtysperoff,
                                 maxoffsperty);
*/
             
  //errs()<<"total offset count:\t"<<totaloffsetcount<<"\n";
  errs()<<"max tys per offset:\t"<<maxtysperoff<<"\n";
  //errs()<<"max offset val:\t"<<maxoffsetval<<"\n";
  errs()<<"max offset per ty:\t"<<maxoffsperty<<"\n";

  Type* int16T= IntegerType::getInt16Ty(M.getContext());
  Constant * defaultval= ConstantInt::get(int16T,-1);

  // * a list of tids of types at the offset can be safely casted to * 
  // * create an array of tyids * 
  // * for each offset/tid {short[maxtysperoff]} *

/*   
  ArrayType* SafeTidsTy= ArrayType::get (int16T, maxtysperoff); //1 
  
  vector<Type*> oneoffsetvec= {int16T, SafeTidsTy};
    
  StructType* oneOffsetTy= StructType::create(M.getContext(), 
                          oneoffsetvec,"offset_tys_pair"); //2

  ArrayType* entryT= ArrayType::get(oneOffsetTy, maxoffsperty); //3 
  
  ArrayType* tableT= ArrayType::get(entryT,offsets.size()); // final array! 
*/
  
  vector<Constant*> tblvec;
  
  // for each type 
  for (unsigned tid=0; tid<offsets.size(); tid++) { 
    errs()<<"\n## "<<tid<<"  "<<*tlist.at(tid)<<"\n"; 
    vector<Constant*> tyvec;

    // for each offset (pair)
    for (unsigned ofs=0; ofs < maxoffsperty; ofs++) { 
      
      vector <Constant*> pairvec;
      
      Constant * ofsval= defaultval; 
      vector<Constant*> tids (maxtysperoff, defaultval); 
        // initialise tid list with constant -1 
      
      if (ofs < (offsets.at(tid)).size()) {
         
        pair <short, vector<short>> onep= (offsets.at(tid)).at(ofs);
       
        // * offsetval 
        ofsval= ConstantInt::get(int16T, onep.first); 

        // for each safe tid
        for (unsigned cst=0; cst< (onep.second).size(); cst++) {

          short val= (onep.second).at(cst);
          tids.at(cst)= ConstantInt::get(int16T, val);
          
        }
      }
      
      Constant* consttids= ConstantArray::get(SafeTidsTy, tids); 
        // now constant tids per offset
      
      pairvec.push_back(ofsval); 
      pairvec.push_back(consttids); 
     
       
      assert(oneOffsetTy->getNumElements()==pairvec.size());
       
      Constant * temp= ConstantStruct::get(oneOffsetTy, pairvec);  
      errs()<<*temp<<"\n"; 
      tyvec.push_back(temp);  
    }
    
    tblvec.push_back(ConstantArray::get(entryT, tyvec));
  }
  
  Constant *ctbl= ConstantArray::get(tableT, tblvec);
    
  rtOffsetTbl= new GlobalVariable (M, 
                              tableT, 
                              true, 
                              GlobalValue::ExternalLinkage,
                              ctbl,
                              "FRAMER_Offset_Table");

  /* const StructLayout * stlo= dlayout->getStructLayout(oneOffsetTy);
  tblentrysize= (unsigned)stlo->getSizeInBytes(); 
  */ 
  errs()<<"createRTOffsetTable ends....\n";

}

static void
createTyOffsetList (vector<Type*> & tlist,
                    vector<vector <short>> & safecasts,
                    vector <vector<pair<short, vector<short>>>> & offsets,
                       // 1st elem: offset.
                       // 2st elem: a list of types in the offset. 
                    const DataLayout * dlayout)
{
    for (unsigned i=0;i<tlist.size();i++) {
        
        short offset= 0;
        vector <short> tids;          
        
        //ttids per offset (distance) 
        pair <short, vector<short>> tidsPerDist 
                 =make_pair(offset, tids);  
        
        vector <pair<short, vector<short>>> onety;
         
        getSubTyOffsets(tlist.at(i), tlist, tidsPerDist,
                        offset, onety, safecasts, dlayout);

        offsets.push_back(onety);
    
    }
}

static void 
createDownCastList (vector<Type*> & tlist, 
                    vector<vector<short>> & safecasts,
                    vector<vector<short>> & downcasts,
                    vector <vector<short>> & llist,
                    const DataLayout * dlayout)
{
    for (unsigned i=0;i<tlist.size();i++) { 

        vector<short> inter; 

        for(unsigned j=0; j<tlist.size(); j++) {

            // * As of cast from void*(i8*) to any ptrs, * 
            // we check separately instead of saving it, since i8* to any types
            // is downcast.
             
            //filter out equal or upcasts
            if (getIdx(safecasts.at(i),(short)j) >= 0) { 
                continue; 
            }

            if (isConversibleTo (llist.at(j), llist.at(i), 
                        tlist, llist, dlayout)) {

                inter.push_back((short)j);               
            }
        }
        downcasts.push_back(inter);
    }
}

static void
createTypeTables (vector<Type*> & tlist, 
                  vector<vector<short>> & safecasts,
                  vector<vector<short>> & downcasts,
                  vector <vector<pair<short, vector<short>>>> & tyoffsets,
                  Module & M)
{
    /* llist stores each type's fields' typeID list.
     e.g. an elem of llist: {int*, {char, char*}, float A[2]}
        == [typeID(int*), typeID(char), typeID(char*), 
            typeID(int), typeID(int)] */
    
    const DataLayout * dlayout= &M.getDataLayout(); 
    
    vector <vector<short>> llist; 
   
    // ** create flattened type layout list. NO offsets. ** 
    createLayOutList(tlist, llist);
    
    // ** Create valid upcasts **
    createSafeCastList(tlist, safecasts, llist, dlayout);
   
    // ** Create valid downcasts **
    createDownCastList (tlist, safecasts, 
                        downcasts, llist, dlayout);
    
    // create flattened type layout list WITH offsets. ** 
    // the entry is in this form: {i64 tidoffset, safedesttids[maxtids]}
    createTyOffsetList(tlist, safecasts, tyoffsets, dlayout);

    errs()<<"####################\nSafe casts\n";
    for (unsigned i=0;i<tlist.size();i++) {
        errs()<<i<<": "<<*tlist.at(i)<<"--------\n";
        for (unsigned j=0;j<(safecasts.at(i)).size();j++){
            errs()<<"  "<<(safecasts.at(i)).at(j);  
        }
        errs()<<"\n";
    }

/*
    errs()<<"####################\ndown casts\n";
    for (unsigned i=0;i<tlist.size();i++) {
        errs()<<i<<": "<<*tlist.at(i)<<"--------\n";
        for (unsigned j=0;j<(downcasts.at(i)).size();j++){
            errs()<<"  "<<(downcasts.at(i)).at(j);  
        }
        errs()<<"\n";
    }
*/    
    errs()<<"\n#### OFFSET TABLE ######\n";
    assert(tlist.size()==tyoffsets.size());

    for (unsigned i=0; i< tyoffsets.size(); i++) {
        errs()<<*tlist.at(i)<<"------------\n";

        for (unsigned j=0; j< (tyoffsets.at(i)).size(); j++) { //for each type

            pair <short, vector<short>> pi= (tyoffsets.at(i)).at(j);

            errs()<<"  "<<pi.first<<"\n";

            for (unsigned k= 0; k< (pi.second).size(); k++) {
                errs()<<"   "<<*tlist.at((pi.second).at(k))<<"\n"; 
            }
        }
    }
    errs()<<"\n#####################\n";

}

static void
setUpSomeRTTypes (ArrayType* & SafeTidsTy, 
                  StructType* & oneOffsetTy,
                  ArrayType* & entryT,
                  ArrayType* & tableT,
                  unsigned maxtysperoff,
                  unsigned maxoffsperty,
                  unsigned tyoffsetssize,
                  unsigned & tblentrysize, 
                  Module & M)
{
    assert (maxtysperoff>0 && maxoffsperty >0 
            && tyoffsetssize>0 && "values not initialised!\n");

    Type* int16T= IntegerType::getInt16Ty(M.getContext());

    SafeTidsTy= ArrayType::get (int16T, maxtysperoff); //1 

    vector<Type*> oneoffsetvec= {int16T, SafeTidsTy};

    oneOffsetTy= StructType::create(M.getContext(), 
            oneoffsetvec,"offset_tys_pair"); //2

    entryT= ArrayType::get(oneOffsetTy, maxoffsperty); //3 

    tableT= ArrayType::get(entryT,tyoffsetssize); // final array!

    const DataLayout * dlayout= &M.getDataLayout();
    const StructLayout * stlo= dlayout->getStructLayout(oneOffsetTy);
    tblentrysize= (unsigned)stlo->getSizeInBytes(); 
}

static unsigned 
getMaxCount (vector<vector<short>> & safecasts)
{
    unsigned maxcount=0;

    for(unsigned i=0; i<safecasts.size(); i++) {
        unsigned count = (safecasts.at(i)).size(); 
        if (count > maxcount) {
            maxcount = count;
        }
    }
    return maxcount; 
}

static void 
createRTSafeCastsTable (vector<vector<short>> & safecasts,
                      GlobalVariable * & SafecastTable,
                      //unsigned max_upcasts, 
                      Module & M) 
{
    unsigned max_upcasts= getMaxCount (safecasts);
    errs()<<"max field count: "<<max_upcasts<<"\n";

    ArrayType* tyIdArrayT=  
        ArrayType::get (IntegerType::getInt16Ty(M.getContext()), //elemty 
                        max_upcasts); //elem count
    
    vector<Constant*> upcastvec;
    
    for (unsigned i=0; i< safecasts.size(); i++) {  
        
        vector<Constant*> fields;
      
        for(unsigned j=0 ; j< max_upcasts ; j++) {  
            
            short framertyid= -1;
            
            if (j < (safecasts.at(i)).size()) {
                framertyid= (safecasts.at(i)).at(j);   
            }
           
            errs()<<framertyid<<"  ";
             
            Constant * fieldconst = 
                ConstantInt::get (IntegerType::get(M.getContext(), 16),      
                                  framertyid); 
            fields.push_back(fieldconst);
            assert(fields.size() <= max_upcasts && "upcast vector pushing wrong!\n");
        }
        
        errs()<<"\n"; 
        
        Constant * onestructarrayconst = ConstantArray::get(tyIdArrayT,fields);
        
        upcastvec.push_back(onestructarrayconst);
    }
    
    ArrayType* SafecastsT= ArrayType::get(tyIdArrayT, upcastvec.size());
    Constant* safecastsTableArray = ConstantArray::get(SafecastsT, upcastvec);
    
    errs()<<"Upcast TAble Array created\n";
     
    SafecastTable = new GlobalVariable (M, 
                                        SafecastsT, //StructTyArr, 
                                        true, 
                                        GlobalValue::ExternalLinkage,
                                        safecastsTableArray,//nullStructTbl,
                                        "FRAMER_Upcast_Table");
}

static bool
isCertainTy (Type * ty, StringRef tyname)
{
    if (!isa<StructType>(ty)) return false;; //if not structype

    StructType * sty= cast<StructType>(ty);

    if (!sty->hasName())  return false;

    if (!sty->getName().startswith("paddedStruct.")) return false;; 

    Type * origty= sty->getElementType(1);

    if (!isa<StructType>(origty)) return false;

    StructType * origsty= cast<StructType>(origty); 

    if (!origsty->hasName())  return false;

    if (origsty->getName().startswith(tyname)) {
        return true;
    }
    return false;
}

/*
static void 
createLocalUnionsList (Function & f,
                       vector <AllocaInst*> & ais)
{
  errs()<<"### Local Unions \n";

  for (Function::iterator fi=f.begin(); fi!=f.end();++fi) {
    
    for (BasicBlock::iterator it=(&*fi)->begin(); it!=(&*fi)->end();++it) {
      
      if (!isa<AllocaInst>(it)) continue;  
      
      AllocaInst * AI= cast<AllocaInst>(&*it);
       
      Type * ty= AI->getAllocatedType();
        
      if (isCertainTy(ty, StringRef("union."))) {
        errs()<<"  "<<*it<<"\n";
        ais.push_back(AI);   
      }
    }
  }
}
*/

static void
insertLocalUnionsList (AllocaInst * ins,
                        //GetElementPtrInst * ins,
                       //vector <GetElementPtrInst*> & LocalUnions)
                      vector <AllocaInst*> & LocalUnions)
{

    PointerType * ty= dyn_cast<PointerType>(ins->getType()); 
    assert(ty);

    if (isCertainTy(ty->getElementType(), StringRef("union."))) {
        errs()<<">> local union:   "<<*ins<<"\n";
        LocalUnions.push_back(ins);   
    }
}

static void
createGVUnionsList (Module & M,
                    vector <GlobalVariable*> & gvs)
{
  for(Module::global_iterator it= M.global_begin();
            it!=M.global_end(); it++) {

    PointerType * ty= dyn_cast<PointerType>((&*it)->getType());
    assert(ty); 
     
    Type * gvT= ty->getElementType(); 

    if (isCertainTy(gvT, StringRef("union."))) {
        
        errs()<<">> global union: "<<*gvT<<"\n";
        gvs.push_back(&*it); 
    }
  }
}

static Value *
getAlloca (Value * val)
{
  Value * op= val->stripPointerCasts();
  
  if (!isa<CallInst>(op)) return op;
  
  CallInst * ci= cast<CallInst>(op);
  
  Function * f= dyn_cast<Function>(ci->getCalledValue());

  if (!f) return op;

  StringRef fname= f->getName();
   
  if (!fname.startswith("FRAMER_"))  return op;
       
  if (fname.equals("FRAMER_forall_alloca") ||
      fname.equals("FRAMER_forall_global_variable")) {
   
    GEPOperator * gep= dyn_cast<GEPOperator>(ci->getArgOperand(0)->stripPointerCasts());
    assert(gep);
    
    return gep->getPointerOperand();
  }
  else {
    errs()<<"what case: "<<*ci<<"\n";
    exit(0);
  }
  return op;  
}

static bool
isAliasWithUnionObj(Value * op_arg, //store/load's ptrop
                    AAResults & AA,
                    vector <AllocaInst*> & ais,
                    vector <GlobalVariable*> & gvs,
                    Module & M)
{
  const DataLayout & DL = M.getDataLayout();
  
  if (ais.empty() && gvs.empty()) {
    return false;
  }
  
  //const MemoryLocation loadloc= MemoryLocation::get(li);    
  //const Value *AccessPtr = GetUnderlyingObject(loadloc, DL);
  Value * val= getAlloca(op_arg); 
  
  errs()<<"  myalloc: "<<*val<<"\n";
  
  const Value *AccessPtr = GetUnderlyingObject(val, DL);
  
  /* for union-typed allocas, check alias */
  
  for (unsigned i=0; i<ais.size(); i++) {
      
      Instruction * ins= ais.at(i);
       
      if (AccessPtr == ins || AA.isMustAlias(ins, AccessPtr)) { 
          
          return true; 
      }
  }
  /* for union-typed gvs, check alias */
  for (unsigned i=0; i<gvs.size(); i++) {
      //if (AA.alias(op_arg, gvs.at(i))) { //
      
      if (AA.isMustAlias(gvs.at(i), AccessPtr)) { 
      
          return true; 
      }
  }
  return false;

}

static GEPOperator *
getGEPFromCheckCallInst(CallInst * CI) 
{
    Value * gep= CI->getOperand(0);
    return dyn_cast<GEPOperator>(gep->stripPointerCasts());     
}

static unsigned 
isStaticInBound (unsigned offset, unsigned sizeToAccess, unsigned totalsize, bool isMemAccess)
{
    if (isMemAccess){
        //assert(offset+sizeToAccess<=totalsize && "Out-of-bound at static time\n");
        //errs()<<"FRAMER ERROR. offset+sizeToAccess > totalsize\n";
        if (offset+sizeToAccess<=totalsize) {
            return SAFESTATICALLY;     //return safe
        }
        else {
            return OUTOFBOUNDATRUNTIME;     //insert exit
        }
    }
    else {
        //assert(offset<totalsize+1); //including off-by-one byte    
        if (offset<totalsize+1) {
            return SAFESTATICALLY;
        }
        else {
            return NOTSAFESTATICALLY;
        }
    }
    return SAFESTATICALLY;
}

static unsigned 
getStaticOffset (GEPOperator * gep, const DataLayout * dlayout)
{
    // obj is gep's ptrop //
    Value * obj= gep->getPointerOperand(); 
    
    assert (isa<CompositeType>(cast<PointerType>(obj->getType())->getElementType()) 
            && "ELT not compositetype\n");
    Type * upT= cast<CompositeType>(cast<PointerType>(obj->getType())->getElementType());; 

//    uint64_t offset= 0;

/*    for (unsigned i=0;i<gep->getNumIndices();i++){
        assert(isa<ConstantInt>(gep->getOperand(i+1)) 
                && "gep idx is not constantint. do something?. getValueDom?\n");
        ConstantInt *CINT= cast<ConstantInt>(gep->getOperand(i+1));
        uint64_t idx = CINT->getZExtValue();
        if (i==0) continue;
*/        
/////////////
// i=1.
    unsigned offset=0;
    for (unsigned i=1;i<gep->getNumIndices();i++){
        ConstantInt *CINT= cast<ConstantInt>(gep->getOperand(i+1));
        uint64_t idx = CINT->getZExtValue();
/////////////
        
        if (SequentialType * SEQT=dyn_cast<SequentialType>(upT)){
            //assert (SEQT->getNumElements()<=idx && "out of bound\n"); // check overflow 
            uint64_t elemsize= (dlayout->getTypeSizeInBits(SEQT->getElementType()))/8;
            offset=offset+ (idx*elemsize);
            upT= SEQT->getElementType(); 
        }
        else if (StructType * SUBCT= dyn_cast<StructType>(upT)){
            const StructLayout * SL= dlayout->getStructLayout(SUBCT);
            offset=offset+SL->getElementOffset(idx); //update offset
            //assert (SUBCT->getNumElements()>idx && "out of bound\n"); // check overflow 
            upT= SUBCT->getElementType(idx);
        }
        else {;}
    }
    return (unsigned)offset; //delete later
}

static Value* 
isHookedAllocaOrGV (Value * p, vector<Value*> & paddedGVs) 
{
    //alloca
    GEPOperator * gep= nullptr; 
    if (isa<CallInst>(p->stripPointerCasts())) { 
        CallInst * CI= cast<CallInst>(p->stripPointerCasts());
        Value * CV= CI->getCalledValue();
        if (isa<Function>(CV)) {
            Function * F= cast<Function>(CV);
            if (F->getName().startswith("FRAMER_forall_alloca")) { //for alloca
                Value * myalloc= dyn_cast<GEPOperator>(CI->getOperand(0)->stripPointerCasts()); 
                assert(myalloc!=nullptr && "alloca op 0 is null\n");  
                return myalloc; 
            }
            else {;}
        }
    }
    // GV
    else if (UnaryConstantExpr * itp= dyn_cast<UnaryConstantExpr>(p)){
        // paddedGV's elems are intptr's operand(0), 
        //   becuz as of cast inttoptr, the cast instructions are merged. 
        
        vector<Value*>::iterator it; //TODO: add paddedGV in doGV. (check bitcast. strip or not) 
        it= find (paddedGVs.begin(), paddedGVs.end(), itp->getOperand(0)); //p or ptr?
        if(it != paddedGVs.end()) {
            return itp;
        }
    }
    return nullptr;
}


static CallInst * 
getGVHookCall (GlobalVariable * gv)
{
    for(Value::user_iterator bit= gv->user_begin();bit!=gv->user_end();++bit) {
        if (isa<BitCastInst>(*bit)) {
            for (Value::user_iterator it=(*bit)->user_begin();it!=(*bit)->user_end();++it) {
                if (!isa<CallInst>(*it)) continue; 
                
                CallInst * ci= cast<CallInst>(*it); 
                Function * hook = ci->getCalledFunction();
                
                if (hook==nullptr) continue;

                if (hook->getName().equals("FRAMER_forall_global_variable")) {
                    return ci;
                }
            }
        }
        else if (isa<CallInst>(*bit)) {
            CallInst * ci= cast<CallInst>(*bit); 
            Function * hook= ci->getCalledFunction(); 
            if (hook==nullptr) continue;

            if (hook->getName().equals("FRAMER_forall_global_variable")) {
                return ci;
            }
        }
    }
    return nullptr;
}

static CallInst * 
__isAllocation (Value * p, Module & M, 
                GEPOperator * gep)
{
    //alloca
    if (isa<CallInst>(p->stripPointerCasts())) { 
        CallInst * CI= cast<CallInst>(p->stripPointerCasts());
        Value * CV= CI->getCalledValue();
        if (isa<Function>(CV)) {
            Function * F= cast<Function>(CV);
            if (F->getName().startswith("FRAMER_forall_alloca")) { //for alloca
                return CI; 
            }
            else if (F->getName().startswith("malloc")) {
                return CI;
            }
        }
    }
    else if (isa<LoadInst>(p->stripPointerCasts())){
        
        Value * liOp= (cast<LoadInst>(p->stripPointerCasts()))->getOperand(0);
        
        if (!isa<GlobalVariable>(liOp->stripPointerCasts())) return nullptr; 
        
        GlobalVariable * gv= cast<GlobalVariable>(liOp->stripPointerCasts());

        return getGVHookCall(gv); //gv may not be involved with global arrays. 
    }

    // GV --> now tagged ptr to global arrays are replaceds with framer's gv's load.
    else if (UnaryConstantExpr * itp= dyn_cast<UnaryConstantExpr>(p)){
        //1. iterate on gvhook (main's 1st or 2nd bb)
        //2. get hook ci's operand ()
        // if op== itp, then return ..what.
        //return itp;
        Function * mf= M.getFunction("main");
        assert(mf!=nullptr);
        
        int BBidx= 0;
        for (Function::iterator IT= mf->begin();IT!=mf->end();++IT) {
            if (BBidx>2) break;  //GV hooks are inserted in the 1st or 2nd BB of main
            for (BasicBlock::iterator it= (&*IT)->begin();it!=(&*IT)->end();++it) {
                if (!isa<CallInst>(&*it)) continue; 
                  
                CallInst * ci= cast<CallInst>(&*it);
                Function * hook= ci->getCalledFunction();
                if (hook==nullptr) continue;
                if (!hook->getName().equals("FRAMER_forall_global_variable")) continue;
                 
                //now we got gv hook.
                
                if (itp==ci->getOperand(0)->stripPointerCasts()) {
                    return ci;  
                }
            }
            BBidx++;    
        }
    }
        return nullptr;
}

static Instruction * 
getNextInst (Instruction * Inst)
{
    BasicBlock::iterator I (Inst);
    I++;
    if (I == Inst->getParent()->end()) {
        return nullptr;
    }
    return &*I;
}

static GlobalVariable *
getNextGV (GlobalVariable * gv)
{
    Module::global_iterator I (gv);
    I++;
    if (I == gv->getParent()->global_end()) {
        return nullptr;
    }
    return &*I;
}


static unsigned 
FramerGetBitwidth (Type * allocatedType, const DataLayout * dlayout)
/* #Bits of element type. (e.g. int->32, struct->sum of member bits, 
    array->#bits of array element. (outmost element, if the array is array of array...)*/
{
    unsigned allocatedTyID = allocatedType->getTypeID();
     
    if (( allocatedTyID > Type::VoidTyID && allocatedTyID < Type::PPC_FP128TyID) ){
        return getPrimTyBits (allocatedTyID); //TODO. maybe we can use llvm's func ?
    }
    else if (IntegerType * intTy = dyn_cast<IntegerType>(allocatedType)) {
        return intTy->getBitWidth();
    }
    else if (isa<CompositeType>(allocatedType)) {
        if (isa<PointerType>(allocatedType)) {
            return dlayout->getPointerSizeInBits(); //8 bytes..
        }
        else if (StructType * structTy = dyn_cast<StructType>(allocatedType)) {
            return (unsigned) getBitwidthOfStruct (structTy, dlayout);
        }
        else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
/*            if (isOutMost) {
                return FramerGetBitwidth(arrayTy->getElementType(), dlayout, false);
            }
            else {
                return (unsigned)(arrayTy->getNumElements())*FramerGetBitwidth(arrayTy->getElementType(), dlayout, false); 
            } */
            return (unsigned)(arrayTy->getNumElements())*FramerGetBitwidth(arrayTy->getElementType(), dlayout); 
        }
        else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {
            if (vecty->getBitWidth()!=0) {
                return vecty->getBitWidth();
            }
            else {
                return (unsigned)(vecty->getNumElements())*FramerGetBitwidth(vecty->getElementType(), dlayout); 
            }
        }
        else {
            errs()<<"1. what type is this??\n";
            exit(0);
        }
    }
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else {
        errs()<<"2. What type is this?!\n";
        exit(0);
    }
}
/*
static unsigned 
getTotalSize(GEPOperator * gep, const DataLayout * dlayout)
{
    Type * upT= cast<PointerType>(gep->getPointerOperand()->stripPointerCasts()->getType())->getElementType(); 
    if (SequentialType * SEQT=dyn_cast<SequentialType>(upT)){
        if (StructType * ST= dyn_cast<StructType>(SEQT->getElementType())){
            const StructLayout * SL= dlayout->getStructLayout(ST);
            return SL->getSizeInBytes()*SEQT->getNumElements();
        }
        else {
            return SEQT->getNumElements()*(dlayout->getTypeSizeInBits(SEQT)/8);
        }
    }
    else if (StructType * SUBCT= dyn_cast<StructType>(upT)){
        const StructLayout * SL= dlayout->getStructLayout(SUBCT);
        return SL->getSizeInBytes();  
    }
    else if (IntegerType * INTT= dyn_cast<IntegerType>(upT)){
        return INTT->getBitWidth()/8;   
    }
    else {
        errs()<<"what the heck.\n";
        exit(0);
    }
}   
*/

static unsigned getmysize (CallInst * ci)
{
    ConstantInt * numelem= nullptr;
    ConstantInt * elemsize= nullptr;
    
    Function * F= ci->getCalledFunction();
    assert(F!=nullptr && "called function null\n"); 
    
    if (F->getName().equals("FRAMER_forall_alloca")) {
        numelem= dyn_cast<ConstantInt>(ci->getOperand(1)); 
        elemsize= dyn_cast<ConstantInt>(ci->getOperand(3)); 
    }
    else if (F->getName().equals("FRAMER_forall_global_variable")){
        numelem= dyn_cast<ConstantInt>(ci->getOperand(2)); 
        elemsize= dyn_cast<ConstantInt>(ci->getOperand(3)); 
    }
    
    assert((numelem && elemsize) && "numelem or elemsize null\n"); 
    return (unsigned)(numelem->getZExtValue()*elemsize->getZExtValue());   
}

static unsigned 
handleMallocStaticBounds(GEPOperator * gep, CallInst * ci, bool isMemAccess, Module & M)
{
    //ci is call malloc
    if (gep->getNumIndices()!=1) {
        return NOTSAFESTATICALLY; 
    }
    // now idx_num==1
    Value * idxval= gep->getOperand(1); 
    Value * mallocarg= ci->getOperand(0); 
    
    if (isa<ConstantInt>(mallocarg)) {
        unsigned elemsize= FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), &M.getDataLayout())/8;
        if (isa<ConstantInt>(idxval)){ //the only idx
            //both constint
            uint64_t mallocsize= cast<ConstantInt>(mallocarg)->getZExtValue();
            uint64_t idx= cast<ConstantInt>(idxval)->getZExtValue();
             
            if(isMemAccess){
                if (mallocsize>=(idx+1)*elemsize) {
                    //errs()<<"SAFE SL: "<<*gep<<" ( "<<*mallocarg<<" )\n";
                    return SAFESTATICALLY; 
                }
                else {
                    //errs()<<"OUT SL: "<<*gep<<" ( "<<*mallocarg<<" )\n";
                    return OUTOFBOUNDATRUNTIME; 
                }
            }
            else {
                if (mallocsize+1>=(idx+1)*elemsize) {
                    //errs()<<"SAFE GEP: "<<*gep<<" ( "<<*mallocarg<<" )\n";
                    return SAFESTATICALLY;     
                }
                else {
                    //errs()<<"Hook GEP: "<<*gep<<" ( "<<*mallocarg<<" )\n";
                    return NOTSAFESTATICALLY; 
                }
            }
        }
        else { //malloc arg is const int, idx is not.
            //errs()<<"malloc: "<<*ci<<"\n";
            //errs()<<"Compare: "<<*gep<<" ("<<*mallocarg<<")\n";
            return COMPSIZEATRUNTIME;
        }
    }
    else { //malloc arg is not const int
        //errs()<<"ci: "<<*ci<<"\n";  
        //errs()<<"Compare: "<<*gep<<" ( "<<*mallocarg<<" )\n";
        return COMPSIZEATRUNTIME; 
    }
}
static void
cleanupCasts(Function & F)
{
  vector <Instruction*> removes;
  
  for(Function::iterator fi= F.begin();fi!=F.end();++fi) {
    for(BasicBlock::iterator it= (&*fi)->begin();it!=(&*fi)->end();++it){
      if (isa<CastInst>(it) && it->getNumUses()==0) {
          //errs()<<"USE 0: "<<*it<<"\n";
          removes.push_back(&*it);
      }
      else if (isa<GetElementPtrInst>(it) && it->getNumUses()==0) {
          removes.push_back(&*it);
      }
    }
  }
  for (vector<Instruction*>::iterator it=removes.begin();
          it!=removes.end();++it) {
      (*it)->eraseFromParent(); 
  }
}

static void
pullHookInLifetime (CallInst * ci, CallInst * start,
                    vector<Instruction*> & toBeRemoved)
{
    // ci is alloca hook, start is it's llvm.lifetime.start
 
 //   errs()<<"\nlifetime BB: \n"<<*start->getParent()<<"\n";
 
   //get ci->getUser()
    Instruction * usr= nullptr;
    Instruction * usrdup=nullptr; 
    for(Value::user_iterator it=ci->user_begin();
            it!=ci->user_end();++it) {
        
        if (!isa<Instruction>(*it)) continue;
        
        usr= cast<Instruction>(*it); 
        
        if (usr->getParent()== &usr->getFunction()->getEntryBlock()) {
            assert(isa<CastInst>(usr)); //some other cases than bitcast? 
            //errs()<<"alloc hook's user in Entry block: "<<*usr<<"(clone,insert,del)\n";   
            usrdup= usr->clone();
            usrdup->insertAfter(start);
            usr->replaceAllUsesWith(usrdup); 
        }
    }


  
  if (BitCastInst * bins= dyn_cast<BitCastInst>(ci->getOperand(0))) {
    //errs()<<"bins op: "<<*bins->getOperand(0)<<"\n";
     
    GetElementPtrInst * gep= 
        dyn_cast<GetElementPtrInst>(bins->getOperand(0));
    
    assert(isa<AllocaInst>(gep->getPointerOperand()));

    AllocaInst * paddedai= cast<AllocaInst>(gep->getPointerOperand());
  
         
    //errs()<<"AI: "<<*paddedai<<"\n";
    //errs()<<"AI ty: "<<*paddedai->getType()<<"\n";
    Instruction * binsdup= bins->clone();
    Instruction * gepdup= gep->clone();
    Instruction * cidup= ci->clone();


 
    //keep the order of insertion!
    cidup->insertAfter(start);
    binsdup->insertAfter(start);   
    gepdup->insertAfter(start);   

    CallInst * untagci= dyn_cast<CallInst>(start->getOperand(1));
    assert(untagci); 
    Function * untagf=untagci->getCalledFunction(); //TODO 
    assert(untagf->getName().equals("FRAMER_supplementary_untag_ptr")); 
    //errs()<<"untagci's op: "<<*untagci->getOperand(0)<<"\n";;
    if (isa<GetElementPtrInst>(untagci->getOperand(0))) {
        GetElementPtrInst * special= cast<GetElementPtrInst>(untagci->getOperand(0));
        special->setOperand(0,paddedai);
        //errs()<<"special: "<<*special<<"\n";
        start->setOperand(1,special);
        errs()<<"start: "<<*start<<"\n";
        exit(0);
    }
    else if (paddedai->getType()!=start->getOperand(1)->getType()) {
        BitCastInst * bciarg= new BitCastInst(paddedai, start->getOperand(1)->getType(),"",start); 
        start->setOperand(1,bciarg);    
    }
    else {
       start->setOperand(1, paddedai); 
    }
    //errs()<<"start setup.start's 1st op: "<<*start->getOperand(1)->stripPointerCasts()<<"\n";
    //errs()<<"DEL untag: "<<*untagci<<"\n"; 
    //untagci->eraseFromParent();
    toBeRemoved.push_back(untagci);

    
    //if (usr) usr->replaceAllUsesWith(usrdup); 
    ci->replaceAllUsesWith(cidup);
    bins->replaceAllUsesWith(binsdup);
    gep->replaceAllUsesWith(gepdup);
  
  
    // setup arg of life.start.
    //errs()<<"DEL: "<<*ci<<"\n";
    //errs()<<"DEL: "<<*bins<<"\n";
    //errs()<<"DEL: "<<*gep<<"\n";

    //ci->eraseFromParent();
    //bins->eraseFromParent();
    //gep->eraseFromParent();
    if (usr) toBeRemoved.push_back(usr);
    toBeRemoved.push_back(ci);
    toBeRemoved.push_back(bins);
    toBeRemoved.push_back(gep);
    //errs()<<"cidup: "<<*cidup<<"\n";
    //errs()<<"usrdup: "<<*usrdup<<"\n";
  }
    else {
        errs()<<"FRAMER: not bitcast. do something. probably this is GEP\n";
        errs()<<*ci->getOperand(0)<<"\n";
        exit(0);
    }
}

// find a llvm.lifetime.start, get a alloca hook.
// then move alloca hook and its operand instructions AFTER start func. 
static void
setupScopeOfLocals(Function & F, Module & M)
{
  vector<Instruction*> toBeRemoved;
/*  if (!F.getName().equals("BZ2_blockSort")){ 
//    errs()<<"\n>>>>>> F: "<<F.getName()<<" <<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<<\n";
    return; 
  }
*/
//  errs()<<"\n-- entry block-- \n"<<F.getEntryBlock()<<"\n"; 
  
  for(Function::iterator fi= F.begin();fi!=F.end();++fi) {
    for(BasicBlock::iterator it= (&*fi)->begin();it!=(&*fi)->end();++it){
       
      if (!isa<CallInst>(it)) continue;
      CallInst * ci= cast<CallInst>(&*it);
      
      Function * func= ci->getCalledFunction();   
      if (func==nullptr) continue; 
        
      if (!func->getName().equals("llvm.lifetime.start")) continue;
        //errs()<<"\n>> lifetime.start: "<<*ci<<"\n"; 
      
            
      Instruction* ins= dyn_cast<Instruction>(ci->getOperand(1));
      assert(ins && "op is not an instruction!\n");
        //errs()<<"ins: "<<*ins<<"\n"; 
        //errs()<<"stripped: "<<*ins->stripPointerCasts()<<"\n"; 
      
      Instruction * raw= dyn_cast<Instruction>(ins->stripPointerCasts());  
      assert(raw);
       
      if (AllocaInst * ai=dyn_cast<AllocaInst>(raw)) {
          // skip non-array allocas.
          //assert(!isa<ArrayType>(ai->getAllocatedType()));
          continue;     
      }
      else if (CallInst * untagci= dyn_cast<CallInst>(raw)) {
        Function * untagf= untagci->getCalledFunction();
        assert(untagf);
        assert(untagf->getName().equals("FRAMER_supplementary_untag_ptr"));
       
        if (isa<GetElementPtrInst>(untagci->getOperand(0))) {
            //errs()<<"skip::: "<<*untagci->getOperand(0)<<"\n";
            continue;
        }
        Value * op= (untagci->getOperand(0))->stripPointerCasts();
        
        //errs()<<"got hook? :"<<*op<<"\n";
        
        CallInst * allocacall= dyn_cast<CallInst>(op);
        
        assert(allocacall);
        
        Function * allocahook= allocacall->getCalledFunction();
        
        assert(allocahook);
        assert(allocahook->getName().equals("FRAMER_forall_alloca"));

        pullHookInLifetime(allocacall, ci, toBeRemoved); 
      }
      else {
          errs()<<"do something for lifetime\n";
          exit(0); 
      }
    }
  }
  //errs()<<" now deleting..\n";
  for(vector<Instruction*>::iterator it=toBeRemoved.begin();
        it!=toBeRemoved.end();++it) {
    //errs()<<"del: "<<**it<<"\n";
    (*it)->eraseFromParent();    
  }
  //errs()<<" now cleanup..\n";
  cleanupCasts(F);
}

static Instruction * 
scopeIsFunc (Instruction * padded)
{
    //errs()<<"padded: "<<*padded<<"\n";
    for (Value::user_iterator it=padded->user_begin();it!=padded->user_end();++it){
        if(CallInst * ci=dyn_cast<CallInst>(*it)) {
            Function * f= ci->getCalledFunction();
            if (f==nullptr) continue;
            if (f->getName().startswith("llvm.lifetime.end")) {
               //errs()<<"got ci: "<<*ci<<"\n";
               return ci; 
            }
        }
        else if (BitCastInst * bi=dyn_cast<BitCastInst>(*it)) {
            for (Value::user_iterator iit=bi->user_begin();
                    iit!=bi->user_end();++iit){
                if (BitCastInst * bi=dyn_cast<BitCastInst>(*iit)) {
                    for (Value::user_iterator ii=bi->user_begin();
                            ii!=bi->user_end();++ii){
                        if(CallInst * ci=dyn_cast<CallInst>(*ii)) {
                            Function * f= ci->getCalledFunction();
                            if (f==nullptr) continue;
                            if (f->getName().startswith("llvm.lifetime.end")) {
                                //errs()<<"got ci: "<<*ci<<"\n";
                                return ci; 
                            }
                        }
                    }
                }
            }
        }
    }
    return nullptr;
}

static unsigned 
__isSafeAccess (GEPOperator * gep, Module & M, 
                bool isMemAccess)
{
        CallInst * ci= __isAllocation(gep->getPointerOperand(), M, gep); 
        //ci is hook_alloca,hook_gv, or malloc call
        if (ci==nullptr) {
            return NOTSAFESTATICALLY; 
        }
        if (gep->hasAllZeroIndices()) { // base addr of alloca/gv
            return SAFESTATICALLY; 
        }
    // ***** malloc s ***   
        if (ci->getCalledFunction()->getName().equals("malloc")) {
            return handleMallocStaticBounds(gep, ci, isMemAccess, M); 
        }
    // ***** malloc e ***

        if (!isa<ConstantInt>(gep->getOperand(1)->stripPointerCasts())){
            return NOTSAFESTATICALLY; // issafeaccess==0. 
        }
        if (!((cast<ConstantInt>(gep->getOperand(1)->stripPointerCasts()))->equalsInt(0))) {
            return NOTSAFESTATICALLY; 
        }
        if (!gep->hasAllConstantIndices()) {
            if (gep->getNumIndices()<=2) {
                return COMPAREIDXATRUNTIME; // issafeaccess==2. requiring runtime check 
            } 
            else {
                return NOTSAFESTATICALLY;
            } 
        }
        // offset= base~ptr (two args. 2nd is gep's ptr.assignment)
        unsigned offset= getStaticOffset(gep, &M.getDataLayout()); 
        unsigned totalsize= getmysize(ci);
        unsigned sizeToAccess= FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), &M.getDataLayout())/8;
        
        return isStaticInBound(offset, 
                        sizeToAccess,
                        totalsize,
                        isMemAccess); 
}

static Value * 
ismalloc (Value * p) 
{
// p, possibly casted
// returns sizeOfObj of malloc or nullptr 
    if (isa<CallInst>(p->stripPointerCasts())) {
        CallInst * ci= cast<CallInst>(p->stripPointerCasts());
        Function * F= ci->getCalledFunction();
        if (F==nullptr) return nullptr; 
         
        if (F->getName().equals("malloc")) {
            return ci->getOperand(0); 
        }
    }
    return nullptr;            
}

// toUntag (-1), do nothing (0), tobechecked (1) 
// op_'s type is always pointer type.
//op: load/store's ptr op
static unsigned 
isSafeAccess (Value * op_, Module & M, bool isMemAccess, 
              vector <Value*> & paddedGVs) 
{
    Value * op=op_->stripPointerCasts();
    
    if (isHookedAllocaOrGV(op, paddedGVs)) {
        return SAFESTATICALLY;
    }
    Value * mallocop= ismalloc(op_);
    if (mallocop!=nullptr) {
        
        return SAFESTATICALLY;
    }
    if (GEPOperator * gep=dyn_cast<GEPOperator>(op)) {  
        dbg("skip. safe gep\n";)
        return __isSafeAccess(gep, M, isMemAccess); 
    }
    else {

/// commented since I am doubtful if this will /////////
/// make a big difference for performance.      /////////
/// can try later                               /////////
//        if (checkSafeWithDomTree(op, dt)) { 
//            errs()<<"Read todo\n"; //TODO. bring case splitting (if load stuff) to here.
//            return true;
//        }
    } 
    return 0;
}


static ConstantAggregate* 
getNewConstAggr (int opnum, Constant * CA, Constant * newGV) 
{
    assert(isa<ConstantAggregate>(CA) && "CA not ConstantAggregate\n");
   
    /// create array with GV replaced with newGV. 
    vector <Constant*> elems;
    for (User::op_iterator it=CA->op_begin(),ie=CA->op_end();it!=ie;++it){
        elems.push_back(cast<Constant>(&*it->get())); 
    } // fill elems from CA. and then replace opnum's elem.
    elems.at(opnum)= newGV;
    
    Constant * replica=nullptr;
    
    if (ConstantStruct * CStrt=dyn_cast<ConstantStruct>(CA)) {
       replica= ConstantStruct::get(CStrt->getType(),elems); 
    }
    else if(ConstantArray * CArr=dyn_cast<ConstantArray>(CA)){
        replica= ConstantArray::get(CArr->getType(), elems); 
    }
    else if (isa<ConstantVector>(CA)){
        replica=ConstantVector::get(elems);
    }
    else {
        errs()<<"FRAMER:: What case is this? getNewConstAggr\n";
        exit(0); 
    }
    return cast<ConstantAggregate>(replica);
}


static Constant* 
getNewConstExpr (Constant * consUse, Constant* newGV, 
            GlobalVariable* origGV, vector <Constant*>& oplist)
{      // use: bitcast (oldgv to ty) 
    if (oplist.empty()) {
        return (cast<Constant>(consUse)); 
    }
    Constant* CU= cast<Constant>(consUse); 
    Constant* replica= CU; 
    int opnum=0;
    
    for (User::op_iterator it= CU->op_begin(), ie=CU->op_end(); it!=ie; ++it) { 
        //iterating numOperands of the operator
         
        if ((&*it)->get()==origGV) {
            if (isa<ConstantExpr>(CU)) {
                replica= cast<ConstantExpr>(replica)->getWithOperandReplaced(opnum, newGV); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                replica= getNewConstAggr(opnum, replica, newGV); 
            }
        }
        else if (isa<ConstantExpr>(&*it)||isa<ConstantAggregate>(&*it)) { 
            Constant * itex= cast<Constant>(&*it);
            oplist.push_back(itex);
           
            Constant * constuse= dyn_cast<Constant>(&*it);
            assert(constuse!=nullptr); 
            //Constant * temp= getNewConstExpr(&*it,newGV,origGV,oplist);
            Constant * temp= getNewConstExpr(constuse,newGV,origGV,oplist);

            if (temp == itex) {
                opnum++;
                continue;
            }
            if (isa<ConstantExpr>(CU)) {
                replica= (cast<ConstantExpr>(replica))->getWithOperandReplaced(opnum,temp); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                replica= getNewConstAggr(opnum, replica, temp);
            }
        }
        else if (User * UU=dyn_cast<User>(&*it)) { // having leaves  
            if (UU->getNumOperands()>=2) {
            errs()<<">> what case is this? CU:: "<<*CU<<"\n";
                exit(0);
            }
        }
        opnum++;
    }
    assert(opnum==CU->getNumOperands() && "CU!=getnumops!!\n"); 
    oplist.pop_back();   
    return replica; 
}



static Constant * 
getReplacement (Constant * consUse, Constant* newGV, 
                GlobalVariable * origGV)
{ //use's form constexpr(orig_gv) or orig_gv. definitely having origGV inside.

    if (consUse==origGV) {
        assert(isa<GlobalVariable>(consUse) && "Use is not GV!\n");
        return newGV; 
    }
   
    assert(!isa<GlobalVariable>(consUse) 
    && "FRAMER ERROR.for this case, it should have been returned.\n");
    
    if (isa<ConstantExpr>(consUse)||isa<ConstantAggregate>(consUse)) {
        vector <Constant*> oplist;
        oplist.push_back(cast<Constant>(consUse)); 
        return getNewConstExpr(consUse, newGV, origGV, oplist); 
    }
    else { 
        errs()<<"Use is Neither GV nor CE. USE: "<<*consUse<<"\n"; 
        exit(0);    
    }
}

static unsigned 
getopidx (User *user, Use * op)
{
    User::op_iterator it (op);
    assert(it!=user->op_end() && "value not found in op_list\n");
    return it - user->op_begin();
}


static Value* 
getNewInsForGV (Constant * constuse, //Use * use, 
                Constant* newGV, 
                GlobalVariable* origGV, vector <Constant*>& oplist,
                Instruction * init, 
                vector<Instruction*> & insToBeInserted,
                set<Instruction*> & FramerLoads)
{      // use: bitcast (oldgv to ty) 
    if (oplist.empty()) {
        //return (cast<Constant>(&*use)); 
        return constuse; 
    }
    
    ConstantExpr* CU= dyn_cast<ConstantExpr>(constuse); 
    assert(CU!=nullptr);

    Instruction* replicaIns= CU->getAsInstruction(); 
    
    int opnum=0;
    for (User::op_iterator it= CU->op_begin(), ie=CU->op_end(); it!=ie; ++it) { 
        //iterating numOperands of the operator
         
        if ((&*it)->get()==origGV) {
            if (isa<ConstantExpr>(CU)) {
               // TODO: if it's gep and safe access, replace with orig GV. 
               // replica= cast<ConstantExpr>(replica)->getWithOperandReplaced(opnum, newGV); 
                replicaIns->setOperand(opnum, init); //do check
                 
            }
            else if (isa<ConstantAggregate>(CU)) {
                replicaIns->setOperand(opnum, getNewConstAggr(opnum, CU, newGV)); 
                errs()<<"what case is this? \n";
                errs()<<"Const user is CAgg: "<<*CU<<"\n";
                errs()<<"replica: "<<*replicaIns<<"\n";
                exit(0);
            }
        }
        else if (isa<ConstantExpr>(&*it)||isa<ConstantAggregate>(&*it)) { 
            Constant * itex= cast<Constant>(&*it);
            oplist.push_back(itex);
            Value * temp= getNewInsForGV(itex,newGV,origGV,
                            oplist, init, insToBeInserted, FramerLoads);

            if (temp == itex) {
                opnum++;
                continue;
            }
            if (isa<ConstantExpr>(CU)) {
                replicaIns->setOperand(opnum,temp); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                if (isa<Constant>(temp)) {
                    replicaIns->setOperand(opnum, getNewConstAggr(opnum, CU, cast<Constant>(temp)));
                }
                else {
                    errs()<<"do something. grr\n";
                    exit(0);  
                }
            }
        }
        else if (User * UU=dyn_cast<User>(&*it)) { // having leaves  
            if (UU->getNumOperands()>=2) {
            errs()<<">> what case is this? CU:: "<<*CU<<"\n";
                exit(0);
            }
        }
        opnum++;
    }
    assert(opnum==CU->getNumOperands() && "CU!=getnumops!!\n"); 
    oplist.pop_back();
    insToBeInserted.push_back(replicaIns);   
    FramerLoads.insert(replicaIns);
    return replicaIns; 
}


static Value * 
getInstReplacement(Constant * constuse, //Use* use, 
                   Constant* newGV, 
                   GlobalVariable * origGV, 
                   Instruction * init,
                   vector<Instruction*> & insToBeInserted,
                   set <Instruction*> & FramerLoads)
{
    
    //if (&*use->get()==origGV) {
    if (constuse==origGV) {
        //assert(isa<GlobalVariable>(&*use) && "Use is not GV!\n");
        assert(isa<GlobalVariable>(constuse) && "Use is not GV!\n");
        return init;
        //return newGV; //DO SOMETHING. 
    }
    //if (isa<ConstantExpr>(&*use)||isa<ConstantAggregate>(&*use)) {
    if (isa<ConstantExpr>(constuse)||isa<ConstantAggregate>(constuse)) {
         
        vector <Constant*> oplist;
        //oplist.push_back(cast<Constant>(&*use)); 
        oplist.push_back(cast<Constant>(constuse)); 
        //return getNewInsForGV(use, newGV, origGV, //test1 
        return getNewInsForGV(constuse, newGV, origGV, //test1 
                        oplist, init, insToBeInserted, FramerLoads); 
      // use: bitcast (oldgv to ty) 
    }
    else { 
        errs()<<"Use is Neither GV nor CE. USE: "<<*constuse<<"\n"; 
        exit(0);    
    }

}

static void 
insertNewIns (vector<Instruction*> & insVec,
              Instruction * iuser)
{
    //push_back, and insert before iuser
    for(Instruction * ins : insVec) {
        ins->insertBefore(iuser);
    }
}



static void
updatepaddedGV (GlobalVariable * origGV,
                Constant* untagged,
                set<tuple<GlobalVariable*, 
                Constant*,Constant*>> & inits)
                //set<pair<GlobalVariable*, Constant*>> & inits)
{
    set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator it;
    for(it=inits.begin();it!=inits.end();++it) {
        if (get<0>(*it)==origGV) { 
            //errs()<<">> Update padded GV. origGV: "<<*origGV<<"\n";
            //errs()<<" paddedGV: "<<*untagged<<"\n";
            break;
        }
    }
    //assert(it!=inits.end());
    
    if (it!=inits.end()) {
        inits.insert(tuple<GlobalVariable*,Constant*,Constant*>(origGV,get<1>(*it),untagged));     
        inits.erase(*it);
    }
    else {
        inits.insert(tuple<GlobalVariable*,Constant*,Constant*>(origGV,origGV->getInitializer(),untagged));     
    }
}

static void
setupGVInitializer (set<tuple<GlobalVariable*, Constant*, Constant*>> & inits,
                    Instruction * lastins)
{
    for(set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator git=inits.begin();
            git!=inits.end();++git) {
        
        GlobalVariable * gv=get<0>(*git);
        if (gv->getInitializer()==get<1>(*git)) continue; 
        
        //errs()<<">>>> STORE GV: "<<gv->getName()<<"\n";
        if (gv->isConstant()) {
        //    errs()<<"  -->> Constant Global. skipping\n";
            continue;
        }
        Constant * newgv= get<2>(*git); // newly created GV array with NO tag
        if (newgv==nullptr) {
            newgv= get<0>(*git);    
        }
        Constant * init= get<1>(*git);
        
        StoreInst * si= new StoreInst(init,newgv,lastins);
        //errs()<<"new si: "<<*si<<"\n";
    }
}
/* return saved constexpr wiht tagged pointer.
    if not existing in the set, return gvu's initializer  */
//static Constant *
static set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator
getInit (set<tuple<GlobalVariable*, Constant*, Constant*>> & inits,
         GlobalVariable * GVU)
{
    set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator it; 
    for(it=inits.begin(); it!=inits.end(); ++it) {
        GlobalVariable * gv= get<0>(*it);
        if (gv->getName().equals(GVU->getName())) {
            break;
        }
    }
    if (it!=inits.end()) { // exists in the set
        //errs()<<" --> in the set.\nGVU: "<<*GVU<<"\n"; 
        return it;
    }
    else {  // not exist in the set
        inits.insert(tuple<GlobalVariable*, Constant*, Constant*>(GVU, GVU->getInitializer(), nullptr));
        for(it=inits.begin(); it!=inits.end(); ++it) {
            GlobalVariable * gv= get<0>(*it);
            if (gv->getName().equals(GVU->getName())) {
                return it; 
            }
        }
    }
    //return GVU->getInitializer(); 
    
    // if exists in inits, return GVU's initializer, 
    // and remove the member from set.
    // otherwise return use. 
}

static void
updateTaggedPtr (set<tuple<GlobalVariable*, Constant*, Constant*>> & inits,
                GlobalVariable * gvu, Constant * replica)
{
    set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator it;
    
    for(it=inits.begin(); it!=inits.end(); ++it) {
        GlobalVariable * gv= get<0>(*it);
        if (gv->getName().equals(gvu->getName())) {
            break;
        }
    }
    assert(it!=inits.end());
    
    inits.insert(tuple<GlobalVariable*,Constant*,Constant*>(gvu,replica,get<2>(*it)));
    //errs()<<" temp init: "<<*gvu->getInitializer()<<"\n";
    //errs()<<" init: "<<*replica<<"\n";
    inits.erase(*it);
}

static void 
handleUsesOfGV (Use* use, Constant* tagged, 
            Constant* untagged, GlobalVariable * origGV,
            GlobalVariable * gvTag, 
            set <Instruction*> & FramerLoads,
            set<tuple<GlobalVariable*, Constant*, Constant*>> & inits)
            //set<pair<GlobalVariable*, Constant*>> & inits)
{
    User * user= use->getUser();
    
    Constant * constuse= dyn_cast<Constant>(use->get());
    assert(constuse!=nullptr); 

    if(GlobalVariable * GVU= dyn_cast<GlobalVariable>(user)) {  
        /// get constexpr whose elem will be modified from inits. 
      
        /// (1) get a saved constexpr from the set, inits. 
        //Constant * initexpr= getInit(inits, GVU);   
        //errs()<<"\norigGV: "<<*origGV<<"\n";
        set<tuple<GlobalVariable*,Constant*,Constant*>>::iterator myelem= getInit(inits,GVU);

        Constant * initexpr= get<1>(*myelem);
        //errs()<<" initexpr: "<<*initexpr<<"\n";
        /// (2) get replacements for both temporary untagged and tagged initializers. 
        Constant* replica= getReplacement(initexpr, tagged, origGV);
        Constant* replica_temp= getReplacement(constuse, untagged, origGV); 
        
        // ** replacing with untagged, since some forms of our tagged pointer 
        // not allowed as an GV initializer.
        assert(constuse->getType()==replica->getType()); 
        GVU->setInitializer(replica_temp); //--> set the initializer with untagged ptr to new GV 
        
        // (3) setup an initializer with a created padded global arrays (untagged) 
        // (4) insert the initializer in a constexpr for tagged ptr.
        updateTaggedPtr(inits, GVU, replica); 
    
    }
    else if(Instruction * IU= dyn_cast<Instruction>(user)) { 
        assert(!isHookFamilyFunction(IU->getFunction()) && IU->getParent()); 
        
        if (isa<PHINode>(IU)) { //got weird error for phi node..so I separated this.
            Constant* replica= getReplacement(constuse,tagged, origGV);
         //   Constant* replica= getReplacement(use,untagged, origGV);
            unsigned myidx= getopidx(IU, use);
            assert(replica->getType()==IU->getOperand(myidx)->getType());
            IU->setOperand(myidx, replica); //do something.
        }
        else {
            LoadInst * li= new LoadInst(gvTag, "loadGVTag", IU);
           // TRY: insert li in the beginning of the function 
          //  Instruction * fstins= &*((IU->getFunction())->begin()->begin());
          //  LoadInst * li= new LoadInst(gvTag, "loadGVTag", fstins);
            
            FramerLoads.insert(li);

            vector<Instruction*> insToBeInserted;

            Value* replica= getInstReplacement(constuse,tagged, origGV, // test1 
                    li, insToBeInserted, FramerLoads);

            //TODO: insert ins in insToBeInserted before  
            insertNewIns (insToBeInserted, IU);
            insToBeInserted.clear();

            unsigned myidx= getopidx(IU, use);
            assert(IU->getOperand(myidx)->getType()==replica->getType()); 
            IU->setOperand(myidx, replica); //do something.
           
           dbg( 
            if (isa<CallInst>(IU)) {
                Function * myf= cast<CallInst>(IU)->getCalledFunction();
                if (myf!=nullptr) {  
                    if (myf->isDeclaration())  {
                        errs()<<"load: "<<*li<<"\n";
                        errs()<<" li op: "<<*li->getPointerOperand()<<"\n"; 
                        errs()<<"new IU: "<<*IU<<"\n";
                    }
                }
            }
            )
        }
    }
    else if (isa<ConstantExpr>(user) || isa<ConstantAggregate>(user)) { 
        Constant * CU= cast<Constant>(user); 
        if (CU->use_empty()) {
            return;
        }
        int OrigNumUses= CU->getNumUses();
        int usenum=0;
        
        Use * currentUse= &*CU->use_begin();
        Use * nextUse= currentUse;
        
        while ( nextUse ) {
            nextUse = currentUse->getNext();

            handleUsesOfGV(currentUse,tagged,
                           untagged, origGV, gvTag, 
                           FramerLoads, inits); //TODO: check if it's user or cit 
            usenum++;
        
            currentUse = nextUse;
        }
        assert(usenum==OrigNumUses && "Not all uses traversed!\n");
    }
    else {
        errs()<<"GV replacement- something else. TODO\n";
        if (isa<Operator>(user)) errs()<<"--> Operator. do something\n";
        if (Constant* cuser= dyn_cast<Constant>(user)) {
            if (isa<ConstantAggregate>(cuser)) errs()<<"--> ConstantAggregate\n";
            else if (isa<ConstantData>(cuser)) errs()<<"--> ConstantAggregate\n";
            else if (isa<GlobalValue>(cuser)) errs()<<"--> GlobalValue\n";
            else errs()<<"Something else.\n";
        }
        exit(0); // do something
    }

}


static void 
castAndreplaceAllUsesWithForGV (GlobalVariable * originalGV, 
                Constant * taggedGV, Constant * untaggedGV,
                GlobalVariable * gvTG, set <Instruction*> & FramerLoads,
                set<tuple<GlobalVariable*, Constant*, Constant*>> & inits)
                //set<pair<GlobalVariable*, Constant*>> & inits)
{
    Use * currentUse =  &*originalGV->use_begin();
    Use * nextUse = currentUse;
    
    while ( nextUse ) {
               
        nextUse = currentUse->getNext();

        handleUsesOfGV (currentUse, taggedGV, untaggedGV, 
                        originalGV, gvTG, FramerLoads, inits); 
        
        currentUse = nextUse;
        //myusenum++;
    }
}


static void pushtoarglist (Instruction * insertBeforeMe,  
                            Type * paramTy,
                            Value * arg, 
                            vector<Value*> & arglist,
                            Module & M) 
{
    if (paramTy != arg->getType()) {
        if (CastInst* temp= dyn_cast<CastInst>(arg)) {
            if (temp->getSrcTy() == paramTy) {
                arglist.push_back(temp->getOperand(0));
                return;
            }
        }
        if (paramTy->isPointerTy() && arg->getType()->isPointerTy()){
            
            BitCastInst * mybitcastinst= new BitCastInst (arg, paramTy,"");
            arglist.push_back(mybitcastinst);
        }
        else if (paramTy->isIntegerTy() && arg->getType()->isVectorTy()) {
            if (paramTy->getIntegerBitWidth()!=FramerGetBitwidth(arg->getType(), &M.getDataLayout())) {
                BitCastInst * mybitcastinst= new BitCastInst(arg, Type::getIntNTy(M.getContext(),FramerGetBitwidth(arg->getType(),  &M.getDataLayout())), "", insertBeforeMe);
                ZExtInst * myzext= new ZExtInst(mybitcastinst, paramTy, "");  
                arglist.push_back(myzext);
            }
            else {
                BitCastInst * mybitcastinst= new BitCastInst (arg, paramTy,"");
                arglist.push_back(mybitcastinst);
            }
        }
        else if (isa<PtrToIntInst>(arg)||isa<TruncInst>(arg)||isa<FPToSIInst>(arg)) {
            ZExtInst * myzext = new ZExtInst (arg, paramTy, "");
            arglist.push_back(myzext);
        }
        else if (isa<SExtInst>(arg)) {
            SExtInst * mysext = new SExtInst (arg, paramTy, "");
            arglist.push_back(mysext);
        }
        else if (paramTy->isIntegerTy() && arg->getType()->isIntegerTy()) {
            assert(paramTy->getIntegerBitWidth() >= (arg->getType())->getIntegerBitWidth()
                    && "created arg for hook's int bitwdith is bigger than hook's original type width!\n");
            SExtInst * mysext = new SExtInst (arg, paramTy, "");
            arglist.push_back(mysext);
        }
        else if (paramTy->isIntegerTy()&& arg->getType()->isDoubleTy()) {
            FPToUIInst * myfptoui= new FPToUIInst (arg, paramTy,"");
            arglist.push_back(myfptoui);
        }
        else if (paramTy->isIntegerTy() && arg->getType()->isPointerTy()) {
            PtrToIntInst * myptoi= new PtrToIntInst (arg, paramTy, "");
            arglist.push_back(myptoi); 
        }
        else {
            errs()<<"ParamTy: "<<*paramTy<<", arg: "<<*arg->getType()<<"\n";
            errs()<<"!!!Unspecified type conversion!\n";
            exit(0);
        }
        return;
    }
    else {
        arglist.push_back(arg);
    }
}


