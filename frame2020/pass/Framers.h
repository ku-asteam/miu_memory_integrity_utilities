
#include<climits>

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

//#include "llvm/Transforms/FramerLoopOpt/CheckInfo.h"
//#include "llvm/Transforms/FramerLoopOpt/Utility.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Transforms/Utils/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../lib/IR/ConstantsContext.h"
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

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%% Setting enables/disables %%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

/// ENABLING ALL RUNTIME CHECKS (bounds, typecast, etc)


/// STORE ONLY CHECK /////////////////
//#define STORE_ONLY_CHECK
//%%
//// TYPECHECK ////////////
//#define TYPECHECK

#define DISABLE_CHECKS_AT_GEP

//// ENABLE_SPACEMIU /// CASTOR or spaceMiu
#define ENABLE_SPACEMIU

//#define DISABLE_RT_TABLE // to debug perlbench

#define INLINE_CUSTOM_MALLOC_WRAPPER

/////////////////////////////
///// TRACK STRUCT //////////

#define TRACK_STRUCT_ALSO

/////////////////////////////
// ENABLE tracking arrays 
//#define ENABLE_TRACK_ARRAYS

/////////////////////////////
// All should be disabled for release.

//// DISABLE handling alloca.
#define DISABLE_HOOK_ALLOCA  

//// DISABLE handling global variables
#define DISABLE_HOOK_GLOBAL_VARIABLE

// DISABLE tagging GVs.
//#define DISABLE_TAGGING_GV

// DISABLE replacement debug. (Disable anyway for release mode)
//#define DISABLE_FAKE_REPLACEMENT

// DISABLE cheap checks just to check check_mem hook is optimized away or not.
//#define DISABLE_CHEAP_CHECKS

// DISABLE bounds check at store/load/mem funcs. 
//#define DISABLE_BOUNDS_CHECKS

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
        case 9: bitnum = 64; break;
        default: errs()<<"?? \n"; exit(0);
    }
    return bitnum;
}

/* check if the GV is a string in printf function. */
//bool SolitaryFramer::isPrintfStr ( GlobalVariable * GV )
static bool 
isPrintfStr ( GlobalVariable * GV )
{
    if ( !(GV->hasPrivateLinkage() 
        && GV->hasGlobalUnnamedAddr() 
        && GV->isConstant()) ) {
        dbg(errs()<<"not printf\n";)
        return false;
    }

    if ((GV->getName().startswith(".str.")
        ||GV->getName().startswith("str"))) {
        return true;
    }
    
    if (GV->hasOneUse()) {
        
        Value* val= (&*GV->use_begin())->getUser();    
        for (Value::use_iterator it = val->use_begin(), 
                ie = val->use_end(); it!=ie ; ++it) {
            
            if (CallInst* ci= dyn_cast<CallInst>((&*it)->getUser())) {
                StringRef fname = ci->getCaller()->stripPointerCasts()->getName();
                if (!fname.equals("printf")
                    && !fname.equals("puts")
                    && !fname.equals("__assert_fail")
                    && !fname.equals("fwrite")){ 
                    return false;               
                }
            }
        }
        return true;
    }
    
    bool isprintfstring= true;
   
    for (Value::use_iterator it = GV->use_begin(), 
            ie = GV->use_end(); it!=ie ; ++it) {
        
        Value* val= (&*it)->getUser();  
        for (Value::use_iterator it1 = val->use_begin(), 
                ie1 = val->use_end(); it1!=ie1 ; ++it1) {
            
            if (CallInst * ci= dyn_cast<CallInst>((&*it1)->getUser())) {
            StringRef fname = ci->getCaller()->stripPointerCasts()->getName();
                if (fname.startswith("llvm.memset")
                    || fname.startswith ("llvm.memcpy")
                    || fname.startswith ("llvm.memmove")
                    || fname.startswith ("llvm.strcpy")) {
                    // TODO: add more addition: all string funcs? 
                    errs()<<*GV<<"-- char array used for mem access func. so processing.. \n";
                    isprintfstring= false;
                    break;          
                }
            }
            else if (Function* f= dyn_cast<Function>((&*it1)->getUser())) {
                if (f->getName().startswith("llvm.memcpy")) {
                    errs()<<">>GV: "<<*GV<<"\n";
                    errs()<<"getuser"<<*(&*it1)->getUser()<<"\n";

                }
            }
        }
    }
    return isprintfstring;

   // && GV->getName().startswith(".str")); commented out since there are other strings named with something else.
    return false;
}

static bool
isNonArrayAccess(GEPOperator * op)
{
    Value * ptrop= op->getPointerOperand()->stripPointerCasts(); 
   
    if (isa<GlobalVariable>(ptrop) || isa<AllocaInst>(ptrop)) {
    
        PointerType * pty= dyn_cast<PointerType>(ptrop->getType()); 
        assert(pty!=nullptr);
        
        if (pty->getElementType()->isArrayTy()) {
            return false;      
        }
        if (pty->getElementType()->isStructTy()
            || pty->getElementType()->isVectorTy()) {
            return true;
        }
        if (isa<GlobalVariable>(ptrop)) {
            GlobalVariable * gv= cast<GlobalVariable>(ptrop);
            if (isPrintfStr(gv) ||
                (gv->getName()).startswith("llvm.used") ||
                 gv->getName().startswith("switch.table") ) {
                return true;
            }

        }
    }
    return false;
}

static bool
isNonStructAccess(GEPOperator * op)
{
    Value * ptrop= op->getPointerOperand()->stripPointerCasts(); 
   
    if (isa<GlobalVariable>(ptrop) || isa<AllocaInst>(ptrop)) {
    
        PointerType * pty= dyn_cast<PointerType>(ptrop->getType()); 
        assert(pty!=nullptr);
        
        if (pty->getElementType()->isArrayTy()) {
            return true;      
        }
        if (pty->getElementType()->isStructTy()
            || pty->getElementType()->isVectorTy()) {
            return false;
        }
        if (isa<GlobalVariable>(ptrop)) {
            GlobalVariable * gv= cast<GlobalVariable>(ptrop);
            if (isPrintfStr(gv) ||
                (gv->getName()).startswith("llvm.used") ||
                 gv->getName().startswith("switch.table") ) {
                return true;
            }

        }
    }
    return false;
}

static bool
isCustomWrapper (Function * wpf)
{
    ///  
    // TODO: function pointer to a wrapper function?
    /// 
    /// At the moment, we assume we take a list of malloc wrapper.
    /// more TODO: call func_ptr_malloc, or multi-depth wrappers 
    
    if (wpf->getName().startswith("Perl_safesysmalloc") 
        || wpf->getName().startswith("Perl_malloc") 
        || wpf->getName().startswith("Perl_safesysrealloc") 
        || wpf->getName().startswith("Perl_realloc") // 400.perlbench wrappers  
        || wpf->getName().startswith("xalloc") 
        || wpf->getName().startswith("xmalloc") 
        || wpf->getName().startswith("xrealloc") // 445.gobmk wrappers 
    //    || wpf->getName().startswith("hashtable_new") 
        || wpf->getName().startswith("sre_malloc") 
        || wpf->getName().startswith("sre_realloc") //456.hmmer 
        ) {
        
        return true;
    }

/*
    // TODO: this is not catching malloc wrapper right now. 
    const DataLayout & DL = M.getDataLayout();
    
    Function * func= ci->getFunction();
   
    // We assume a func is a mallco family wrapper if it meets 2 requirements
    // (1) ptr= ci (call mallocfamily) is alias with return of the func
    /// (1.1) find ret inst. if any of ret's op is alias with ci, then meeting (1)
    // (2) no memory write inside func.
   
    const Value *AccessPtr = getUnderlyingObject(ci, DL);
    
    bool isAliasWithReturn= false;
    bool MemoryWriteOccur= false;

    for (Function::iterator bb= func->begin(); bb!= func->end(); bb++) {
      for (BasicBlock::iterator it= bb->begin(); it!=bb->end(); it++) {
     
        Instruction * ins= &*it;
     
        if (isa<ReturnInst>(ins)) {
            errs()<<"ret: "<<*ins<<"\n"; 
            Value * retval= cast<ReturnInst>(ins)->getReturnValue();
            const Value *retPtr = getUnderlyingObject(retval, DL);
                
            if (AccessPtr == retPtr || AA.isMustAlias(retPtr, AccessPtr)) {
                errs()<<" --> alias with call!\n";
                isAliasWithReturn= true;
            }
        }
        if (ins->mayWriteToMemory()) {
           errs()<<" --> write to memory!\n";
           MemoryWriteOccur= true;
           break;
        }
      }
   
      if (MemoryWriteOccur) break;
    }
  
    if (isAliasWithReturn && !MemoryWriteOccur) {
        return true;
    }
    return false;
    
*/

  return false;
}


static ConstantInt *
getObjSizeFromCallInst (CallInst * ci)
{
  
  ConstantInt * objsize= nullptr;
   
  // if a malloc call (op num is 1) or malloc wrapper with arg num 1.
  if (ci->getNumArgOperands()==1) { 
    objsize= dyn_cast<ConstantInt>(ci->getOperand(0)); 
  }
  // if a realloc call (op num is 2) or realloc wrapper with arg num 2.
  else if (ci->getNumArgOperands()==2) {
    objsize= dyn_cast<ConstantInt>(ci->getOperand(1)); 
  }
  else {
    
    // special case of custom wrapper - sre_malloc (x,y,size)
    if (ci->getCalledFunction()->getName().equals("sre_malloc")) {
        objsize= dyn_cast<ConstantInt>(ci->getOperand(2)); 
    }
    else if (ci->getCalledFunction()->getName().equals("sre_realloc")) {
        objsize= dyn_cast<ConstantInt>(ci->getOperand(3)); 
    }
  }
  
  return objsize;
}




static bool
MayBeHeapArray (Value * ptr)
{
    CallInst * ci= dyn_cast<CallInst>(ptr);
    
    if (!ci) return false;
    
    Function * func= ci->getCalledFunction();

    if (!func) return false;

    StringRef fname= func->getName();

    if (fname.equals("calloc")) return true;
     
    if ((fname.startswith("malloc"))
        && !isCustomWrapper(ci->getFunction())
        && !getObjSizeFromCallInst(ci)) {
        
        return true;
    }
        
    return false;
}


// CCured's safeptr - not involved with pointer arith or type cast
static bool 
isSafePtr (Value * ptr)
{
    Value * p=ptr->stripPointerCasts(); 
    if (isa<GlobalVariable>(p) || isa<AllocaInst>(p)) {
        return true;   
    }
    if (isa<GEPOperator>(p)) { //li's ptrop == gep. return false.

      #ifndef TRACK_STRUCT_ALSO 
        if (isNonArrayAccess(cast<GEPOperator>(p))) {
            return true;
        }
      #else 
        if (isNonStructAccess(cast<GEPOperator>(p))) {
            return true;
        }
      #endif
        return false;
    }
  #ifndef ENABLE_TRACK_ARRAYS
    if (MayBeHeapArray(ptr)) {
        return true;   
    }
  #endif
  
    return false;
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
     
    /*if ((allocatedTyID > Type::VoidTyID 
         && allocatedTyID <= Type::PPC_FP128TyID)
        || allocatedTyID== Type::X86_MMXTyID ){
        return allocatedType->getPrimitiveSizeInBits(); 
    }*/
    if (IntegerType * intTy= dyn_cast<IntegerType>(allocatedType)) {
        return intTy->getBitWidth();
    }
    //else if (isa<CompositeType>(allocatedType)) {
        //if (isa<PointerType>(allocatedType)) {
        //    return dlayout->getPointerSizeInBits(); //8 bytes..
        //}
    else if (StructType * structTy = dyn_cast<StructType>(allocatedType)) {
      return (unsigned) getBitwidthOfStruct (structTy, dlayout);
    }
    else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
      return (unsigned)(arrayTy->getNumElements())*getNumBits(arrayTy->getElementType(), dlayout); 
    }
    else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {

//      if (vecty->getBitWidth()!=0) {
//        return vecty->getBitWidth();
//      }
//      else {
        return (unsigned)(vecty->getNumElements())*getNumBits(vecty->getElementType(), dlayout); 
//      }
    }
     //   else {
     //       errs()<<"1. what type is this - "<<*allocatedType<<"\n";
     //       exit(0);
     //   }
    //}
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else if (isa<FunctionType>(allocatedType)) {
        //assert(isa<FunctionType>(allocatedType)); 
        errs()<<" functiontype in getNumBits\n";
        return 0;
    }
    else {
        
        assert(!allocatedType->isVoidTy()); // what should I do for this?
        return allocatedType->getPrimitiveSizeInBits();
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

static bool
isUnionTy (Type * ty)
{
    StructType * sty= dyn_cast<StructType>(ty);
    
    if (sty==nullptr) return false;
  
    if (!sty->hasName()) return false; 
        
    //errs()<<" sty: "<<*sty<<"\n"; 
    if (sty->getName().startswith("union.")) {
      //  errs()<<"  Union! "<<sty->getName()<<"\n";

        return true;
    }
    return false; 
}




static void
insertSubTypes(Type * ty, vector<Type*> & tlist)
{

  if (getIdx(tlist, ty) < 0) {
    tlist.push_back(ty);
   // errs()<<" insert: "<<*ty<<"\n";
  }

  if (isa<StructType>(ty)) {
      StructType * sty= cast<StructType>(ty);

//// to skip adding an unresolved opaque type in Perlbench.
//  if (sty->isOpaque()) {
//      errs()<<" dirstream skip: "<<*sty<<"\n";
//      return;
//  }
////    
      for (unsigned i=0;i<sty->getNumElements();i++) {
        insertSubTypes(sty->getElementType(i), tlist);
      }
  }
  else if (isa<ArrayType>(ty)) {
    ArrayType * aty= cast<ArrayType>(ty);
    insertSubTypes(aty->getElementType(), tlist);    
  }
  else if (isa<PointerType>(ty)) {
    PointerType * pty= cast<PointerType>(ty);
    
    if (getIdx(tlist, pty->getElementType()) >= 0) {
      return;
    } 
    insertSubTypes(pty->getElementType(), tlist);
  }
  else if (isa<FunctionType>(ty)) {
      
    FunctionType * fty= cast<FunctionType>(ty);

    if (fty->isVarArg()) return;
    
    insertSubTypes (fty->getReturnType(), tlist);

    for (int pi=0; pi< fty->getNumParams(); pi++) {

      if (getIdx(tlist, fty->getParamType(pi)) >= 0) continue;
          
      insertSubTypes(fty->getParamType(pi), tlist);
    }
  }

  return;
  
}
 
static void
createAllTypeList(vector<Type*> & AllTypeList, Module & M)
{
    const DataLayout * dlayout= &M.getDataLayout();

    /// (1) insert BasicTypes and their Pointertype to the vector
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::VoidTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::HalfTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::FloatTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::DoubleTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::X86_FP80TyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::FP128TyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::PPC_FP128TyID));
//    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::LabelTyID));
//    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::MetadataTyID));
    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::X86_MMXTyID));
//    AllTypeList.push_back(Type::getPrimitiveType(M.getContext(), Type::TokenTyID));
    
    /// (2) insert all inttypes.
    AllTypeList.push_back(IntegerType::get(M.getContext(), 8));       
    AllTypeList.push_back(IntegerType::get(M.getContext(), 16));
    AllTypeList.push_back(IntegerType::get(M.getContext(), 32)); //10
    AllTypeList.push_back(IntegerType::get(M.getContext(), 64));         
    AllTypeList.push_back(IntegerType::get(M.getContext(), 128));      
    AllTypeList.push_back(IntegerType::get(M.getContext(), 1));    
    AllTypeList.push_back(IntegerType::get(M.getContext(), 48));       

    // (3) insert Struct types and its field types.
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    
    for (vector<StructType*>::iterator it=temp.begin(),
            ie=temp.end();it!=ie;++it) {

        StructType * sty= (*it);

        errs()<<"sty:: "<<*sty<<"\n";

        //opaque. 
        // 1) when creating typelist, add it, and leave it as opaque.
        // 2) when creating up/downcast list, consider it "safe" from/to any types 
   
   /*     
        if (sty->isOpaque()) { 
            errs()<<"OPAQUE:" <<*sty<<". Check what I should do. \n"; 
            exit(0);     
            continue; // hm..should I skip this?
        }
   */     
        // * in this vrsion of SpaceMiu, we do not deal with packedstructure.
        // * to handle them, we need to consider offsets in reference rules. 
        if (sty->isPacked()) continue;
        
        // * now identified types in llvm are not structurally uniqued.
        if (sty->getName().startswith("struct.FRAMER")) continue; 
     
        ///////// 
         
        if (sty->getName().startswith("union.")) {
       
            const StructLayout * slayout= dlayout->getStructLayout(sty);
            
            errs()<<"UNION- "<<*sty<<"\n";
            
            for (unsigned x=0; x<sty->getNumElements(); x++) {
                errs()<<"\telem "<<x<<": "<<*sty->getElementType(x)<<"\n";
                errs()<<"\t  offset"<<slayout->getElementOffset(x)<<"\n";
            }
            //errs()<<"  alignment: "<<slayout->getAlignment()<<"\n";
        }

      /////////
        insertSubTypes(sty, AllTypeList); // insert to tlist including itself.
    }
    
    /// 
    // (4) insert types used in bitcast. 
    ///
    
    errs()<<" 1. typelist size: "<<AllTypeList.size()<<"\n";
     
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
      if (isHookFamilyFunction (&*mi)) {
          continue;
      }
      for (Function::iterator bit=(*mi).begin();bit!=(*mi).end();++bit) {
        for (BasicBlock::iterator iit=(*bit).begin();iit!=(*bit).end();++iit) {
                
          if (!isa<BitCastOperator>(iit)) continue;
                
          BitCastOperator * bc= cast<BitCastOperator>(iit);
          
          PointerType * spty= dyn_cast<PointerType>(bc->getSrcTy());
          PointerType * dpty= dyn_cast<PointerType>(bc->getDestTy());
                
          if (spty) {
            
            Type * pelem= spty->getElementType();
            insertSubTypes(pelem, AllTypeList); 
            
          }
                
          if (dpty) {
            
            insertSubTypes(dpty->getElementType(), AllTypeList);
            
            
          }
        }
      }
    }
    errs()<<" 2. typelist size: "<<AllTypeList.size()<<"\n";
    /// 
    // function's param type push to type list.
    ///
    int tempsize= AllTypeList.size();

    for (int i=0; i< tempsize; i++) {
    
      Type * ty= AllTypeList.at(i);
      
      FunctionType * fty= dyn_cast<FunctionType>(ty); 

      if (!fty) {
      
        PointerType * pty= dyn_cast<PointerType>(ty);    
        
        if (!pty) continue;
        
        fty= dyn_cast<FunctionType>(pty->getElementType());        
        
        if (!fty) continue;
      }
      
      if (fty->isVarArg()) continue;
      
      for (int pi=0; pi< fty->getNumParams(); pi++) {
        
        int idx= getIdx(AllTypeList, fty->getParamType(pi));
        
        if (idx<0) AllTypeList.push_back(fty->getParamType(pi));

      }
    }
  
    ///  print all types
  //  errs()<<"#### All TypeList #################\n";
  //  for (int i=0; i< AllTypeList.size(); i++) {
  //      errs()<<"> "<<i<<" : "<<*AllTypeList.at(i)<<"\n";
  //  }

}

static void 
buildFields (Type * ty, vector<short> & fields, vector<Type*> & tlist)
{
    if (ty->isVoidTy()) {
        return;
    }
    else if (isa<StructType>(ty) && !isUnionTy(ty)) {
        
        StructType * sty= cast<StructType>(ty);
     
      #ifndef ENABLE_CHECK_OPAQUE_TYPES
        if (sty->isOpaque()) {
          short result= getIdx(tlist, ty);
          assert(result>=0);
          fields.push_back(result);
          return;
        }
      #endif
        for (unsigned i=0;i<sty->getNumElements();i++) {
            buildFields(sty->getElementType(i), fields, tlist);    
        }
    }
    //else if (isa<SequentialType>(ty)) {
    else if (ty->isArrayTy() || ty->isVectorTy()) {
    
        //SequentialType * aty= cast<SequentialType>(ty);
        uint64_t elemnum= 0;
        Type * elemty= nullptr;

        if (ty->isArrayTy()){ 
            elemnum= cast<ArrayType>(ty)->getNumElements();
            elemty=  cast<ArrayType>(ty)->getElementType();
        }
        else { 
            elemnum= cast<VectorType>(ty)->getNumElements();
            elemty=  cast<VectorType>(ty)->getElementType();
        }
       
        assert(elemnum && elemty);
        
        //for (uint64_t i=0;i<aty->getNumElements();i++) {
        for (uint64_t i= 0; i < elemnum; i++) {
            buildFields(elemty, fields, tlist);    
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
  dbg(  errs()<<"src: "<<*src<<", dest: "<<*dest<<"\n"; )
    short stid= getIdx(tlist, src);
    short dtid= getIdx(tlist, dest);
    
    assert(stid >= 0 && dtid >= 0);
     
    for (unsigned i=0; i<(safecasts.at(stid)).size(); i++) {
        short tyid= (safecasts.at(stid)).at(i); 
        if (tyid==dtid) {
          //errs()<<"\t ---> SAFE CAST!\n";
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

    /// strip off both types' pointer.

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
  // instead of traversing downcast list with pointer itself, 
  // trying with its element type.
   
    //short srcid= getIdx(tlist, src);
    //short destid= getIdx(tlist, dest);
    short srcid= getIdx(tlist, cast<PointerType>(src)->getElementType());
    short destid= getIdx(tlist, cast<PointerType>(dest)->getElementType());
  
  dbg(  errs()<<"src: "<<*src<<", dest: "<<*dest<<"\n"; )
    
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

static unsigned
getAlgnVal(Type * ty, const DataLayout * dl)
{
  if (StructType * sty=dyn_cast<StructType>(ty)) {
    const StructLayout * sl= dl->getStructLayout(sty); 
    return (unsigned)(sl->getAlignment()).value();
  }
  //else if (SequentialType * sqty= dyn_cast<SequentialType>(ty)) {
  else if (ty->isArrayTy() || ty->isVectorTy()) {
    
    Type * et= nullptr;

    if (ty->isArrayTy()) 
        et= cast<ArrayType>(ty)->getElementType();
    else 
        et= cast<VectorType>(ty)->getElementType();
    
    //Type * et= sqty->getElementType();
    return getAlgnVal(et, dl);
  }
  else {
    //return getNumBits(ty, dl)/8;
    return ty->getPrimitiveSizeInBits()/8;
  }
  /*
  else if (ty->isVoidTy()) {
    return 1; 
  }
  else {
    errs()<<"do something for Ty: "<<*ty<<"\n";
    exit(0); 
  }
  */
}

static bool
isSafeCastofUnionTy (Type * from, Type * to,
                     const DataLayout * dl)
{
  uint64_t algnf= 0; 
  uint64_t algnt= 0; 
  
dbg(  errs()<<"from: "<<*from<<"<, to: "<<*to<<"\n"; ) 

  if (from->isVoidTy()) return false;
  
  if (to->isVoidTy()) return true;

  if (!from->isSized() || !to->isSized()) return false; 

  /// fromTy 
  if (isUnionTy(from)) {
    const StructLayout * sl= dl->getStructLayout (cast<StructType>(from)); 
    algnf= (sl->getAlignment()).value();
  }
  else {
    algnf= getAlgnVal(from, dl); 
  }
  
  /// toTy 
  if (isUnionTy(to)) {
    const StructLayout * sl= dl->getStructLayout (cast<StructType>(to)); 
    algnt= (sl->getAlignment()).value();
  }
  else {
    algnt= getAlgnVal(to,dl); 
  }

  //assert(algnf!=0 && algnt!=0);
   
  uint64_t fsize= dl->getTypeSizeInBits(from);
  uint64_t tsize= dl->getTypeSizeInBits(to);

dbg(
  errs()<<"falign: "<<algnf<<", talign: "<<algnt<<"// fsize: "<<fsize<<", tsize: "<<tsize<<"\n";
)

  if (algnf >= algnt && fsize >= tsize) {
    return true; 
  }
  return false;
}

/* one of them is 64-width integer, return true. */
static bool
oneOfThemIsInt64 (Type * fromT, Type * toT)
{
    if (isa<IntegerType>(fromT)) { 
      if (cast<IntegerType>(fromT)->getBitWidth()== 64) return true;
    }
    
    if (isa<IntegerType>(toT)){ 
      if (cast<IntegerType>(toT)->getBitWidth()== 64) return true;
    }
    
    return false;
}
/*
static bool
isSafeCastofFuncPtr(Type * src, 
                    Type * dest,
                    vector <Type*> & tlist, 
                    vector<vector<short>> & llist, 
                    const DataLayout * dlayout,
                    vector<short> & fq,
                    vector<short> & tq)
{
    if (dest->isVoidTy()) return true;
    
    FunctionType * from= cast<FunctionType>(src);
    FunctionType * to= cast<FunctionType>(dest);
    
    if (!from || !to) return false;
    
    Type * fr= from->getReturnType();
    Type * tr= to->getReturnType();
     
    if (isConversibleTo(llist.at(getIdx(tlist,fr)), 
                        llist.at(getIdx(tlist,tr)),
                        tlist,llist,dlayout,fq,tq)) return false; 
   
    //do something. currently return true to avoid halts at error.
    if (from->isVarArg() || to->isVarArg()) {
        errs()<<"FRAMER: var arg\n";
        errs()<<"from:\t"<<*from<<"\n";
        errs()<<"to:\t"<<*to<<"\n";
        exit(0);
    }
    
    if (from->getNumParams () != to->getNumParams ())  return false;
     
    for (unsigned i=0; i< from->getNumParams(); i++) {
        Type * farg= from->getParamType(i);
        Type * targ= to->getParamType(i);
       
        if(!isConversibleTo(llist.at(getIdx(tlist,farg)), 
                            llist.at(getIdx(tlist,targ)),
                            tlist,llist,dlayout,fq,tq)) return false; 
    }

    return true;
}
*/


static bool
isConversibleTo(vector<short> & from, 
                vector<short> & to,
                vector <Type*> & tlist, 
                vector<vector<short>> & llist, 
                const DataLayout * dlayout,
                vector<short> & fq,
                vector<short> & tq) 
{
 
    if (from.size() < to.size()) {
        return false;
    }

    if (from.size()==0 && to.size()==0) return true;   //e.g. void?       
    
    for(unsigned i=0;i<to.size();i++) {
      
        Type* fromT= tlist.at(from.at(i)); 
        Type* toT= tlist.at(to.at(i));
       
        if (fromT==toT) { /// <<-  correct?
            continue;
        }
        
    #ifndef ENABLE_FUNCTION_POINTER   

        if (fromT->isFunctionTy() || toT->isFunctionTy()) {

            if (toT->isVoidTy()) continue;

            FunctionType * from= dyn_cast<FunctionType>(fromT);
            FunctionType * to= dyn_cast<FunctionType>(toT);

            if (!from || !to) return false;
            
           // errs()<<"\n  Func from:\t"<<*fromT<<"\n";
           // errs()<<"  Func to:\t"<<*toT<<"\n";

            Type * fr= from->getReturnType();
            Type * tr= to->getReturnType();
    
            if (!isConversibleTo(llist.at(getIdx(tlist,fr)), 
                        llist.at(getIdx(tlist,tr)),
                        tlist,llist,dlayout,fq,tq)) {
            
            //    errs()<<"  -> return unsafe\n";

                return false; 
            }
    
            //do something. currently return true to avoid halts at error.
            if (from->isVarArg() || to->isVarArg()) {
            //    errs()<<"  -> variadic args. return true\n";
                continue;
            }

            if (from->getNumParams() != to->getNumParams()) {
            //    errs()<<"  --> #param not match\n";
                return false;
            }
    
            for (unsigned pi=0; pi< from->getNumParams(); pi++) {

                Type * farg= from->getParamType(pi);
                Type * targ= to->getParamType(pi);

                if(!isConversibleTo(llist.at(getIdx(tlist,farg)), 
                                    llist.at(getIdx(tlist,targ)),
                                    tlist,llist,dlayout,fq,tq)) {
                    
              //      errs()<<"   unsafe -> "<<pi<<"'s param not match.\n";
                    return false; 
                }
            }
    
            continue;
        }
    #else
        printf("FRAMER ERROR: do something for function pointer!");
        exit(0);
    #endif


        if (!fromT->isSized() || !toT->isSized()) {
            return false; 
        }

       /// check union type compatibility before it checks struct types.
         


      #ifndef ENABLE_CHECK_OPAQUE_TYPES
        if (isa<StructType>(fromT) || isa<StructType>(toT)) {
         
          StructType * styf= dyn_cast<StructType>(fromT); 
          StructType * styt= dyn_cast<StructType>(toT);
            
          if (styf) {
            if (styf->isOpaque()) continue;
          }
          if (styt) {
            if (styt->isOpaque()) continue; 
          }
        }
      #endif

        if (isa<PointerType>(fromT) || isa<PointerType>(toT)){
          
            if (oneOfThemIsInt64(fromT, toT)) return true; 
            
            if (!isa<PointerType>(fromT) || !isa<PointerType>(toT)) {
                return false; 
            }
            // now both are pointers.
            
            Type * felemT= (cast<PointerType>(fromT))->getElementType(); 
            Type * telemT= (cast<PointerType>(toT))->getElementType(); 
            
            // result type is void --> valid conversion in C (not in C++)
           
            if (felemT==telemT) continue;

            /// union is considered non-aggregate so one elem! 
            /// like int. so fields are smaller.
            
            if (isUnionTy(felemT) || isUnionTy(telemT)) {
                if (isSafeCastofUnionTy (felemT, telemT, dlayout)) {
                    continue; 
                }
                else {
                    return false;
                }
            }

//// moved to here
            
            short f_idx= getIdx(tlist, felemT);             
            short to_idx= getIdx(tlist, telemT);             

        if (f_idx < 0) {
            errs()<<"felemT: "<<*felemT<<"\n";
        }
        if (to_idx < 0) {
            errs()<<"toT: "<<*telemT<<"\n";
        }


            assert(f_idx>=0 && to_idx>=0); 
          ////////// 
         
            short f_isrec= getIdx(fq, f_idx); 
            short t_isrec= getIdx(tq, to_idx);
            
            if (f_isrec>=0 && t_isrec>=0) {
                continue; 
            }
            fq.push_back(f_idx);
            tq.push_back(to_idx);
          
          ///////////

            bool iscompatible= isConversibleTo (llist.at(f_idx), 
                    llist.at(to_idx), tlist, llist, dlayout, fq, tq);
            
            fq.pop_back();  ///////
            tq.pop_back();  ///////

            if( !iscompatible) {
            //    errs()<<" NOT conversible\n";
                return false;
            }
            else {
            //    errs()<<" conversible\n";
                continue;
            }
        }
      
        uint64_t fsize= dlayout->getTypeSizeInBits(fromT);
        uint64_t tsize= dlayout->getTypeSizeInBits(toT);

        if (fsize!=tsize){ // TODO. pointertype? t1*, ty* 
            return false; 
        }

        if ((fromT->isIntegerTy() && !toT->isIntegerTy())
            || (toT->isIntegerTy() && !fromT->isIntegerTy())) {
            return false; 
        }
    }  
    return true; 
}

static void 
createLayOutList(bool is_CPP_Modules, 
                 vector<Type*> & tlist,
                 vector<vector<short>> & llist,
                 Module & M)
{

    // This function builds each type's physical layout of C, so returns for CPP.
    if (is_CPP_Modules) return; 

    for (unsigned i=0;i<tlist.size();i++){
     
        vector<short> fields;
        
     //   errs()<<">> ty layout: "<<*tlist.at(i)<<"\n";
     
     ////////
     // to handle unresolved opaque type in Perlbench. (struct.__dirstream)   
        if (isa<StructType>(tlist.at(i))) {
          StructType * sty= cast<StructType>(tlist.at(i));
          
          if (sty->isOpaque()) {
            //errs()<<sty->getName()<<"\n";
            //assert(sty->getName().startswith("struct.__dirstream"));  
            short otid= getIdx(tlist, (Type*)Type::getInt8Ty(M.getContext()));
            assert(otid >=0 ); 
            fields.push_back(otid); 
            llist.push_back(fields);
            continue;    
          }
        }
    /////////
        
        buildFields(tlist.at(i), fields, tlist);
        llist.push_back(fields);
    }
}

// check typesan: func recursiveProcessType in typesan.

static StructType *  
recursiveProcessSafeTy (StructType *STy, 
                      vector<short> & parents, 
                      vector<Type*> & tlist) 
{

    if(STy->isLiteral() || STy->isOpaque()) {
        return nullptr;
    }
   
    // Already processed, return it as it is
    // TODO. if is already in safecast
    
    auto classIt = parents.find(STy);
    if (classIt != parents.end()) {
        return STy; 
    }

    // Only check for primary parent class
    // Secondary parents are handled via offsets

    if (STy->elements().size() > 0) {
   
        Type * firstElement = *(STy->elements().begin());
        
        if (StructType *InnerSTy = dyn_cast<StructType>(firstElement)) {

            StructType * returnedsty= recursiveProcessSafeTy(InnerSTy);
            
            // Potential parent isn't really a parent ignore it
            if (!returnedsty)
                return nullptr; // or return returnedsty. the same.
            
            parents.push_back(getIdx(tlist, InnerSTy));

            // phantom class 
        }
    }
   
    //classInfoMap.insert(std::make_pair(STy, info));
    
    return STy;
}




static void
createSafeCastList_CPP (vector<Type*> & tlist, 
                        vector<vector<short>> & safecasts,
                        vector <vector<short>> & llist,
                        const DataLayout * dlayout) 
{
  // fill it,
  // for each type,we can get a list of parent types. hence, just add the types recursively.  
  
  for (unsigned i=0;i<tlist.size();i++) { 
        
    vector<short> inter; 
    
    if (tlist[i]->isStructTy()) { 
        
        StructType * itself= recursiveProcessSafeTy(tlist[i], inter, tlist); 
         
        if (itself) {
            inter.push_back (tlist[i]); 
        }
        // if nullptr is returned, don't save it e.g. opaque, literal, 
        // or already processed (when??)
    }
 
    safecasts.push_back(inter);
    // non-struct types will have an empty list.
  }

}

 
static void
createSafeCastList_C (vector<Type*> & tlist, 
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
        continue;
      }
           
      if (isUnionTy(tlist.at(i)) || isUnionTy(tlist.at(j))) {
        if (isSafeCastofUnionTy (tlist.at(i), tlist.at(j), dlayout)) {
          if (getIdx(inter,(short)j) >= 0) {
            continue; 
          }
          inter.push_back((short)j); 
          continue; 
        }
      }
      // to check if it's recursive type of not. 
      // Skip if both subtypes are in fq and tq.
      
      vector <short> fq;
      vector <short> tq;
            
      fq.push_back(i); //insert an id of fromTy
      tq.push_back(j); //insert an id of toTy
      
      //errs()<<"** "<<i<<", "<<j<<"\n";
       
     if (isConversibleTo(llist.at(i), llist.at(j),
                          tlist, llist, dlayout,
                          fq, tq)) {
             
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
createSafeCastList (bool is_CPP_Modules, 
                    vector<Type*> & tlist, 
                    vector<vector<short>> & safecasts,
                    vector <vector<short>> & llist,
                    const DataLayout * dlayout) 
{
    // TODO: use function pointer?
    
    if (is_CPP_Modules) {
        createSafeCastList_CPP (tlist, safecasts, llist, dlayout)
    }
    else {
        createSafeCastList_C (tlist, safecasts, llist, dlayout)
    }

    return; 
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
  
    ////////////
    // to handle an unresolved opaque type (struct.__dirstream in perlbench)   
        if (sty->isOpaque()) {
            errs()<<"OPAQUE: "<<*sty<<"\n";
        
            short current_offset= 0; 
            tidsPerDist.first= current_offset;
            onety.push_back(tidsPerDist);
         
            (tidsPerDist.second).clear();  
            return;
        }
    ////////////
         
        const StructLayout * slayout= dlayout->getStructLayout(sty); 
              
        for (unsigned j=0; j<sty->getNumElements(); j++) {
           
            Type * subty= sty->getElementType(j);
            
            short offset= slayout->getElementOffset(j); 
            short current_offset= preoffset+offset; 
            
            assert(preoffset < USHRT_MAX - offset);
             
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

            assert(preoffset < USHRT_MAX - offset);
 
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
                     unsigned & maxoffsperty
                     ,unsigned & totaloffsetcount // total count of pairs
                     ,unsigned & maxtysperoff
                     )  // the max of pair.second.size 
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

/* this offset table's entry per ty is {short offset, short tid_at_offset} */

static void
getSubTyOffsetsToTid(short tidx, 
                vector<Type*> & tlist, 
                unsigned & MaxOffset, // unsigned?
                unsigned preoffset,   //unsigned?
                vector <pair<unsigned, short>> & onety,
                vector <vector<short>> & safecasts,
                const DataLayout * dlayout)
{
    if (preoffset > MaxOffset) {
        MaxOffset= preoffset;
    }
    assert(tidx >= 0);
      
    // * for each ty, for each offset, we save a list of tyids, *
    // * that the type at the offset is safely casted to.
     
    if (StructType * sty= dyn_cast<StructType>(tlist.at(tidx))) {  
  
    ////////////
    // to handle an unresolved opaque type (struct.__dirstream in perlbench)   
        if (sty->isOpaque()) return;
        
    ////////////
         
        const StructLayout * slayout= dlayout->getStructLayout(sty); 
              
        for (unsigned j=0; j<sty->getNumElements(); j++) {
            
            unsigned offset= slayout->getElementOffset(j); 
            unsigned current_offset= preoffset+offset; 
            
         //   assert(preoffset < USHRT_MAX - offset);
             
            Type * subty= sty->getElementType(j);
            short subtyid= getIdx(tlist,subty);
            
            if (preoffset != current_offset) {
                
                pair <unsigned, short> cur_pair= make_pair(current_offset, subtyid); 
                // subtyid is shor-typed since it can be -1  
                onety.push_back(cur_pair);
            }
             
            getSubTyOffsetsToTid (subtyid, tlist, MaxOffset, //tidsPerDist,
                             current_offset, onety, safecasts, dlayout);           
            
        }
    }
    //else if (SequentialType * aty= dyn_cast<SequentialType>(tlist.at(tidx))) {
    else if (tlist.at(tidx)->isArrayTy() || tlist.at(tidx)->isVectorTy()) {
       
        Type * elty= nullptr;
        unsigned elemnum= 0;

        if (tlist.at(tidx)->isArrayTy()) {
            elty= cast<ArrayType>(tlist.at(tidx))->getElementType();
            elemnum= cast<ArrayType>(tlist.at(tidx))->getNumElements(); 
        }
        else {
            elty= cast<VectorType>(tlist.at(tidx))->getElementType();
            elemnum= cast<VectorType>(tlist.at(tidx))->getNumElements(); 
        }

        //Type * elty= aty->getElementType();
        short elsize= getNumBits(elty, dlayout)/8;
        
        //for (unsigned j=0; j<aty->getNumElements(); j++) {
        for (unsigned j=0; j< elemnum; j++) {
             
            unsigned offset= elsize * j; 
            unsigned current_offset= preoffset + offset; 
          
         //   assert(preoffset < USHRT_MAX - offset);
            
            short subtyid= getIdx(tlist,elty);
            
            
            if (preoffset != current_offset) {
                pair <unsigned, short> cur_pair= 
                        make_pair(current_offset, subtyid);  
                onety.push_back(cur_pair);
            }
            
            getSubTyOffsetsToTid (subtyid, tlist, MaxOffset, 
                         current_offset, onety, safecasts, dlayout);           
        }
    }
    else {
        // bottom case: isAtomicTy (int,float, MMX, vector etc)
        return;
    }
}


static void 
createRTOffsetTable (vector <Type*> & tlist, 
                     vector <vector <short>> & flatrtoffsets,
                     unsigned MaxOffset,
                     GlobalVariable* & rtOffsetTbl, 
                     Module & M)
{
  errs()<<"createRTOffsetTable start.....\n";
  
 // assert(offsets.size()==tlist.size());
    
  const DataLayout * dlayout= &M.getDataLayout(); 
    
  errs()<<"#All Types:\t"<<tlist.size()<<"\n";

  Type* int16T= IntegerType::getInt16Ty(M.getContext());
  Constant * defaultval= ConstantInt::get(int16T,-1);
  
  ArrayType* entryT= ArrayType::get(int16T, MaxOffset+1); //3 
  
  
  assert((MaxOffset+1)==(flatrtoffsets.at(0)).size());
     
  vector<Constant*> tblvec;
  ///
  // create entries for types used in a target program 
  ///
  for (short i=0;i<flatrtoffsets.size();i++) {

    vector<Constant*> tids; 

    for (unsigned j=0; j<(flatrtoffsets.at(i)).size(); j++) {
      
      short val= flatrtoffsets.at(i).at(j); 
      tids.push_back(ConstantInt::get(int16T, val));
    }
    Constant* constonety= ConstantArray::get(entryT, tids); 
     
    tblvec.push_back(constonety);  
  } 
  ///
  // create an entry for a type "compatible-with-all-types".
  // this type is assigned to heap objects without an effective type at runtime.
  ///
  vector<Constant*> unversaltype ((flatrtoffsets.at(0)).size(),ConstantInt::get(int16T,tlist.size())); // its typeID == total count
  Constant* cont_unversalty= ConstantArray::get(entryT, unversaltype); 
  tblvec.push_back(cont_unversalty);  
   
  //// print
dbg( 
  for (short i=0;i<flatrtoffsets.size();i++) {
    errs()<<"\n@@@@@ "<<i<<" "<<*tlist.at(i)<<"\n";

    for (short j=0; j<(flatrtoffsets.at(i)).size(); j++) {

      errs()<<" "<<flatrtoffsets.at(i).at(j); 
    }
    errs()<<"\n";
  }  
)
  ////

  //ArrayType* tableT= ArrayType::get(entryT, flatrtoffsets.size()); // final array!
  ArrayType* tableT= ArrayType::get(entryT, tblvec.size()); // final array!
     
  Constant *ctbl= ConstantArray::get(tableT, tblvec);
    
  rtOffsetTbl= new GlobalVariable (M, 
                              tableT, 
                              true, 
                              GlobalValue::ExternalLinkage,
                              ctbl,
                              "FRAMER_Offset_Table");

  errs()<<"createRTOffsetTable ends....\n";

}



static void
createTyOffsetList (
                    bool is_CPP_Modules, 
                    vector<Type*> & tlist,
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


static StructType *  
recursiveProcessDownTy (unsigned childid, // typeid of class type 
                        vector<vector<short>> & downcasts,
                        vector<Type*> & tlist) 
{
    StructType * STy= dyn_cast<StructType>(tlist[childid]);
    assert(STy); // we enter this func only when tlist[childid] is struct ty.  
    
    if(STy->isLiteral() || STy->isOpaque()) {
        return nullptr;
    }
   
    // Only check for primary parent class
    // Secondary parents are handled via offsets

    if (STy->elements().size() > 0) {
   
        Type * firstElement = *(STy->elements().begin());
        
        if (StructType *InnerSTy = dyn_cast<StructType>(firstElement)) {

            StructType * parent= recursiveProcessSafeTy(InnerSTy);
              
            // Potential parent isn't really a parent ignore it
            if (!parent)
                return nullptr; // or return returnedsty. the same.
            
            unsigned parentid= getIdx(tlist, parent);  
            
            // Already processed, return it as it is
            auto classIt = downcasts[parentid].find(childid);
            if (classIt != downcasts.end()) {
                return STy; 
            }
            
            downcasts[parentid].push_back(childid);  

            // Jin: sty has +1 elems, and 1st elem is sty, which is not opaque or literal.
            // to create a safecastlist, this is not necessary? 
            // it should be checked at downcast. 
            // if (STy->elements().size() == 1) {
            //    parentInfo->phantomChildren.push_back(info);
            //    parentInfo->fakeParentHashes.push_back(info->classHash);
            //}
        }
    }
   
    return STy;
}


static void 
createDownCastList_CPP (
                    vector<Type*> & tlist, 
                    vector<vector<short>> & downcasts,
                    vector <vector<short>> & llist,
                    const DataLayout * dlayout)
{
  
  // safe/down cast can be processed in one function maybe..
  // but for easier maintenance and simplicity  
 
  // initialise downcasts 

  for (unsigned i=0;i<tlist.size();i++) { 
    vector<short> children; 
    downcasts.push_back(children);
  }
  
  for (unsigned i=0;i<tlist.size();i++) { 
        
    if (tlist[i]->isStructTy()) { 
        
        StructType * itself= recursiveProcessDownTy(i, downcasts, tlist); 
         
        // if nullptr is returned, don't save it e.g. opaque, literal, 
        // or already processed (when??)
    }
 
    // non-struct types will have an empty list.
  }

}

static void 
createDownCastList_C (
                    vector<Type*> & tlist, 
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
           
            vector <short> fq;
            vector <short> tq;
            
            fq.push_back(j); //insert an id of fromTy
            tq.push_back(i); //insert an id of toTy
 
            if (isConversibleTo (llist.at(j), llist.at(i), 
                        tlist, llist, dlayout, fq, tq)) {

                inter.push_back((short)j);               
            }
        }
        downcasts.push_back(inter);
    }
}

static void 
createDownCastList (bool is_CPP_Modules,
                    vector<Type*> & tlist, 
                    vector<vector<short>> & safecasts,
                    vector<vector<short>> & downcasts,
                    vector <vector<short>> & llist,
                    const DataLayout * dlayout)
{
    // TODO: use function pointer?
    
    if (is_CPP_Modules) {
        createDownCastList_CPP (tlist, downcasts, llist, dlayout)
    }
    else {
        createDownCastList_C (tlist, safecasts, downcasts, llist, dlayout)
    }

    return; 
}

static void 
createTyOffsetList (bool is_CPP_Modules,
                    vector<Type*> & tlist,
                    vector<vector <short>> & safecasts,
                    vector <vector <short>> & flatrtoffsets,
                       // 1st elem: offset.
                       // 2st elem: a list of types in the offset. 
                    unsigned & MaxOffset,
                    const DataLayout * dlayout)
{
  /*
    for each type,
      for each offset,
        save only tid of the outermost type at the offset.
  */
  
  vector <vector<pair<unsigned, short>>> rtoffsets; //temporary offset table vector
  MaxOffset= 0;
  
  
  for (short i=0;i<tlist.size();i++) {
     
    vector <pair<unsigned, short>> onety;
        
    unsigned offset= 0;
       
    //tid per offset (distance) 
    pair <unsigned, short> tidPerDist= make_pair(offset, i);  
    onety.push_back(tidPerDist);    
   
    getSubTyOffsetsToTid(i, tlist, MaxOffset, //tidPerDist, //<<==== 
                    offset, onety, safecasts, dlayout);

    rtoffsets.push_back(onety);
  }

  //now creating a table to pass to the static lib.
  // (1) initial setting. create a vector set as -1. 
  //vector <vector <short>> flatrtoffsets;
   
  for (unsigned short i=0; i< rtoffsets.size(); i++) {
    vector <short> temponety;
    short temponetid= -1;
     
    for (unsigned j=0; j< MaxOffset+1; j++) {
        temponety.push_back(temponetid);      
    }
    flatrtoffsets.push_back(temponety);
  }

  // (2) for corresponding offset, set up the id. 

  for (unsigned short i=0; i< rtoffsets.size(); i++) {
    
    for (unsigned j=0; j< rtoffsets.at(i).size(); j++) {
      
      unsigned off= rtoffsets.at(i).at(j).first;
      short tid= rtoffsets.at(i).at(j).second;
    
      flatrtoffsets.at(i).at(off)= tid; 
    }
   }

  //errs()<<"MaxOffset: "<<MaxOffset<<"\n";
  //rtoffsets.clear(); // lets save some space..
     
}

static void
goDeeper (short tid,
          vector <short> & tidlist,
          vector<Type*> & tlist, 
          vector<vector<short>> & safecasts)
{
  if (getIdx(tidlist, tid)<0) {
    tidlist.push_back(tid); 
  }
  
  Type * subty=nullptr;
   
  if (isa<StructType>(tlist.at(tid))) {
    if (cast<StructType>(tlist.at(tid))->isOpaque() ||
        (cast<StructType>(tlist.at(tid))->getNumElements()) == 0 ) {
        return;
    }
    subty= cast<StructType>(tlist.at(tid))->getElementType(0);
  }
  else if (isa<ArrayType>(tlist.at(tid))){ 
    subty= cast<ArrayType>(tlist.at(tid))->getElementType();
  }
  else {
    return;
  }
  // get subtype's tid

  short subtid= getIdx(tlist, subty);

  if (subtid<0) {
      return;
  }
  goDeeper (subtid, tidlist, tlist, safecasts);    

}

static void
updateSafeCasts (is_CPP_Modules,
                 vector<Type*> & tlist, 
                 vector<vector<short>> & safecasts)
{

 for (short tid=0; tid<tlist.size(); tid++){
 
    vector <short> tidlist;

    goDeeper (tid, tidlist, tlist, safecasts); 

    // for each subtids, 
    for (int i=0; i<tidlist.size(); i++) {
     
      short subtid= tidlist.at(i);
       
      for (int j=0; j<safecasts.at(subtid).size(); j++) {
       
        short mysafetid= safecasts.at(subtid).at(j);

        if (getIdx(safecasts.at(tid), mysafetid) >= 0) continue;   
          
        (safecasts.at(tid)).push_back(mysafetid);

      }
    }

    std::sort(safecasts[tid].begin(), safecasts[tid].end());

 }
}

bool 
isCPPModule (Module & M)
{
    // Cpp: true, c: false
    if (M.source_filename().endswith("cpp") || (M.source_filename().endswith("cc")) {
        
        errs()<<"isCPPModule.Module Name: "<<M.source_filename()<<"\n";
        return true;
    }
    
    for (unsigned i=0; i< M.getIdentifiedStructTypes().size(); i++ ) { 
        if (M.getIdentifiedStructTypes()[i].startswith("class.std::")) {
            errs()<<"isCPPModule. has cpp type name 1: "<<M.getIdentifiedStructTypes()[i]<<"\n";
            return true;
        }
        if ((M.getIdentifiedStructTypes()[i].startswith("class.")){
            errs()<<"isCPPModule. has cpp type name 2: "<<M.getIdentifiedStructTypes()[i]<<"\n";
            return true;
        }
    }
    errs()<<"\n### Modules are in C ############\n";

    return false;
}

static void
createTypeTables (vector<Type*> & tlist, 
                  vector<vector<short>> & safecasts,
                  vector<vector<short>> & downcasts,
                  vector <vector<pair<short, vector<short>>>> & tyoffsets,
                  vector <vector <short>> & flatrtoffsets, //just one tid at one offset. 
                  unsigned & MaxOffset,
                  bool isCPP, // modules in C -> isCPP := false
                  Module & M)
{
    /* llist stores each type's fields' typeID list.
     e.g. an elem of llist: {int*, {char, char*}, float A[2]}
        == [typeID(int*), typeID(char), typeID(char*), 
            typeID(int), typeID(int)] */
    
    const DataLayout * dlayout= &M.getDataLayout(); 

    bool is_CPP_Modules= isCPPModule(M);

    vector <vector<short>> llist; // not used if is_CPP_Modules is TRUE.
   
    // ** create flattened type layout list. NO offsets. ** 
    createLayOutList (is_CPP_Modules, tlist, llist, M);
    
    errs()<<">> createLayOutList done\n";
     
    // ** Create valid upcasts **
    createSafeCastList(is_CPP_Modules, tlist, safecasts, llist, dlayout);
    
    errs()<<">> createSafeCastList done\n";
   
    // ** Create valid downcasts **
    createDownCastList (tlist, safecasts, 
                        downcasts, llist, dlayout);
    
    errs()<<">> createDownCastList done\n";
    
    // create flattened type layout list WITH offsets. ** 
    // the entry is in this form: {i64 tidoffset, safedesttids[maxtids]}
    
    createTyOffsetList(is_CPP_Modules, tlist, safecasts, tyoffsets, dlayout);
    
    errs()<<">> createTyOffsetList done\n";

    createTyOffsetList (is_CPP_Modules, tlist, safecasts, 
                        flatrtoffsets, MaxOffset, dlayout);
    
    errs()<<">> createTyOffsetList done\n";

    updateSafeCasts (is_CPP_Modules, tlist, safecasts);

 
    errs()<<"####################\ndown casts\n";
    for (unsigned i=0;i<tlist.size();i++) {
        errs()<<i<<": "<<*tlist.at(i)<<"--------\n";
        for (unsigned j=0;j<(downcasts.at(i)).size();j++){
            errs()<<"  "<<(downcasts.at(i)).at(j);  
        }
        errs()<<"\n";
    }
  errs()<<"####################\nSafe casts\n";
    for (unsigned i=0;i<tlist.size();i++) {
        errs()<<"TY_"<<i<<": "<<*tlist.at(i)<<"--------\n";
        for (unsigned j=0;j<(safecasts.at(i)).size();j++){
            errs()<<"  "<<(safecasts.at(i)).at(j);  
        }
        errs()<<"\n";
    }
   
   errs()<<"\n#### OFFSET TABLE ######\n";
    assert(tlist.size()==tyoffsets.size());
    for (unsigned i=0; i< tyoffsets.size(); i++) {
        errs()<<"TY_"<<*tlist.at(i)<<"------------\n";

        for (unsigned j=0; j< (tyoffsets.at(i)).size(); j++) { //for each offset type

            pair <unsigned short, vector<short>> pi= (tyoffsets.at(i)).at(j);

            errs()<<"  OFS_"<<pi.first<<"\n";

            for (unsigned k= 0; k< (pi.second).size(); k++) {
                errs()<<"    "<<*tlist.at((pi.second).at(k))<<"\n"; 
            }
        }
    }
    errs()<<"\n#### OFFSET TABLE ######\n";

    for (unsigned i=0; i< llist.size(); i++) {
        errs()<<"TY_"<<i<<"  "<<*tlist.at(i)<<"------------\n";

        for (unsigned j=0; j< (llist.at(i)).size(); j++) { //for each offset type

            errs()<<"  Elem_"<<j<<": "<<(llist.at(i)).at(j)<<"\n";
        }
    }
    
    errs()<<"\n#####################\n";
    
    exit(0);

}

static void
setUpSomeRTTypes (ArrayType* & SafeTidsTy, 
                  StructType* & oneOffsetTy,
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

  /*
    errs()<<"### maxoffsperty\t: "<<maxoffsperty<<"\n";
    errs()<<"### maxtysperoff\t: "<<maxtysperoff<<"\n";
    errs()<<"### tyoffsetssize\t: "<<tyoffsetssize<<"\n";
    errs()<<"### tblentrysize\t: "<<tblentrysize<<"\n";
    errs()<<"### MaxOffset\t: "<<MaxOffset<<"\n";
    errs()<<"### flatrtoffsetsize\t: "<<flatrtoffsetsize<<"\n";
  */
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

///
// type relation table
//
/*
static void 
createRTSafeCastsTable (vector<vector<short>> & safecasts,
                      GlobalVariable * & SafecastTable,
                      short & max_upcasts,  
                      Module & M) 
{
    errs()<<"max field count: "<<max_upcasts<<"\n";
    assert (max_upcasts!=0);

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
           
            dbg(errs()<<framertyid<<"  ";)
             
            Constant * fieldconst = 
                ConstantInt::get (IntegerType::get(M.getContext(), 16),      
                                  framertyid); 
            fields.push_back(fieldconst);
            assert(fields.size() <= max_upcasts && "upcast vector pushing wrong!\n");
        }
        
        dbg(errs()<<"\n";)
        
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
*/

static void 
createRTSafeCastsTable (vector<vector<short>> & safecasts,
                      GlobalVariable * & SafecastTable,
                      short & max_upcasts,  
                      Module & M) 
{
    errs()<<"$$######################\n";

    unsigned entrysize= safecasts.size()+1;
    
    ArrayType* tyIdArrayT=  
        ArrayType::get (IntegerType::getInt8Ty(M.getContext()), //elemty 
                        entrysize); //elem count
    
    errs()<<"tyIdArrayT: "<<*tyIdArrayT<<"\n";

    Constant * falseval = 
        ConstantInt::get (IntegerType::get(M.getContext(), 8), 0); 
                // assuming BOOL size 8 bits (1byte)    
    Constant * trueval = 
        ConstantInt::get (IntegerType::get(M.getContext(), 8), 1); 
                // assuming BOOL size 8 bits (1byte)    
    
    vector<Constant*> upcastvec;
     
    ///
    // create entries for types used in target program.
    /// 
    for (unsigned i=0; i< entrysize-1; i++) { // iterating only types in target program 
        
        vector<Constant*> onerow (entrysize, falseval) ;
      
        for(unsigned j=0 ; j< (safecasts.at(i)).size() ; j++) {  
            
            unsigned idx= (safecasts.at(i)).at(j);
            //replace the value (false) at idx of the onerow list.     
            onerow.at(idx)= trueval; 
        }
        onerow.at(entrysize-1)= trueval; // 
         
        Constant * onerowconst = ConstantArray::get(tyIdArrayT,onerow);
        
        upcastvec.push_back(onerowconst);
    }
    
    ///
    // add one entry a wild card type (its typeID becomes totalcount)
    // for a heap object that is tracked but not assigned its effective type.
    // (so final total account becomes total account + 1) 
    /// 
    vector<Constant*> onerow (entrysize, trueval);
    Constant * onerowconst = ConstantArray::get(tyIdArrayT,onerow);
    upcastvec.push_back(onerowconst);
  
    /// 
    // now create a global table.
    /// 
    ArrayType* SafecastsT= ArrayType::get(tyIdArrayT, upcastvec.size());
    Constant* safecastsTableArray = ConstantArray::get(SafecastsT, upcastvec);
    
    errs()<<"######################\nUpcast Table Array created\n";
     
    SafecastTable = new GlobalVariable (M, 
                                        SafecastsT, //StructTyArr, 
                                        true, 
                                        GlobalValue::ExternalLinkage,
                                        safecastsTableArray,//nullStructTbl,
                                        "FRAMER_Upcast_Table");
//    errs()<<*SafecastTable<<"\n";
}

static bool
isCertainTy (Type * ty, StringRef tyname)
{
    if (!isa<StructType>(ty)) return false;; //if not structype
    

    StructType * sty= cast<StructType>(ty);

    if (!sty->hasName())  return false;
    

    if (!sty->getName().startswith("paddedStruct")) return false;; 


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
collectLocalUnionsList (Function & f,
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

static bool 
isMallocPtr(Instruction * ins)
{
  if (!isa<StoreInst>(ins)) return false;

  StoreInst * si= cast<StoreInst>(ins);

  Value * siop= si->getValueOperand();
      
  if (!isa<BitCastInst>(siop)) return false;     
 
  BitCastInst * bci= cast<BitCastInst>(siop); 
  Value * bop= bci->getOperand(0);
 
  if (!isa<CallInst>(bop)) return false;
  
  CallInst * ci= cast<CallInst>(bop);
 
  // we cannot deal with indirect calls.. 
  if (!ci->getCalledFunction()) return false;

  Function * f= ci->getCalledFunction();
  
  if (f->getName().equals("malloc")
      || f->getName().equals("realloc")){
    
    return true;     
  }
  
  return false;;
         
}

static LoadInst *
getPtrHoldingMalloc (AllocaInst * ai)
{
  for (Value::user_iterator it= ai->user_begin();
        it!=ai->user_end();it++) {
    
    if (isa<LoadInst>(it)) {
      return cast<LoadInst>(&*it);      
    }
  }
  return nullptr; 
}
*/

static void 
handleHeapUnions (CallInst * ci, 
                vector<Value*> & heapunions)
{
 // errs()<<"\nCI: "<<*ci<<"\n";

  Function * f= ci->getCalledFunction();
  
  if (!f) return;
  
  if (!f->getName().equals("malloc")
      && !f->getName().equals("realloc")){
    return;     
  }
   
  for (Value::user_iterator it= ci->user_begin();
        it!=ci->user_end();it++) {
    
    if (!isa<BitCastInst>(*it)) continue;
    
    BitCastInst * bci= cast<BitCastInst>(*it);
    
    Type * dty= bci->getDestTy();
   
    PointerType * ut= dyn_cast<PointerType>(dty);
    assert(ut);

    if (!isUnionTy(ut->getElementType())) continue;    
    
    for (Value::user_iterator iit= bci->user_begin();
        iit!=bci->user_end();++iit) {
        
      if (!isa<StoreInst>(*iit)) continue;
      
      StoreInst * si= cast<StoreInst>(*iit);
      
       
      if (si->getValueOperand()!=bci) continue; 
     
      Value * sop= si->getPointerOperand();
      
      for (Value::user_iterator sit= sop->user_begin();
        sit!=sop->user_end(); ++sit) {
      
        if(isa<LoadInst>(*sit)) {
            
            //assert(isUnionTy(load's type));
          //  errs()<<"\nheap union--- \n";
          //  errs()<<"\tCI: "<<*ci<<"\n";
          //  errs()<<"\tptr(li): "<<**sit<<"\n";
            heapunions.push_back(*sit); 
            //return;     
        }
      }
    }
  } 
  
}

static void
insertLocalUnionsList (AllocaInst * ins,
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
/*  
  if (!isa<CallInst>(op)) return op;
  CallInst * ci= cast<CallInst>(op);
  Function * f= dyn_cast<Function>(ci->getCaller());
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
*/

  /* get an alloca inst */
  if (isa<CallInst>(op)) { 
    CallInst * ci= cast<CallInst>(op);
    Function * f= dyn_cast<Function>(ci->getCaller());
    
    if (f) { 
      StringRef fname= f->getName();
      if (fname.startswith("FRAMER_")){  
        if (fname.equals("FRAMER_forall_alloca") 
           // || fname.equals("FRAMER_forall_global_variable")
           ) {

          GEPOperator * gep= 
            dyn_cast<GEPOperator>(ci->getArgOperand(0)->stripPointerCasts());
          assert(gep);
          return gep->getPointerOperand();
        }
/* TODO. 
        // Alias analysis for heap to recognise unions? what do we do?
        else {
          errs()<<"what case: "<<*ci<<"\n";
          exit(0);
        }
*/
      }
    }
  }
  /* get an global variable */
  else if (isa<LoadInst>(op)) {
    
    LoadInst * li= cast<LoadInst>(op);
    Value * liop= li->getPointerOperand();
   // errs()<<"liop: "<<*liop<<"\n";
    
    if (isa<GlobalVariable>(liop)) {
     
      GlobalVariable * gv= cast<GlobalVariable>(liop); 
      Value * ini= gv->getInitializer();
      
      if (isa<GEPOperator>(ini)) {
        GEPOperator * gep= cast<GEPOperator>(ini);
        Value * gop= gep->getPointerOperand();
   //     errs()<<"gop: "<<*gop<<"\n";
        return gop;
      }
    }
  }
  return op;  
}

static Type *
extractAllocatedTypeFromPaddedStruct(Type * ty)
{

  StructType * sty= dyn_cast<StructType>(ty);
  
  assert(sty && "ty is assumed that {header,allocatedTy} here.");    

  return sty->getElementType(1);
      
}

static StructType * 
isAliasWithUnionObj(Value * op_arg, //store/load's ptrop
                    AAResults & AA,
                    vector <AllocaInst*> & ais, //union typed
                    vector <GlobalVariable*> & gvs, //union typed
                    vector <Value*> & heapunions,
                    Module & M)
{
  const DataLayout & DL = M.getDataLayout();
   
  if (ais.empty() && gvs.empty()) {
    return nullptr;
  }
  
  //const MemoryLocation loadloc= MemoryLocation::get(li);    
  //const Value *AccessPtr = getUnderlyingObject(loadloc, DL);
  
  //errs()<<"Mem access op: "<<*op_arg->stripPointerCasts()<<"\n";
  
  Value * val= getAlloca (op_arg); 
  
  //errs()<<"my alloc: "<<*val<<"\n";
  
  const Value *AccessPtr = llvm::getUnderlyingObject(val);
  //errs()<<"AccessPtr: "<<*AccessPtr<<"\n";
   
  /* for union-typed allocas, check alias */
  
  for (unsigned i=0; i<ais.size(); i++) {
      Instruction * ins= ais.at(i);
      
     // errs()<<i+1<<"/"<<ais.size()<<" ... ais: "<<*ins<<"\n";
       
      if (AccessPtr == ins || AA.isMustAlias(ins, AccessPtr)) { 
          
        Type * t= cast<PointerType>(ins->getType())->getElementType(); 
        return dyn_cast<StructType>(extractAllocatedTypeFromPaddedStruct(t));
      }
  }
  /* for union-typed gvs, check alias */
  for (unsigned i=0; i<gvs.size(); i++) {
      
      //if (AA.alias(op_arg, gvs.at(i))) { //
      //errs()<<i+1<<"/"<<gvs.size()<<" ... gv: "<<*gvs.at(i)<<"\n";
      
      if (AA.isMustAlias(gvs.at(i), AccessPtr)) { 
          Type * t= cast<PointerType>(val->getType())->getElementType(); 
          return dyn_cast<StructType>(extractAllocatedTypeFromPaddedStruct(t));
      }
  }
  
  /* for union-typed heap objects, check alias */

  for (unsigned i=0; i<heapunions.size(); i++) {
      
    //  errs()<<i+1<<"/"<<heapunions.size()<<" ... heap: "<<*heapunions.at(i)<<"\n";
      
      if (AA.isMustAlias(heapunions.at(i), AccessPtr)) { 
          Type * t= cast<PointerType>(val->getType())->getElementType(); 
          errs()<<"got heap alias!";
          return dyn_cast<StructType>(t);
      }
  }

  return nullptr;

}

static bool
justToBeUntagged (Value * op,
                  AAResults & AA,
                  vector <AllocaInst*> & ais, //union typed
                  vector <GlobalVariable*> & GVUnions, //union typed
                  vector <Value*> & heapunions,
                  vector<Type*> & tlist,
                  vector<vector<short>> & safecasts, 
                  Module & M)
{ 
  StructType * unionty= isAliasWithUnionObj(op, 
                AA, ais, GVUnions, heapunions, M); 
  Type * dstTy= cast<PointerType>(op->getType())->getElementType(); 
  
  // (1) if unionty. then check bounds, and return.
  if (unionty) {
    bool status= isSafelyCastedTo(unionty, dstTy, tlist, safecasts); 
    assert(status);
    //errs()<<"\tUnion safe cast!\n";
    return status;
  }
  
  
  // (2) now non union-typed pointer, but type cast from/to union.  
   
  BitCastOperator * bitcastop= dyn_cast<BitCastOperator>(op); 

  /// if an operand is not pointer cast, just untag a pointer. 
  if (!bitcastop) {
    //errs()<<"\tnot bitcast\n";
    return true;  
  }
  
  assert(isa<PointerType>(bitcastop->getDestTy()) && 
         isa<PointerType>(bitcastop->getSrcTy())); 
 
  /// get a pointer's element type.
  Type * srcTy= cast<PointerType>(bitcastop->getSrcTy())->getElementType();   

  /// if none of types (src, dst) is union typed, just untag 
  if (!isUnionTy(srcTy) && !isUnionTy(dstTy)) {
    return true; 
  }
  /// now one of them are union. 
  /// if it's pointer cast with unions, and it's equal/upcast, then untag  
  if (isSafelyCastedTo(srcTy, dstTy, tlist, safecasts)) {
    return true;
  }
  
  assert(getAlgnVal(srcTy, &M.getDataLayout()) >= getAlgnVal(dstTy, &M.getDataLayout()));

  return false;
}

/*
static GEPOperator *
getGEPFromCheckCallInst(CallInst * CI) 
{
    Value * gep= CI->getOperand(0);
    return dyn_cast<GEPOperator>(gep->stripPointerCasts());     
}
*/

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
    
    //assert (isa<CompositeType>(cast<PointerType>(obj->getType())->getElementType()) 
    //        && "ELT not compositetype\n");
    //Type * upT= cast<CompositeType>(cast<PointerType>(obj->getType())->getElementType());; 
    Type * upT= cast<PointerType>(obj->getType())->getElementType();; 



/////////////
// i=1.
    unsigned offset=0;

    for (unsigned i=1;i<gep->getNumIndices();i++){
        ConstantInt *CINT= cast<ConstantInt>(gep->getOperand(i+1));
        uint64_t idx = CINT->getZExtValue();
/////////////
        
        // below: SequentialType is gone from llvm 12.0. T_T
        //if (SequentialType * SEQT=dyn_cast<SequentialType>(upT)){ /
         
         if (upT->isArrayTy () || upT->isVectorTy()){ 
            
            Type * SEQElemT= nullptr;
            
            if (upT->isArrayTy ()) {
              SEQElemT= cast<ArrayType>(upT)->getElementType();
            }
            else {
              SEQElemT= cast<VectorType>(upT)->getElementType();
            }
            uint64_t elemsize= (dlayout->getTypeSizeInBits(SEQElemT))/8;
            
            //assert (SEQT->getNumElements()<=idx && "out of bound\n"); // check overflow 
            //uint64_t elemsize= (dlayout->getTypeSizeInBits(SEQT->getElementType()))/8;
            //upT= SEQT->getElementType(); 
            offset=offset+ (idx*elemsize);
            upT= SEQElemT; 
        }
        
        else if (StructType * SUBCT= dyn_cast<StructType>(upT)){
            const StructLayout * SL= dlayout->getStructLayout(SUBCT);
            offset=offset+SL->getElementOffset(idx); //update offset
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
        Value * CV= CI->getCaller();
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
        Value * CV= CI->getCaller();
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

/*
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
*/

static unsigned 
FramerGetBitwidth (Type * allocatedType, const DataLayout * dlayout)
/* #Bits of element type. (e.g. int->32, struct->sum of member bits, 
    array->#bits of array element. (outmost element, if the array is array of array...)*/
{
    unsigned allocatedTyID = allocatedType->getTypeID();
     
    //if (( allocatedTyID > Type::VoidTyID && allocatedTyID <= Type::PPC_FP128TyID) ){
    //    return allocatedType->getPrimitiveSizeInBits(); 
    //}
    
    if (IntegerType * intTy = dyn_cast<IntegerType>(allocatedType)) {
        return intTy->getBitWidth();
    }
    else if (StructType * structTy = dyn_cast<StructType>(allocatedType)) {
        return (unsigned) getBitwidthOfStruct (structTy, dlayout);
    }
    else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
       return (unsigned)(arrayTy->getNumElements())*FramerGetBitwidth(arrayTy->getElementType(), dlayout); 
        }
    else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {
        //if (vecty->getBitWidth()!=0) {
        //    return vecty->getBitWidth();
        //}
        //else {
        return (unsigned)(vecty->getNumElements())*FramerGetBitwidth(vecty->getElementType(), dlayout); 
         //}
    }
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else {
        assert(!allocatedType->isVoidTy()); // what should I do for this?
        return allocatedType->getPrimitiveSizeInBits();
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

/*
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
*/

// find a llvm.lifetime.start, get a alloca hook.
// then move alloca hook and its operand instructions AFTER start func. 
/*
static void
setupScopeOfLocals(Function & F, Module & M)
{
  vector<Instruction*> toBeRemoved;
  
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
*/


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

/*
static bool 
isNonTagged (Instruction * ins, AAResults & AA, Module & M) 
{
  Value * op_ = ins->getOperand(0);
  
  const DataLayout & DL = M.getDataLayout();
  Function * F= ins->getFunction();
   
  const Value *AccessPtr = llvm::getUnderlyingObject(op_);
  
  for (Function::iterator fi= F->begin(); fi!=F->end(); ++fi) {
    for (BasicBlock::iterator it= (&*fi)->begin(); it!=(&*fi)->end(); it++) {
        
        if (!isa<AllocaInst>(&*it)) continue;
       
        AllocaInst * ai= cast<AllocaInst>(&*it); 
        Type * aty= ai->getAllocatedType();
        
        if (aty->isArrayTy()) continue; 

        else if (aty->isStructTy()) {

          StructType * sty= cast<StructType>(aty);

          if (!sty->hasName()) continue;

          if (sty->getName().startswith("paddedStruct")) continue; 
              
          if (AA.isMustAlias(ai, AccessPtr)) {
              return true;    
          }
        }
        else {
          if (AA.isMustAlias(ai, AccessPtr)) {
              return true;    
          }
        }
    }
        
      
  }
  for (Module::global_iterator gi= M.global_begin(); 
            gi !=M.global_end(); ++gi) {

     GlobalVariable * gv= &*gi;
     Type * aty= cast<PointerType>(gv->getType())->getElementType();
 
     if (aty->isArrayTy()) continue; 

     else if (aty->isStructTy()) {

         StructType * sty= cast<StructType>(aty);

         if (!sty->hasName()) continue;

         if (sty->getName().startswith("paddedStruct")) continue; 

         if (AA.isMustAlias(gv, AccessPtr)) {
             return true;    
         }
     }
     else {
         if (AA.isMustAlias(gv, AccessPtr)) {
             return true;    
         }
     }

  }
  
  return false;
  
  //Value * val= getAlloca (op_arg); 
}
*/


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
                GlobalVariable* origGV, 
                vector <Constant*> & oplist,
                Instruction * init, 
                vector<Instruction*> & insToBeInserted,
                set<Instruction*> & FramerLoads)
{      
    //errs()<<"constuse: "<<*constuse<<"\n";
    
    // use: bitcast (oldgv to ty) 
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
        //    errs()<<"itex: "<<*itex<<"\n";
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
    
    if (constuse==origGV) {
        //assert(isa<GlobalVariable>(&*use) && "Use is not GV!\n");
        assert(isa<GlobalVariable>(constuse) && "Use is not GV!\n");
        return init;
        //return newGV; //DO SOMETHING. 
    }
    //if (isa<ConstantExpr>(&*use)||isa<ConstantAggregate>(&*use)) {
    else if (isa<ConstantExpr>(constuse)) {
         
        vector <Constant*> oplist;
        
        oplist.push_back(cast<Constant>(constuse)); 
        //return getNewInsForGV(use, newGV, origGV, //test1 
        return getNewInsForGV(constuse, newGV, origGV, //test1 
                        oplist, init, insToBeInserted, FramerLoads); 
      // use: bitcast (oldgv to ty) 
    }
    else if (isa<ConstantAggregate>(constuse)) {
        for (unsigned i=0;i<constuse->getNumOperands();i++) {
            if (constuse->getOperand(i)==origGV) {
                //constuse->setOperand(i,newGV);    
                constuse->handleOperandChange(constuse->getOperand(i), newGV);
            }
        }
        //errs()<<"new constuse: "<<*constuse<<"\n";
        return constuse;
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

            PointerType * gvtag_ptrty= dyn_cast<PointerType>(gvTag->getType());
            assert(gvtag_ptrty);

            LoadInst * li= new LoadInst(gvtag_ptrty->getElementType(), 
                                        gvTag, "loadGVTag", IU);

            assert(li->getType() == gvtag_ptrty->getElementType());            

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


static void 
pushtoarglist (Instruction * insertBeforeMe,  
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


