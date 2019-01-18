
#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm/Transforms/FramerLoopOpt/CheckInfo.h"
#include "llvm/Transforms/FramerLoopOpt/Utility.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "../../../../../llvm-4.0.0.src/lib/IR/ConstantsContext.h"

#define NOTSAFESTATICALLY   0 //requiring runtime check
#define SAFESTATICALLY      1
#define COMPAREIDXATRUNTIME 2
#define OUTOFBOUNDATRUNTIME 3 //should not be called at runtime.



using namespace llvm;
using namespace std;

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
        errs()<<"FRAMER ERROR. offset+sizeToAccess > totalsize\n";
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

    uint64_t offset= 0;
    for (unsigned i=0;i<gep->getNumIndices();i++){
        assert(isa<ConstantInt>(gep->getOperand(i+1)) 
                && "gep idx is not constantint. do something?. getValueDom?\n");
        ConstantInt *CINT= cast<ConstantInt>(gep->getOperand(i+1));
        uint64_t idx = CINT->getZExtValue();
        if (i==0) continue;
        
        if (SequentialType * SEQT=dyn_cast<SequentialType>(upT)){
            //assert (SEQT->getNumElements()>=idx && "out of bound\n"); // check overflow 
            uint64_t elemsize= dlayout->getTypeSizeInBits(SEQT->getElementType())/8;
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

static CallInst* __isHookedAllocaOrGV(Value * p, Module & M,GEPOperator * gep) //only for delHooksPass :( 
{
    //alloca
    if (isa<CallInst>(p->stripPointerCasts())) { 
        CallInst * CI= cast<CallInst>(p->stripPointerCasts());
        Value * CV= CI->getCalledValue();
        if (isa<Function>(CV)) {
            Function * F= cast<Function>(CV);
            if (F->getName().startswith("FRAMER_forall_alloca")) { //for alloca
                //Value * myalloc= dyn_cast<GEPOperator>(CI->getOperand(0)->stripPointerCasts()); 
                //assert(isa<AllocaInst>(CI->getOperand(0)->stripPointerCasts()) && "not alloca\n");  
                //return myalloc;
                return CI; 
            }  
        }
    }
    // GV
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

static unsigned 
FramerGetBitwidth (Type * allocatedType, const DataLayout * dlayout, bool isOutMost=true)
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
            if (isOutMost) {
                return FramerGetBitwidth(arrayTy->getElementType(), dlayout, false);
            }
            else {
                return (unsigned)(arrayTy->getNumElements())*FramerGetBitwidth(arrayTy->getElementType(), dlayout, false); 
            }
        }
        else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {
            if (vecty->getBitWidth()!=0) {
                return vecty->getBitWidth();
            }
            else {
                return (unsigned)(vecty->getNumElements())*FramerGetBitwidth(vecty->getElementType(), dlayout, false); 
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

static unsigned 
getTotalSize(GEPOperator * gep, const DataLayout * dlayout)
{
//debug.s
    Value * obj= gep->getPointerOperand();

    if(!isa<CompositeType>(cast<PointerType>((obj->stripPointerCasts())->getType())->getElementType())) {
        if (isa<GetElementPtrInst>(gep))
            errs()<<"function- "<<(cast<GetElementPtrInst>(gep)->getFunction())->getName()<<"\n";
        errs()<<"gep: "<<*gep<<"\n";
        errs()<<"obj: "<<*obj<<", and uncast: "<<*obj->stripPointerCasts()<<"\n";    
        errs()<<"obj type: "<<*obj->getType()<<"\n";    
    }
//debug.e    

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
__isSafeAccess(GEPOperator * gep, Module & M, bool isMemAccess) 
{
        CallInst * hook= __isHookedAllocaOrGV(gep->getPointerOperand(), M, gep); 
        if (hook==nullptr) {
            return 0; 
        }
        if (gep->hasAllZeroIndices()) { // base addr of alloca/gv
            return 1; 
        }
        if (!isa<ConstantInt>(gep->getOperand(1)->stripPointerCasts())){
            return 0; // issafeaccess==0. 
        }
        if (!((cast<ConstantInt>(gep->getOperand(1)->stripPointerCasts()))->equalsInt(0))) {
            return 0; 
        }
        if (!gep->hasAllConstantIndices()) {
            if (gep->getNumIndices()<=2) {
                return 2; // issafeaccess==2. requiring runtime check 
            } 
            else {
                return 0;
            } 
        }
        // offset= base~ptr (two args. 2nd is gep's ptr.assignment)
        unsigned offset= getStaticOffset(gep, &M.getDataLayout()); 
        //unsigned totalsize= getTotalSize(gep, &M.getDataLayout()); 
        unsigned totalsize= getmysize(hook); 
        unsigned sizeToAccess= FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), &M.getDataLayout())/8;
        
     //debug.s 
/*        if(offset+sizeToAccess>totalsize && isMemAccess) {
            if(isa<GetElementPtrInst>(gep)) {
                errs()<<"-- func: "<<cast<GetElementPtrInst>(gep)->getFunction()->getName()<<", BB name: "<<*cast<GetElementPtrInst>(gep)->getParent()<<"\n";
            }
            errs()<<">>>gep: "<<*gep<<"\n";
            errs()<<"op ptr: "<<*gep->getPointerOperand()<<"\n";
            errs()<<"op uncast: "<<*gep->getPointerOperand()->stripPointerCasts()<<"\n";
            errs()<<"offset: "<<offset<<", sizetoaccess: "<<sizeToAccess<<", totalsize: "<<totalsize<<"\n";
            
            if (CallInst * cii= dyn_cast<CallInst>(gep->getPointerOperand()->stripPointerCasts())) {
               Value * opnd= cii->getArgOperand(0)->stripPointerCasts();
               errs()<<"ALLOCA/GV: "<<*opnd<<"\n";   
            }
        } */
     //debug.e 
        
        return isStaticInBound(offset, 
                        sizeToAccess,
                        totalsize,
                        isMemAccess); 
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


