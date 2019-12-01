
#include "llvm/Support/raw_ostream.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/TypeFinder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/Instruction.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/Support/DynamicLibrary.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/IR/Argument.h"
#include <map>
#include "llvm-c/Core.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Use.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/Instruction.def"
#include "llvm/IR/InstrTypes.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Transforms/Utils/CtorUtils.h"
#include "../../../../llvm-4.0.0.src/lib/IR/ConstantsContext.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h" 
#include "llvm/Support/CommandLine.h"
#include "llvm/PassRegistry.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include "llvm/IR/LegacyPassManager.h"

//#include "llvm/IR/Intrinsics*.td"
//#include "llvm/include/llvm/IR/Intrinsics*.td"

#define DEBUG_TYPE "MemfisPass"

#define initVec ConstantInt::get(Type::getInt64Ty(M.getContext()),(1ULL<<63))
#define MacroEqualTo(...) \
        ConstantExpr::getICmp(\
            CmpInst::ICMP_EQ,\
            ConstantExpr::getAnd(ConstantExpr::getShl(xorResult, ConstantInt::get(Type::getInt64Ty(M.getContext()), __VA_ARGS__)),initVec),\
            initVec)  

#define constCLZ(...)\
        ConstantInt::get(Type::getInt64Ty(M.getContext()),__VA_ARGS__)

using namespace llvm;
using namespace std;

STATISTIC (memfispasscounter, "MemfisPass");


enum CalledFuncEnum {
    MallocIsCalled,
    FreeIsCalled,
    LLVMMemTransferIsCalled, // containing both memcpy and memmove.
    LLVMMemSetIsCalled,
    ExternalFuncIsCall
    
    //LLVMMemCpyIsCalled,
    //LLVMMemMoveIsCalled,
    //LLVMMemCpySRCIsCalled,
    //LLVMMemCpyDESTIsCalled,
    //LLVMMemMoveSRCIsCalled,
    //LLVMMemMoveDESTIsCalled,
};
const DataLayout * dlayout;

const int CalledFuncEnum_count = ExternalFuncIsCall-MallocIsCalled+1;
Function *      Func_main;
Instruction*    initHookCall;
Instruction *   fstInstOfMainFunction; 
BasicBlock *    fstBBOfMainFunction;
BasicBlock *    initBBOfMain;
BasicBlock *    GVsBBOfMain;

const char * prefix_of_hookGV_name = "FRAMER_";
const char * prefix_of_hookfunc_name = "FRAMER_forall_";
const char * prefix_of_supplementary_funcName = "FRAMER_supplementary_";

bool HookDefinitionExists [100]={0};
bool HookDefForCalledFuncExists [CalledFuncEnum_count]={0};

vector <StructType*> allStructTyList;

StructType*     HeaderTy;
IntegerType*    OffByOneTy;


GlobalVariable * basicTypeTable; 
GlobalVariable* StructTyTable; /* StructTyTable in Arraytype */ 
GlobalVariable* startStructTypeTable; 

const unsigned llvmbasicTyCount= 17;
const unsigned extrabasicTyCount=5;
const unsigned FramerBasicTyCount= llvmbasicTyCount+extrabasicTyCount; 
unsigned structTyCount;
uint64_t headerTySize;  
unsigned headerTyAlign;

const uintptr_t FRAMER_log_slotsize= 15;
bool PointersAreTagged = false;

namespace
{
     struct MyPrintPass : public ModulePass {
        public:
        char static ID;
        MyPrintPass() : ModulePass(ID) {};
    /*    
        virtual void getAnalysisUsage(AnalysisUsage &AU) const {
            //AU.setPreservesCFG();
            AU.addRequired<PostDominatorTreeWrapperPass>();
        }
    https://stackoverflow.com/questions/24174285/minimal-code-for-dynamically-loaded-analysis-pass-and-analysis-group-in-llvm 
    */
        virtual bool    runOnModule(Module &M);
        //virtual bool    runOnFunction (Function &F, Module &M, PostDominatorTree & postDT);
        virtual bool    runOnFunction (Function &F, 
                                        Module &M); 
        /*bool            runOnBasicBlock (BasicBlock &BB, 
                                        Module &M, 
                                        PostDominatorTree & postDT); */
        bool            runOnBasicBlock (BasicBlock &BB, 
                                        Module &M); 

        protected:
            Instruction * getNextInst (Instruction * Inst);
            GlobalVariable * getNextGV (GlobalVariable * GV, Module &M); 

            bool isTaggedPointer        (Value* accessedPtr); 
            bool isHookFamilyFunction   (Function * F); 

            void insertCastInstForArg   (Instruction * insertBeforeMe, 
                                        vector<Value*> & arglist);
            void pushtoarglist (Instruction * insertAfterMe, 
                                Type * paramTy, 
                                Value * argtobepushed, 
                                vector<Value*> & arglist);

            void pushArgForBitCastInst (FunctionType *FTy, 
                                       BitCastInst * BCI, 
                                       vector<Value*> & arglist);
            void pushArgForFPToSIInst  (FunctionType * FTy, 
                                       FPToSIInst * FTS, 
                                       vector<Value*> & arglist); 
            
            Value * castingArgToParam (Instruction * I, 
                                      Type * paramType, 
                                      Value * arg);

            void getArgumentsForGV (FunctionType * FTy, 
                                    GlobalVariable * GV, 
                                    vector<Value*> & arglist, 
                                    Instruction * insertBeforeMe);
           
            void doInitFuncHook     (Module &M);
            void doExitingMain      (Module &M);
            bool isLeafOfDomTree    (BasicBlock* bb, PostDominatorTree & postDT); 
            void insertEpilogueOfFunc (Instruction* tagged, Module &M);//, PostDominatorTree & postDT);  
            void doInitialSetup     (Module &M);
            
            void create1stBBOfMain          (Module &M); 
            void flagHooksDefinitionExists  (Module &M);
            void assertBasicTyTable         (Module &M);
            void runOnGlobalVariables       (Module &M);       
            void padObject                  (Value* obj, Module &M);
            unsigned getFramerTypeID        (Type* ty);
            unsigned getUserIntegerTypeID   (IntegerType* ty);
            Constant* constructAddressValue (Module &M, GlobalVariable* tab, unsigned subindex);
            Constant* getFramerTyEntryAddress(Module &M, unsigned ftid);
            int  getUserStructTypeID        (StructType* ty);
            void createStructTypeTable      (Module &M); 
            void createUserStructTyList     (Module &M);
            unsigned  getMaxFieldCountOfStruct   ();
            bool isFramerIntID              (unsigned id);
            bool isFramerStructID           (unsigned id);
            Value* tagFramerTyID            (Value * val, 
                                            unsigned id, 
                                            Module &M); 
           
            bool hasConstructorAttribute (GlobalVariable * GV);
            bool hasDestructorAttribute  (GlobalVariable * GV);
            bool isPrintfStr             (GlobalVariable * GV);
            
            Constant* tagConstantPtr (Constant* ptr, 
                                      Constant* tag, 
                                      Constant* flag, 
                                      Module & M); 
            Constant* getPaddedEndInt       (GlobalVariable* paddedGV,
                                            Module & M); 
            Constant* getLogFrameSize       (Constant* base, 
                                            Constant* end,
                                            Module & M); 
            Constant* getOffset            (Constant* base, 
                                            Module & M); 
            Constant* getTaggedConstantPtr (GlobalVariable* basePadded,
                                            Constant* origPtr,
                                            Module & M); 
            Constant* createHeaderInitializer (GlobalVariable* GV,
                                               unsigned Tid,
                                               unsigned gvsize);

            GlobalVariable* doGlobalVariable (GlobalVariable * GV, 
                                            Function * F, 
                                            Instruction * insertBeforeMe, 
                                            Module & M);
            Value * getEndAddressGV (GlobalVariable * GV, 
                                    uint64_t numElems, 
                                    unsigned numBitsOfElemTy, 
                                    Type * typeToConvertTo, 
                                    Instruction * insertBeforeMe, 
                                    Module & M);
            uint64_t getArraySizeforGV (Type * allocatedObjTy);

            void insertFunctionCallforGV(GlobalVariable * GV, 
                                        Function * F, 
                                        Instruction * insertBeforeMe);
            void insertFunctionCall (Function * F, 
                                     Instruction * insertBeforeMe, 
                                     vector<Value*> & arglist );
            CallInst *  insertHookAndReturn (Function * F, 
                                            Instruction * insertBeforeMe, 
                                            vector<Value*> & arglist); 
            
            Instruction* castAndreplaceAllUsesWith (Value * originalPtr, 
                                                    Value * modifiedPtr); 
            void insertCastToRestoreType    (Instruction* insertAfterMe,
                                            vector<Value*> & castinglist);
            Value * getArraySize            (AllocaInst * AI, 
                                            Type * funcParamTy);
            Type *  getTypeOfElemOfArray    (Type * allocatedType);
            Value * getPrimitiveEndAddress  (AllocaInst * baseAddr, 
                                            Instruction * insertBeforeMe, 
                                            Module & M);
            Value * getArrayEndAddress      (Value * baseAddr, 
                                            unsigned numBitsOfElemTy, 
                                            Value * numArrayElements, 
                                            Type * typeToConvertTo, 
                                            Instruction * insertBeforeMe, 
                                            Module & M );
            Value * getEndAddrforMalloc     (Value * baseAddr, 
                                            Value * numBytes, 
                                            Type * typeToConvertTo, 
                                            Instruction * insertBeforeMe, 
                                            Module & M);
            
            Value * createConstantIntInstance   (unsigned valueToBeInstantiated, 
                                                Type * whatTypeItShouldBe);
            Value * constructValueFromFunc      (unsigned valueToBeInstantiated, 
                                                Function * F, 
                                                unsigned paramIndex);

            unsigned getBitwidth    (Type * allocatedType, bool isOutMost=true);
            unsigned getPrimTyBits  (unsigned Typeid);
            uint64_t getBitwidthOfStruct ( StructType * STy );
           
            size_t getNewAlignment (size_t totalsize);
            size_t pow2roundup (size_t x);

            /* process memory access instruction */
            Instruction* doAllocaInst           (AllocaInst * AI, 
                                                Instruction * successorInst, 
                                                Module & M);
                                                //PostDominatorTree & postDT);
            Instruction* doPrimitiveAllocaInst  (AllocaInst * AI, 
                                                Instruction * successorInst, 
                                                Module & M);
                                                //PostDominatorTree & postDT);
            Instruction* doArrayAllocaInst      (AllocaInst * AI, 
                                                Instruction * successorInst, 
                                                bool arraykind, 
                                                Module & M);
                                                //PostDominatorTree & postDT);
            void doLoadInst             (LoadInst * LI, Instruction * successorInst, Module & M);
            void doStoreInst            (StoreInst * SI, Instruction * successorInst, Module &M);
            void doGetElementPtrInst    (GetElementPtrInst * GEP, Instruction * successorInst, Module &M);

            /* process Call Instruction */
            Instruction* doCallInst     (CallInst * CI, Instruction * successorInst, Module &M);
            Instruction* doCallInstMalloc(CallInst * CI, Instruction * successorInst, Module & M);
            Instruction* doCallInstFree (CallInst * CI, Instruction * successorInst, Module & M);
            
            void doCallLLVMMemTransfer  (MemTransferInst * MI, Instruction * successorInst, Module &M);            
            void doCallLLVMMemSet       (MemSetInst * MMI, Instruction * successorInst, Module &M);            
            void doCallExternalFunc     (CallInst * CI, Instruction * successorInst, Module &M);
            
            /*void doCallLLVMMemCpySRC    (MemCpyInst * MCI, Instruction * successorInst, Module &M);            
            void doCallLLVMMemCpyDEST   (MemCpyInst * MCI, Instruction * successorInst, Module &M);            
            void doCallLLVMMemMoveSRC   (MemMoveInst * MMI, Instruction * successorInst, Module &M);            
            void doCallLLVMMemMoveDEST  (MemMoveInst * MMI, Instruction * successorInst, Module &M);*/            
 
            /* process Cast Instruction */
            void doBitCastInst  (BitCastInst * BCI, Instruction * successorInst, Module &M);
            void doSIToFPInst   (SIToFPInst * STF, Instruction * successorInst, Module &M);
            void doPtrToIntInst (PtrToIntInst * PTI, Instruction * successorInst, Module &M);
            void doIntToPtrInst (IntToPtrInst * IPI, Instruction * successorInst, Module &M);
            void doFPToSIInst   (FPToSIInst * FTS, Instruction * successorInst, Module &M);
            void doTruncInst    (TruncInst * TR, Instruction * successorInst, Module &M);
            void doSExtInst     (SExtInst * SI, Instruction * successorInst, Module &M);
            void doZExtInst     (ZExtInst * ZI, Instruction * successorInst, Module &M);
            void doFPExt        (FPExtInst * FEI, Instruction * successoInst, Module & M);
            void doAddrSpaceCastInst (AddrSpaceCastInst * I, Instruction * successorInst, Module & M);

            /* do Possibly Exact operator */
            void doPossiblyExactOp  (PossiblyExactOperator * PEO, Instruction * successorInst, Module & M);
            void doUDivOp           (UDivOperator * UDO, Instruction * successorInst, Module & M);
            void doSDivOp           (SDivOperator * SDO, Instruction * successorInst, Module & M);
            void doLShrOp           (LShrOperator * UDO, Instruction * successorInst, Module & M);
            void doAShrOp           (AShrOperator * OP, Instruction * successorInst, Module &M);
          
            /* do OverFlow Binary Operator */ 
            void doOverflowBinaryOp (OverflowingBinaryOperator * OFO, Instruction * successorInst, Module & M);
            void doSubOp    (SubOperator * SO, Instruction * successorInst, Module &M);
            void doMulOp    (MulOperator * MO, Instruction * successorInst, Module &M);
            void doAddOp    (AddOperator * AO, Instruction * successorInst, Module &M);
           
            bool isItsUser (Value * useuser, User * useruser);
            Value * getOriginalAlloca (Value* ptr); 
            bool isToBeTaggedType (Type* t);

            void restoreModifiedPtr (LoadInst * LI); 
            void castAndreplaceUsesOfWithBeforeInst (Instruction * user, Value * from, Value * toThis);
            Type* getResultTypeOfMalloc (CallInst * CI);
            /*void getAnalysisUsage(AnalysisUsage &AU) const override {                                                                        
                AU.setPreservesCFG();
                AU.addPreserved<CallGraphWrapperPass>();
            }*/
    };
}

char MyPrintPass::ID = 0;
static RegisterPass<MyPrintPass> X ("MemfisPass", "Memfis Pass", false, false);

//INITIALIZE_PASS (MyPrintPass,  "MemfisPass", "Memfis Pass", false, false);

//namespace llvm {
//    ModulePass *createMyPrintPassPass() {return new MyPrintPass();}
//}

//ModulePass *llvm::createMyPrintPassPass() { return new MyPrintPass(); }
//static RegisterAnalysisGroup<PostDominatorTreeWrapperPass> Y(X);

GlobalVariable* MyPrintPass::getNextGV (GlobalVariable * GV, Module &M)
{
    Module::global_iterator I (GV);
    I++;
    
    if (I == M.global_end()) {
        errs()<<"Next is the last GV!\n";
        return nullptr;
    }
    return &*I;
}

Instruction * MyPrintPass::getNextInst (Instruction * Instr)
{
    BasicBlock::iterator I (Instr);
    I++;
    
    if (I == Instr->getParent()->end()) {
        errs()<<"Next is the last inst of BB!\n";
        return nullptr;
    }
    return &*I;
}

Value * MyPrintPass::createConstantIntInstance (unsigned valueToBeInstantiated, Type * whatTypeItShouldBe)
{
    return ConstantInt::get(whatTypeItShouldBe, valueToBeInstantiated); 
}

Value * MyPrintPass::constructValueFromFunc (unsigned valueToBeInstantiated, 
                                            Function * F, 
                                            unsigned paramIndex)
{
    return ConstantInt::get(F->getFunctionType()->getParamType(paramIndex), 
                            valueToBeInstantiated); 
}

Value * MyPrintPass::getArraySize (AllocaInst * AI, Type * funcParamTy) 
{
    if (AI->isArrayAllocation() || AI->getArraySize() != ConstantInt::get(AI->getArraySize()->getType(), 1)) {
        return AI->getArraySize();
    }
    else if (AI->getAllocatedType()->isArrayTy()){
        //|| AI->isArrayAllocation() ) { // TODO: Why this not working???
        Value * size = ConstantInt::get
                        (funcParamTy, 
                        cast<ArrayType>(AI->getAllocatedType())->getNumElements());
        return size; //uint64_6 type..
    }
    else {
        errs()<<"how come it enteres here?\n";
        exit(0);
    }
}

Type * MyPrintPass::getTypeOfElemOfArray (Type * allocatedType)
{
    if  (ArrayType *  MyArrayTy = dyn_cast<ArrayType>(allocatedType)) { 
        return MyArrayTy->getElementType();
    }
    else {
        return allocatedType;
    }
}

void MyPrintPass::insertCastToRestoreType (Instruction* insertAfterMe, 
                                            vector<Value*> & castinglist)
{
    for(vector<Value*>::iterator it = castinglist.begin(), ie = castinglist.end(); it!=ie ; ++it){
        if (Instruction * mycastinst = dyn_cast<Instruction>(*it)){
            if (!mycastinst->getParent()) {
                mycastinst->insertAfter (insertAfterMe);
                errs()<<"INST INSERTED: "<<*mycastinst<<"\n";
            }
        }
        else if (Constant* mycastconst= dyn_cast<Constant>(*it)) {
            //mycastconst->insertAfter (insertAfterMe);
            errs()<<"CONST NOT INSERTED: "<<*mycastconst<<"\n";
        }
        else {
            errs()<<"Neither cast inst nor constant\n";
            exit(0);
        }
    }  
} 

Instruction* MyPrintPass::doArrayAllocaInst (AllocaInst * AI, 
                                            Instruction * successorInst, 
                                            bool notDynamicArray,
                                            Module &M)
                                            //PostDominatorTree & postDT)
{
    //FRAMER_forall_alloca (void * locationOfAllocatedObject, uint64_t numElems, enum BASICType allocatedTypeID, unsigned numBytesPerElem )
    // TODO This is only for array of basictypes. Add struct type for elem... ALSO TODO merge this with doprimitivealocainst? duplicated code lines..
    
    Function * hook     = M.getFunction ("FRAMER_forall_alloca");
    Type * typeOfElem   = getTypeOfElemOfArray (AI->getAllocatedType());
    unsigned FramerTyID = getFramerTypeID (typeOfElem); 
    unsigned numBytes   =  MyPrintPass::getBitwidth(typeOfElem)/8;

    AllocaInst * paddedAI;
    GetElementPtrInst* origObj;

    if (!notDynamicArray) {
        return nullptr;
    }
    if (notDynamicArray){ 
        //--- to wrap an object
        vector<Type*> paddedObjTyList= {HeaderTy, AI->getAllocatedType(), OffByOneTy};
        StructType* paddedTy= StructType::create(M.getContext(), paddedObjTyList, "paddedStruct", true);

        Constant * nullHeader = Constant::getNullValue(HeaderTy);
        Constant * nullPad = Constant::getNullValue(OffByOneTy);

        paddedAI= new AllocaInst (paddedTy, AI->getName(), AI);
        paddedAI->setAlignment(16);
        
        vector<Value*> idx={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                            ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
        origObj= GetElementPtrInst::CreateInBounds (paddedTy,
                                               paddedAI,
                                               idx,
                                               "ptrToOrignalObj",
                                               AI);
    }
    else {
        errs()<<"dynamic array.. it may cause bug errors (10) again..\n"; exit(0);
        Instruction* addby2=nullptr;
        /* wtf is this duplicate??
        BinaryOperator* addby2= 
            BinaryOperator::Create (Instruction::Add,
                                    AI->getArraySize(), 
                                    ConstantInt::get ((AI->getArraySize())->getType(), 2, true), 
                                    "", 
                                    AI);
        */ 
        if ((uintptr_t)(MyPrintPass::getBitwidth(AI->getAllocatedType())) >= headerTySize) {
            addby2= BinaryOperator::Create (Instruction::Add,
                                    AI->getArraySize(), 
                                    ConstantInt::get(Type::getInt64Ty(M.getContext()), 2,true),
                                    "", 
                                    AI); 
        }
        else {
            errs()<<"do something for dyn_array alloca..\n";
            exit(0);
        }
        paddedAI= new AllocaInst (typeOfElem, addby2, AI->getName(), AI);
        paddedAI->setAlignment(16);
        
        errs()<<"paddedAI:\t"<<*paddedAI<<"\n";
        vector<Value*> idx={
                            //ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                            ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
        origObj= GetElementPtrInst::Create (AI->getAllocatedType(),
                                               paddedAI,
                                               idx,
                                               "ptrToOrignalObj",
                                               AI);
    }
    //--------- 
    Value * locationOfAllocatedObject = origObj; //AI;
    Value * numElems        = getArraySize(AI, hook->getFunctionType()->getParamType(1));
    Value * typeIDOfElem    = constructValueFromFunc (FramerTyID, hook, 2);
    Value * numBytesPerElem = constructValueFromFunc (numBytes, hook, 3);

    vector<Value *> arglist;

    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    origObj,//locationOfAllocatedObject, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    numElems, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2), 
                    typeIDOfElem, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3), 
                    numBytesPerElem, 
                    arglist);

    CallInst * CI = CallInst::Create (hook, arglist, "");
    
    Instruction* typeRestoringPtrForReplacedUse= 
        castAndreplaceAllUsesWith (AI, CI);
    
    insertCastInstForArg (successorInst, arglist);
    CI->insertBefore (successorInst);
    
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter (CI); 
    }
    
    insertEpilogueOfFunc (CI, M);//, postDT);
    
    errs()<<"exiting array alloca..\n";
    return AI;
}

Value * MyPrintPass::getPrimitiveEndAddress (AllocaInst * baseAddr, Instruction * insertBeforeMe, Module & M) 
{
    ConstantInt * numBytes       = 
        ConstantInt::get(Type::getInt64Ty(M.getContext()), 
                        (baseAddr->getAllocatedType()->getPrimitiveSizeInBits())/8);
    PtrToIntInst * baseAddrInInt = 
        new PtrToIntInst (baseAddr, Type::getInt64Ty(M.getContext()), "", insertBeforeMe);
    BinaryOperator * addByteNumToBase = BinaryOperator::Create (Instruction::Add, baseAddrInInt, numBytes, "", insertBeforeMe);
    IntToPtrInst * endAddr       = new IntToPtrInst (addByteNumToBase, baseAddr->getType(), "", insertBeforeMe);   
     
    return endAddr;

}

Value * MyPrintPass::getArrayEndAddress 
                (Value * baseAddr, unsigned numBitsOfElemTy, Value * numArrayElements, 
                 Type * typeToConvertTo, Instruction * insertBeforeMe, Module & M)
{
    IntegerType * my64IntTy = Type::getInt64Ty (M.getContext());
    
    ConstantInt * numByteOfElem = ConstantInt::get(my64IntTy, (numBitsOfElemTy/8));
    errs()<<"numBytesOfElem:\t"<<*numByteOfElem<<"\n";
    PtrToIntInst * baseAddrInInt = new PtrToIntInst (baseAddr, my64IntTy, "", insertBeforeMe);
    Instruction * totalNumBytes = 
                                BinaryOperator::Create (Instruction::Mul, numByteOfElem, numArrayElements, "", insertBeforeMe);
    errs()<<"totalNumBytes:\t"<<*totalNumBytes<<"\n";
    
    Instruction * addTotalByteNumToBaseAddr = 
                               BinaryOperator::Create (Instruction::Add, baseAddrInInt, totalNumBytes, "", insertBeforeMe);
    IntToPtrInst * endAddress = new IntToPtrInst (addTotalByteNumToBaseAddr, typeToConvertTo, "", insertBeforeMe); 
     
    return endAddress;
}


unsigned MyPrintPass::getPrimTyBits (unsigned Typeid)
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

uint64_t MyPrintPass::getBitwidthOfStruct ( StructType * STy )
{
    if (!STy->isSized()) {
        errs()<<"structure "<<*STy<<"is not sized!! \n";
        exit(0);
    }
    /*
       int sumBits = 0;
       
    if ( STy->isPacked()) { //no padding
        for (unsigned i=0;i<STy->getNumElements();++i) {
            sumBits = sumBits + MyPrintPass::getBitwidth (STy->getElementType(i), false);
        }
        return sumBits;
    }
    else { // padding may exist.
        // do something here..
    }
    */
    const StructLayout * strtlayout = dlayout->getStructLayout (STy);
    return (unsigned)strtlayout->getSizeInBits();

}

unsigned MyPrintPass::getBitwidth (Type * allocatedType, bool isOutMost)
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
            errs()<<"STRUCT SIZE in Bytes: "<< getBitwidthOfStruct (structTy)/8<<"\n";
            return (unsigned) getBitwidthOfStruct (structTy);
        }
        else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
            if (isOutMost) {
                return MyPrintPass::getBitwidth(arrayTy->getElementType(), false);
            }
            else {
                return (unsigned)(arrayTy->getNumElements()) *  MyPrintPass::getBitwidth(arrayTy->getElementType(), false); 
            }
        }
        else {
            errs()<<"Compositie type, but neither pointer nor struct\n";
            exit(0);
        }

    }
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else {
        errs()<<"What type is this?!\n";
        exit(0);
    }
}

bool MyPrintPass::isItsUser (Value * useuser, User * useruser)
{
    //for (Function::arg_iterator ai = F->arg_begin(), ae = F->arg_end(); ai!=ae ; ++ai) {
    for (Value::user_iterator it = useuser->user_begin(), ie=useuser->user_end();it!=ie;++it) {
        if (*it == useruser) {
            return true;
        }
    }
    return false;
}

/*  modified value replaces ALL USES of original one, EXCEPT newly inserted insts by pass. 
    the new cast insts are not inserted yet. still got caught as a uses, so skipping the new ones.  
    Call Hook is inserted BEFORE the target user. */
Instruction* MyPrintPass::castAndreplaceAllUsesWith(Value * originalPtr, 
                                                    Value* modifiedPtr)
                                                    //Value* ToBeReplacedwith,
{
    errs()<<"INSIDE castAndreplaceAllUsesWith\n"; 
    //restoring tagged_pointer back to original ptr is inserted right before the first use.
    /*assert ((isa<AllocaInst>(originalPtr) 
                || isa<GlobalVariable>(originalPtr) 
                || isa<GetElementPtrInst>(originalPtr))  
                && "Original Ptr must be AllocaInst or Global Variable!\n");
    commented out, since there are other cases of replacing origPtr. such as malloc, calloc, etc. 
    and GEP is not replaced?*/
        
        errs()<<"modified ptr: "<<*modifiedPtr->getType()<<"\n";
        errs()<<"orig ptr: "<<*originalPtr->getType()<<"\n";
    
    Instruction* bitcastFromModifiedToOrig = nullptr;

    if (originalPtr->getType()==modifiedPtr->getType() 
        && !isa<Constant>(originalPtr)) { 
        // if originalptr is void * type. (modifiedPtr type is fixed)
        /*replace all occurrences of original ptrs with the modified AI/GV. 
        Note that use of original_ptr in the hook func call is also replaced! */
        // restore a ptr in the hook function, which is modifiedAI/modifiedGV. 
        //No bitcast instructions inserted since types match. 
        //modifiedPtr->replaceUsesOfWith (modifiedPtr, originalPtr); 
        
        originalPtr->replaceAllUsesWith (modifiedPtr);
    
    }
    else if (originalPtr->getType() != modifiedPtr->getType()){
        errs()<<"different type, and not GV case.\n";     
        
        bitcastFromModifiedToOrig= new BitCastInst (modifiedPtr, 
                                                    originalPtr->getType(),
                                                    "");
        Use * currentUse =  &*originalPtr->use_begin();
        Use * nextUse = currentUse;
       
        errs()<<"before while\n"; 
        while ( nextUse ) {
            
            User * user = currentUse->getUser();
            nextUse = currentUse->getNext();
            errs()<<"current user: "<<*user<<"\n";
           
            if (Instruction * instUser = dyn_cast<Instruction>(user)){
                errs()<<"\tUser is inst\n"; 
                
                if (!instUser->getParent()){ //for inst user created by hook, not inserted yet.
                    currentUse = nextUse;
                    continue; 
                }
                if (!isHookFamilyFunction(instUser->getParent()->getParent())) {
                    (&*currentUse)->set(bitcastFromModifiedToOrig);
                    errs()<<"\treplaced\n";
                    errs()<<"\tnew: "<<*instUser<<"\n";
                    //instUsed=true;
                }
                else {
                    ;
                }
            } 
            else if (ConstantExpr* constUser= dyn_cast<ConstantExpr>(user)) {
                errs()<<"User is const\n"; 
                assert(isa<Constant>(modifiedPtr) && "modifiedPtr must be constant\n");
                Constant* bitcastConstant=
                    ConstantExpr::getPointerBitCastOrAddrSpaceCast(cast<Constant>(modifiedPtr), 
                                                                    (*currentUse)->getType());
                constUser->handleOperandChange (*currentUse, bitcastConstant);//, currentUse); 
                
                errs()<<"REPLACED!!!\n";
                errs()<<"constuser replaced? "<<*constUser<<"\n"; 
            }
            else {
                errs()<<"what is this?? Exiting..\n";
                exit(0);          
            }
            currentUse = nextUse;
        }
    }
    else { //old=new type && constant.
        assert((isa<Constant>(originalPtr) 
                && originalPtr->getType()==modifiedPtr->getType())
                && "what is this?? exiting.. \n");
        
        Use * currentUse =  &*originalPtr->use_begin();
        Use * nextUse = currentUse;

        while ( nextUse ) {
            User * user = currentUse->getUser();
            nextUse = currentUse->getNext();
            
            if (Instruction * instUser = dyn_cast<Instruction>(user)){
                if (!instUser->getParent()){ //for inst user created by hook, not inserted yet.
                    currentUse = nextUse;
                    continue; 
                }
                if (!isHookFamilyFunction(instUser->getParent()->getParent())) {
                    (&*currentUse)->set(modifiedPtr);
                }
                else {
                    ;    
                }
            }
            else if (ConstantExpr* constUser= dyn_cast<ConstantExpr>(user)) {
                constUser->handleOperandChange (*currentUse, modifiedPtr);//, currentUse); 
            }
            else {
                errs()<<"other cases?check. exiting \n";
                exit(0);
            }
            currentUse = nextUse;
        }      
    }
    
    PointersAreTagged = true;
    errs()<<"exiting castAndreplaceAllUsesWith... \n";
    return bitcastFromModifiedToOrig; 
}

int MyPrintPass::getUserStructTypeID (StructType* ty)
{
    int structtyid = -1; 
    vector<StructType*>::iterator it= find( allStructTyList.begin(),
                                            allStructTyList.end(), 
                                            ty);
    if (it != allStructTyList.end()) {
        structtyid= it - allStructTyList.begin();
    }
    return structtyid;
}

unsigned MyPrintPass::getUserIntegerTypeID (IntegerType* ty)
{
    unsigned intID=-1;
    unsigned numBits= (ty->getBitWidth());
    switch(numBits) {
        case 8:
            intID= 0; 
            break; 
        case 16:
            intID= 1; 
            break; 
        case 32:
            intID= 2; 
            break; 
        case 64:
            intID= 3; 
            break; 
        case 128:
            intID= 4; 
            break;
        default:
            errs()<<"Error, integer bitwidth is strange!\n";
            exit(0);
            break;
    }
    return intID;
}

unsigned MyPrintPass::getFramerTypeID (Type* ty)
{
    unsigned tID= 0;

    if ( StructType* st= dyn_cast<StructType>(ty)){
        errs()<<"Struct: "<<*st<<"\n"; 
        int sid = getUserStructTypeID(st);  
        assert(sid!=-1 && "cannot find the struct type in the struct type list\n");
        tID = FramerBasicTyCount + sid;  
    }
    else if (IntegerType* intT= dyn_cast<IntegerType>(ty)) {
        int intid = getUserIntegerTypeID(intT); 
        assert(intid!=-1 && "cannot find the integer type in the struct type list\n");
        tID = llvmbasicTyCount + intid; 
    }
    else {
        tID= ty->getTypeID();
    }
    return tID;
}

Constant* MyPrintPass::constructAddressValue (Module &M, GlobalVariable* tab, unsigned subindex)
{
    Type* ty= tab->getType(); 
    
    Constant* idconst= ConstantInt::get(Type::getInt64Ty(M.getContext()), subindex); 
    Constant* entryAddr = 
        ConstantExpr::getInBoundsGetElementPtr(ty, tab, idconst); 
    errs()<<"wtf is this?\n";
    exit(0); 
    return entryAddr;
}

bool MyPrintPass::isFramerIntID (unsigned id)
{
    bool isInt;
    if (llvmbasicTyCount<=id && id<FramerBasicTyCount){
        isInt= true;
    }
    else{
        isInt= false;
    }
    return isInt;
}
bool MyPrintPass::isFramerStructID (unsigned id)
{
    bool isStruct;
    if (FramerBasicTyCount<=id && id < (FramerBasicTyCount+structTyCount)) {
        isStruct=true;
    }
    else{
        isStruct=false;
    }
    return isStruct;
}

Constant* MyPrintPass::getFramerTyEntryAddress (Module &M, unsigned ftid)
{
    //starting address: StructTyTable
    // integer
    unsigned subindex = 0;
    GlobalVariable* subtytable;
    if (isFramerIntID(ftid)) {
        subtytable= basicTypeTable; 
        subindex = ftid;       
    } 
    else if (isFramerStructID(ftid)){ //struct
       subtytable = StructTyTable;
       subindex= ftid- FramerBasicTyCount;
    }
    else {
        subtytable= basicTypeTable; 
        subindex = ftid;       
    }
    Constant* entryAddrValue= constructAddressValue(M, subtytable, subindex); 
    
    return entryAddrValue;
}
/*
void MyPrintPass::doPrimitiveAllocaInst(AllocaInst * AI, 
                                        Instruction * successorInst, 
                                        Module &M)
{
    //void FRAMER_forall_alloca (void * locationOfAllocatedObject, uint64_t numElems, enum BASICType allocatedType, unsigned numBytesPerElem )
    
    Function * hook     = M.getFunction ("FRAMER_forall_alloca");
    unsigned FramerTyID = getFramerTypeID(AI->getAllocatedType()); 
    unsigned numBytes   = (MyPrintPass::getBitwidth(AI->getAllocatedType()))/8;
    //Constant* addressOfTyEntry = getFramerTyEntryAddress (M, FramerTyID); //address of type table entry
    
    Value* locationOfAllocatedObject = AI;
    Value* numArrayElem = 
        constructValueFromFunc (1, hook, 1); 
        // for non-array object, we set numarrayelem as '1'. 
    Value* typeIDOfAllocatedObj = 
        constructValueFromFunc (FramerTyID, hook, 2);
    Value * numBytesOfElemTy = 
        constructValueFromFunc (numBytes, hook, 3);
    
    //Value* locationOfFramerTyEntry = addressOfTyEntry; 
    //Value* locationOfFramerTyEntry = constructValueFromFunc (addressOfTyEntry, hook, 3); 

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    locationOfAllocatedObject, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1),
                    numArrayElem, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2) , 
                    typeIDOfAllocatedObj, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3) , 
                    numBytesOfElemTy, 
                    arglist);
    
    //pushtoarglist (successorInst, hook->getFunctionType()->getParamType(3) , 
    //        locationOfFramerTyEntry, arglist);
    //pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , 
    //        typeIDOfAllocatedObj, arglist);

    CallInst * modifiedAI = CallInst::Create(hook, arglist, "");
    Instruction * restoredPtr = castAndreplaceAllUsesWith (AI, modifiedAI, successorInst);
    insertCastInstForArg (successorInst, arglist);
    modifiedAI->insertBefore(successorInst);
    restoredPtr->insertAfter(modifiedAI);

    if (isa<StructType>(AI->getAllocatedType())) {
        padObject (AI, M);
    }
    else {
        errs()<<"not struct? what case is this?\n";
        exit(0);
    }
    errs()<<"\tNew ptr: "<<*modifiedAI<<"\n";
    
    for (Value::user_iterator ui= AI->user_begin(), ue= AI->user_end(); ui!=ue ; ++ui) {
        errs()<<"\tAI's User Iterator:\t"<<**ui<<"\n";
    }errs()<<"\n";
} */


Instruction* MyPrintPass::doPrimitiveAllocaInst(AllocaInst * AI, 
                                                Instruction * successorInst, 
                                                Module &M)
                                                //PostDominatorTree & postDT)
{
    //for struct alloca, get type of alloca. -> create struct-> replace all alloca uses. then replace itself.
    Function * hook     = M.getFunction ("FRAMER_forall_alloca");
    unsigned FramerTyID = getFramerTypeID(AI->getAllocatedType()); 
    unsigned numBytes   = (MyPrintPass::getBitwidth(AI->getAllocatedType()))/8;

//--- wrap the object in a struct   
    vector<Type*> paddedObjTyList= {HeaderTy, AI->getAllocatedType(), OffByOneTy};
    StructType* paddedTy= StructType::create(M.getContext(), paddedObjTyList, "paddedStruct", true);
    
    Constant* nullHeader = Constant::getNullValue(HeaderTy);
    Constant* nullPad = Constant::getNullValue(OffByOneTy);


    AllocaInst* paddedAI= new AllocaInst (paddedTy, AI->getName(), AI);
    paddedAI->setAlignment(16);
     
    errs()<<"PaddedAI: "<<*paddedAI<<"\n";
    
    vector<Value*> idx={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
    GetElementPtrInst* origObj=  
        GetElementPtrInst::CreateInBounds(paddedTy,
                                        paddedAI,
                                        idx,
                                        "ptrToOrignalObj",
                                        AI);
    errs()<<"new GEP: "<<*origObj<<"\n";
    errs()<<"origObj type:: "<<*origObj->getType()<<"\n";
//--------
    Value* numArrayElem = 
        constructValueFromFunc (1, hook, 1); 
        // for non-array object, we set numarrayelem as '1'. 
    Value* typeIDOfAllocatedObj = 
        constructValueFromFunc (FramerTyID, hook, 2);
    Value * numBytesOfElemTy = 
        constructValueFromFunc (numBytes, hook, 3);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    origObj,// locationOfAllocatedObject, // <---- replaced! 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1),
                    numArrayElem, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2) , 
                    typeIDOfAllocatedObj, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3) , 
                    numBytesOfElemTy, 
                    arglist);

    CallInst * modifiedAI = CallInst::Create(hook, arglist, "");
    
    //vector<Value*> castinglist;
    Instruction* restoredPtr= 
        castAndreplaceAllUsesWith (AI, modifiedAI);
    
    insertCastInstForArg (successorInst, arglist);
    modifiedAI->insertBefore(successorInst);
    //insertCastToRestoreType(modifiedAI, castinglist); 
    if (restoredPtr != nullptr) {
        restoredPtr->insertAfter(modifiedAI);
    }
    
    insertEpilogueOfFunc (modifiedAI, M);//, postDT);
    
    return AI;
}

Instruction* MyPrintPass::doAllocaInst (AllocaInst* AI, 
                                        Instruction* successorInst, 
                                        Module & M) //,
                                        //PostDominatorTree & postDT)
{
    bool notDynamicArray= false;

    if (AI->use_empty()) {
        errs()<<"\tuse list empty. skipping..\n";
        return nullptr;
    }
    
    Type * Ty = AI->getAllocatedType();
    Instruction* ToBeRemoved=NULL;

    if (AI->isArrayAllocation() 
        || AI->getArraySize() != ConstantInt::get(AI->getArraySize()->getType(), 1)) 
       {
        notDynamicArray= false;
        ToBeRemoved= doArrayAllocaInst (AI, successorInst, notDynamicArray, M);//, postDT);
        return ToBeRemoved;
    }
    if (Ty->isFirstClassType()) { 
        
        if (Ty->isSingleValueType() ) {
            
            if (Ty->isVectorTy()) {
                errs()<<"ERROR: Alloca - single valued, vector type. do something \n"; 
                exit(0);
            }
            else if (!(Ty->isPointerTy())) {
                errs()<<"\tSKIP: non-pointer type.\n";
                return ToBeRemoved; 
            }
            else {
                ;//doPrimitiveAllocaInst (AI, successorInst, M); 
                // doing nothing right now for non-array allocation. 
            }
        
        }
        else if (Ty->isAggregateType() ) {
            
            if (Ty->isArrayTy()) {
                notDynamicArray= true;
                ToBeRemoved= doArrayAllocaInst (AI, successorInst, notDynamicArray, M);//, postDT);
                return ToBeRemoved;
            }
            else if (Ty->isStructTy()) {
                ToBeRemoved= doPrimitiveAllocaInst (AI, successorInst, M);//, postDT); //tag structTyID!
                return ToBeRemoved; 
            }
            else {
                errs()<<"Aggregated type allocated, but neither array nor struct. It is "<<*Ty<<"\nDo something here. \n";
                exit(0);
            }
        }
    }
    else {
        errs()<<"Not a first class type! Exiting... do something for this. \n\n";
        exit(0);
    }
    return ToBeRemoved;
}

//ptr expects an operand (0) of load inst.
Value *  MyPrintPass::getOriginalAlloca (Value * ptr) 
{
    StringRef hookName = "";
    
    if (CallInst * callHook = dyn_cast<CallInst>(ptr)) { // The case of AI ty == modified AI Ty
        hookName = callHook->getCalledFunction()->getName();

        if (hookName.equals(StringRef("FRAMER_forall_alloca")) || 
            hookName.equals(StringRef("FRAMER_forall_global_variable"))) {

            errs()<<"\tis Modified one 1.\n";
            errs()<<"\treturining orig: "<<*callHook->getArgOperand(0)<<"\n";
            
            return callHook->getArgOperand(0);
       
        }
        else {
            errs()<<"Loaded from CallInst? .\n";
            exit(0);
        }
    }
    else if (CallInst * callHook = dyn_cast<CallInst>(cast<User>(ptr)->getOperand(0))) { // AI Ty != modified AI Ty
        hookName = callHook->getCalledFunction()->getName();

        if (hookName.equals(StringRef("FRAMER_forall_alloca")) || 
            hookName.equals(StringRef("FRAMER_forall_global_variable"))) {

            errs()<<"\tis Modified one 2.\n";
            errs()<<"\tCallInst Hook: "<<*callHook<<"\n";
            errs()<<"\tCallInst's arg: "<<*callHook->getArgOperand(0)<<"\n";
            errs()<<"\tCallinst's arg(bitcast)'s op(0): "<<*cast<BitCastInst>(callHook->getArgOperand(0))->getOperand(0)<<"\n";

            Value * OriginalPtr = cast<BitCastInst>(callHook->getArgOperand(0))->getOperand(0);
            return OriginalPtr;
        }
        else {
            errs()<<"Loaded from CallInst? seems wrong..\n";
            exit(0);
        }
    }
    else {
        errs()<<"Not a modified Alloca family. so Skip...\n";
        return nullptr;
    }
     
    
}

void MyPrintPass::restoreModifiedPtr (LoadInst * LI) 
{
    Value * MaybeModifiedPtr = LI->getOperand(0);

    //*** from here, implementation of restoring an original alloca in load inst. ****
    Value * originalPtr = getOriginalAlloca (MaybeModifiedPtr);
    if (originalPtr != nullptr ){
        errs()<<"\tRestoring load...\n";
        LI->replaceUsesOfWith (MaybeModifiedPtr, originalPtr); 
        errs()<<"\tFinal restored LoadInst: "<<*LI<<"\n";
    }

}

void MyPrintPass::castAndreplaceUsesOfWithBeforeInst(Instruction* user, 
                                                    Value* from, 
                                                    Value * toThis)
{
    if (from->getType() == toThis->getType()) { 
        // if originalptr is void * type. (toThis type is fixed)
        //replace 'from' with the modified value (toThis)!
        user->replaceUsesOfWith (from, toThis);
    }
    else {
        BitCastInst * mybitcastinst= 
            new BitCastInst (toThis, from->getType(),"");
        mybitcastinst->insertBefore(user);
        //errs()<<"INSERTED: "<<*mybitcastinst<<"\n";
        //unlike alloca, FRAMER_load and bitcast should be inserted BEFORE load inst.
        //replace 'from' with mybitcastinst which casts toThis (modifiedptr) to 'from's type.
        user->replaceUsesOfWith (from, mybitcastinst);
    }
}

void MyPrintPass::doLoadInst (LoadInst * LI, Instruction * successorInst, Module &M)
{
    /*if (!isTaggedPointer((LI->getPointerOperand())->stripPointerCasts())) {
        return;
    }*/
    Function * hook = M.getFunction ("FRAMER_forall_load");
    
    Type *  typeOfLoadedContent = LI->getType();
    Value * typeIDOfLoadedContent= 
        constructValueFromFunc (typeOfLoadedContent->getTypeID(), 
                                hook, 
                                1);
    Value * numBytesOfLoadedContent= 
        constructValueFromFunc (MyPrintPass::getBitwidth(typeOfLoadedContent)/8, 
                                hook, 
                                2);
    
    vector<Value *> arglist;
    
    //here 'insertBeforeMe' is LoadInst itself, since hook call and bitcast should be inserted BEFORE LI for a relacement.
    pushtoarglist (LI, 
                    hook->getFunctionType()->getParamType(0), 
                    LI->getOperand(0),     
                    arglist);
    pushtoarglist (LI, 
                    hook->getFunctionType()->getParamType(1), 
                    typeIDOfLoadedContent, 
                    arglist);
    pushtoarglist (LI, 
                    hook->getFunctionType()->getParamType(2), 
                    numBytesOfLoadedContent, 
                    arglist);
    
    
    //modifiedPtr == return val of hook == tag-stripped pointer.
    CallInst * modifiedPtr = CallInst::Create(hook, arglist, "");
    errs()<<"modifiedptr: "<<*modifiedPtr<<"\n";
    insertCastInstForArg (LI, arglist); 
    modifiedPtr->insertBefore(LI);

    /* replace operand of LI with modifiedPtr, since operand of LI is tagged pointer. 
    If an in-bound pointer, load with tag-stripped pointer, if else out-of-bound, error msgs and exit. */
    castAndreplaceUsesOfWithBeforeInst (LI, 
                                        LI->getOperand(0), 
                                        modifiedPtr);
    
}

Value* MyPrintPass::tagFramerTyID ( Value * val, 
                                    unsigned id, 
                                    Module &M) 
{
    Value* result;
    uintptr_t tagvec = ((uintptr_t)id)<<48;
    errs()<<"FramerTypeID tagged vec: "<<tagvec<<"\n"; 
    ConstantInt* idconst= 
        ConstantInt::getSigned (Type::getInt64Ty(M.getContext()), 
                                tagvec); 
    
    if (Constant* constval= dyn_cast<Constant>(val)){
        Constant* idtagged= ConstantExpr::getOr(idconst, constval);
        result= idtagged;
    }
    else {
        //create and operator. do process. and insert the operator before store.  
        BinaryOperator* or_tag = 
            BinaryOperator::Create(Instruction::Or, 
                                   idconst, val, 
                                   "referencedVar");
        result= or_tag; 
    }
    return result;
}
bool MyPrintPass::isTaggedPointer (Value* accessedPtr)
{
    errs()<<"strippedptr: "<<*accessedPtr<<"\n";
    bool istagged=false;
    if (CallInst* ci= dyn_cast<CallInst>(accessedPtr)) {
        Function * f= ci->getCalledFunction();
        if (f->getName().equals("FRAMER_supplementary_untag_ptr")) {
            errs()<<"already untagged? how? check!\n";
            exit(0); 
        }
        else if (isHookFamilyFunction(f)) {
            istagged=true; 
        }
        else {;}
    }
    return istagged;
}

void MyPrintPass::doStoreInst ( StoreInst * SI, 
                                Instruction * successorInst, 
                                Module &M)
{
   // void * FRAMER_forall_store (void * destAddress, enum BASICType srcValueTy, unsigned numBytesOfSrcTy );
 
    errs()<<"meow store ptr op: "<<*(SI->getPointerOperand())->stripPointerCasts()<<"\n";
    /*if (!isTaggedPointer((SI->getPointerOperand())->stripPointerCasts())) {
        return;
    }*/
    Function * hook = M.getFunction ("FRAMER_forall_store");
    
    Value* val = SI->getOperand(0);  
    Type * srcType = val->getType(); 
    unsigned srcFramerTyID = getFramerTypeID(srcType); 
     
    errs()<<"STORE: SI->op(0): "<<*val<<"\n";
    if (isa<AllocaInst>(val) || isa<GlobalVariable>(val)) {
        errs()<<"REFERENCE! replacing Store->op(0)..\n";

        /*in case of array typed allocation, the operand(0) is call hook, neither alloca nor gv. */
        assert(!(val->getType()->isArrayTy()) 
            && "Error! array typed allocation should have been replaced with call hook!! check\n");
        Value* IDtagged= tagFramerTyID(val, srcFramerTyID, M);  
        SI->setOperand(0, IDtagged);
        if (BinaryOperator * op= dyn_cast<BinaryOperator>(IDtagged)){
            op->insertBefore(SI); 
        }
    }
    /*if (!isa<PointerType>(srcType)) {
        srcAddress = Constant::getNullValue (hook->getFunctionType()->getParamType(0));
    } -> wtf is this? */

    Value * destAddress     = SI->getPointerOperand();
    //Value * srcValueTyID    = constructValueFromFunc(srcType->getTypeID(), hook, 1);
    Value * srcValueTyID    = 
        constructValueFromFunc (srcFramerTyID, 
                                hook, 
                                1);
        errs()<<"meow?";
    Value * numBytesOfSrcTy = 
        constructValueFromFunc (MyPrintPass::getBitwidth(srcType)/8, 
                                hook, 
                                2);

        errs()<<"meow!";
    assert (srcType == (cast<PointerType>(destAddress->getType())->getElementType()) 
            && "Type mismatch between src and dest in store."); 

    vector<Value *> arglist;
         
    pushtoarglist (SI, 
                    hook->getFunctionType()->getParamType(0), 
                    destAddress,    
                    arglist);
    pushtoarglist (SI, 
                    hook->getFunctionType()->getParamType(1), 
                    srcValueTyID,   
                    arglist);
    pushtoarglist (SI, 
                    hook->getFunctionType()->getParamType(2), 
                    numBytesOfSrcTy, 
                    arglist);
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (SI, arglist);
    modifiedPtr->insertBefore (SI);
    castAndreplaceUsesOfWithBeforeInst(SI, destAddress, modifiedPtr);
}


void MyPrintPass::doGetElementPtrInst (GetElementPtrInst * GEP, 
                                        Instruction * successorInst, 
                                        Module &M)
{
    /*void FRAMER_getelementptr(void * dest_addr, 
                                void * base_addr, 
                                enum BASICType typeOfbaseAddr, 
                                unsigned NumBytesOfElemTy, 
                                int64_t numindices, 
                                int64_t idx0, int64_t idx1, 
                                int64_t idx2, int64_t idx3, 
                                int64_t idx4, int64_t idx5 ) */
    /*void* FRAMER_forall_getelementptr (void * GEP, 
                                    void * baseOfGEP, 
                                    unsigned srcFramerTyID,  
                                    unsigned resultFramerTyID); */ 
    
    Function* hook= M.getFunction ("FRAMER_forall_getelementptr");
    
    unsigned srcFramerTyID= 
        getFramerTypeID(GEP->getSourceElementType()); 
    unsigned resultFramerTyID= 
        getFramerTypeID(GEP->getResultElementType()); 
    
    //unsigned arg_idx  = 5; 
    /* GEP idx starts after 4 arguments 
    (GEP addr, base addr, typeOfbaseAddr, NumBytesOfElemTy, numofindices) */
    
    /*Value* redundant_arg_val = 
        ConstantInt::getSigned(hook->getFunctionType()->getParamType(4), -2); 
    
    assert (GEP->getNumIndices() + arg_idx <= hook->getFunctionType()->getNumParams() 
            && "Only GEP instructions with >= 6 indices can be processed. Add more case to doGetElementPtrInst.\n");
   */

    //Type * GEPElemType          = 
    //    cast<PointerType>(GEP->getOperand(0)->getType())->getElementType();
   /* Value * typeIDOfElem        = 
        constructValueFromFunc(getFramerTypeID(GEPElemType), //GEPElemType->getTypeID(),   
                                hook, 
                                2);
    Value * NumBytesOfElemTy    = 
        constructValueFromFunc(MyPrintPass::getBitwidth(GEPElemType)/8,
                                hook, 
                                3); 
    Value * numIndicesValue     = 
        ConstantInt::getSigned(hook->getFunctionType()->getParamType(4), 
                                GEP->getNumIndices()); */
    Value* srcFramerTyIDval= constructValueFromFunc(
                                    srcFramerTyID,   
                                    hook, 
                                    2);
    Value* resultFramerTyIDval= constructValueFromFunc(
                                    resultFramerTyID,   
                                    hook, 
                                    3);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    GEP, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    GEP->getPointerOperand(), 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2), 
                    srcFramerTyIDval, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3), 
                    resultFramerTyIDval, 
                    arglist);
     
    /* 
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2), 
                    typeIDOfElem, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3), 
                    NumBytesOfElemTy, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(4), 
                    numIndicesValue, 
                    arglist);
  */
  /*  
    for (GetElementPtrInst::op_iterator it=GEP->idx_begin(),ie=GEP->idx_end(); it!=ie; ++it) {
        pushtoarglist (successorInst, 
                        hook->getFunctionType()->getParamType(arg_idx), 
                        *it, 
                        arglist);
        arg_idx++;
    }
    
    for (unsigned i=arg_idx ; i < hook->getFunctionType()->getNumParams() ; ++i ) {
        pushtoarglist ( successorInst, 
                        hook->getFunctionType()->getParamType(arg_idx), 
                        redundant_arg_val , 
                        arglist);
    } */
    //insertFunctionCall (hook, successorInst, arglist);
    
    for (GetElementPtrInst::op_iterator it=GEP->idx_begin(), ie=GEP->idx_end(); it!=ie; ++it)
    {
        errs()<<**it<<", ";  
    } errs()<<" )\n";
    
    CallInst * modifiedGEP = CallInst::Create(hook, arglist, "");
    
    //Instruction * restoringPtr = 
    //    castAndreplaceAllUsesWith (GEP, modifiedGEP); 
    insertCastInstForArg (successorInst, arglist);
    modifiedGEP->insertBefore(successorInst);
    
    //if (restoringPtr!=nullptr) {
    //    restoringPtr->insertAfter(modifiedGEP); 
    //}
    errs()<<"\tNew ptr: "<<*modifiedGEP<<"\n";
}


void MyPrintPass::doFPToSIInst (FPToSIInst * FTS, 
                                Instruction * successorInst, 
                                Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_fptosi");
    
    Type * SrcTy    = FTS->getSrcTy(); 
    Type * DestTy   = FTS->getDestTy();

    assert (SrcTy->isFloatingPointTy() && DestTy->isIntegerTy() && "The type of FPToSI is wrong!\n"); 

    Value * numBytesOfSrc     = 
        constructValueFromFunc(MyPrintPass::getBitwidth(SrcTy)/8, 
                                hook, 
                                0);
    Value * numBytesOfDest    = 
        constructValueFromFunc(MyPrintPass::getBitwidth(DestTy)/8, 
                                hook, 
                                1);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    numBytesOfSrc, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesOfDest, 
                    arglist);
    insertCastInstForArg (successorInst, arglist);
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doSIToFPInst   (SIToFPInst * SFI, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sitofp");
    
    Type * SrcTy    = SFI->getSrcTy(); 
    Type * DestTy   = SFI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isFloatingPointTy() && "The type of SIToFP is wrong!\n");

    Value * numBytesOfSrc     = constructValueFromFunc (MyPrintPass::getBitwidth(SrcTy)/8, hook, 0);
    Value * numBytesOfDest    = constructValueFromFunc (MyPrintPass::getBitwidth(DestTy)/8, hook, 1);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , numBytesOfSrc, arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfDest, arglist);
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doFPExt (FPExtInst * FEI, Instruction * successorInst, Module & M)
{
    Function * hook = M.getFunction ("FRAMER_forall_fpext");
    
    Type * SrcTy    = FEI->getSrcTy(); 
    Type * DestTy   = FEI->getDestTy();

    assert (SrcTy->isFloatingPointTy() && DestTy->isFloatingPointTy() && "The types of FPExt are wrong!\n");

    unsigned numBytesOfSrcTy = MyPrintPass::getBitwidth(SrcTy)/8;
    unsigned numBytesOfDestTy = MyPrintPass::getBitwidth(DestTy)/8;

    assert (numBytesOfSrcTy < numBytesOfDestTy && "SrcTy of FPExt must be smaller than the destination type.\n");

    Value * numBytesOfSrc     = constructValueFromFunc (numBytesOfSrcTy, hook, 0);
    Value * numBytesOfDest    = constructValueFromFunc (numBytesOfDestTy, hook, 1);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , numBytesOfSrc, arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfDest, arglist);
    
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);
 
}

void MyPrintPass::doPtrToIntInst (PtrToIntInst * PTI, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_ptrtoint (void * ptrToBeConvertedToInt, unsigned ptrSizeInBytes, unsigned numBytesOfDestType, uint64_t resultOfPtrToInt)

    Function * hook = M.getFunction ("FRAMER_forall_ptrtoint");
    
    Value * ptrToBeConvertedToInt   = PTI->getOperand(0);
    Value * ptrSizeInBytes          = constructValueFromFunc(dlayout->getPointerSize(), hook, 1);
    Value * numBytesOfDestType      = constructValueFromFunc((PTI->getType()->getIntegerBitWidth())/8, hook, 2);
    Value * resultOfPtrToInt        = PTI;

    assert (PTI->getOperand(0)->getType()->isPointerTy() && "PtrToInt's operand must be pointer typed.\n");
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0), ptrToBeConvertedToInt,  arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1), ptrSizeInBytes,         arglist); 
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2), numBytesOfDestType,     arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(3), resultOfPtrToInt,       arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doIntToPtrInst (IntToPtrInst * ITP, Instruction * successorInst, Module &M) 
{
    /*
        void FRAMER_inttoptr (uint64_t intToBeConvertedToPtr, unsigned ptrSizeInBytes, void * resultOfIntToPtr)
    */
    
    Function * hook = M.getFunction ("FRAMER_forall_inttoptr");
    
    Value * intToBeConvertedToPtr   = ITP->getOperand(0);
    Value * ptrSizeInBytes        = constructValueFromFunc(dlayout->getPointerSize(), hook, 1);
    Value * resultOfIntToPtr        = ITP;

    assert (ITP->getSrcTy()->isIntegerTy() && "Either Trunc or its operand is not int typed!\n");
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , intToBeConvertedToPtr, arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , ptrSizeInBytes,      arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , resultOfIntToPtr,      arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doAddrSpaceCastInst (AddrSpaceCastInst * I, Instruction * successorInst, Module & M)
{
    /* void FRAMER_forall_addrspacecast (void * ptrToBeCasted,
                                unsigned addrSpaceOfSrcPtr,
                                unsigned addrSpaceOfDestPtr); */
  
    errs()<<"AddrSpaceCastInst! Not tested.. Test doAddrSpaceCastInst in the pass.. \n";
    exit(0);


    Function * hook = M.getFunction ("FRAMER_forall_addrspacecast");
    
    Value * ptrToBeCasted       = I->getOperand(0);
    Value * addrSpaceOfSrcPtr   = constructValueFromFunc (cast<PointerType>(I->getSrcTy())->getAddressSpace(), hook, 1); 
    Value * addrSpaceOfDestPtr  = constructValueFromFunc (cast<PointerType>(I->getDestTy())->getAddressSpace(), hook, 2); ;

    assert ((I->getSrcTy()->isPointerTy() && I->getDestTy()->isPointerTy()) 
            && "Either Trunc or its operand is not int typed!\n");
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , ptrToBeCasted,     arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , addrSpaceOfSrcPtr, arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , addrSpaceOfDestPtr,arglist);
    
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);

}


Value * MyPrintPass::castingArgToParam (Instruction * I, Type * paramType, Value * arg)
{
    if ( paramType != arg->getType()) {
            BitCastInst * mybitcastinst = new BitCastInst (arg, paramType,"");
            mybitcastinst->insertBefore(getNextInst(I));
            return mybitcastinst;
    }
    else {
        return arg;
    }
}


/*
pushtoarglist does NOT insert castinst for arg. 
just creating a castinst, and then pushing to arglist.
*/
void MyPrintPass::pushtoarglist(Instruction * insertBeforeMe, 
                                Type * paramTy,
                                Value * argtobepushed, 
                                vector<Value*> & arglist) 
{
    errs()<<"\narg: "<<*argtobepushed<<", paramTy: "<<*paramTy<<"\n";
    if ( paramTy != argtobepushed->getType()) {
        if (CastInst* temp= dyn_cast<CastInst>(argtobepushed)) {
            if (temp->getSrcTy() == paramTy) {
                arglist.push_back(temp->getOperand(0));
                return;
            }
        }
        if (paramTy->isPointerTy() && argtobepushed->getType()->isPointerTy()) {
            BitCastInst * mybitcastinst = new BitCastInst (argtobepushed, paramTy,"");
            //mybitcastinst->insertBefore(insertBeforeMe);
            //castToHookArgType = mybitcastinst;
            arglist.push_back(mybitcastinst);
        }
        else if (isa<PtrToIntInst>(argtobepushed) 
                || isa<TruncInst>(argtobepushed) 
                || isa<FPToSIInst>(argtobepushed)) {
            
            ZExtInst * myzext = new ZExtInst (argtobepushed, paramTy, "");
            //myzext->insertBefore(insertBeforeMe);
            arglist.push_back(myzext);
        }
        else if (isa<SExtInst>(argtobepushed)) {
            SExtInst * mysext = new SExtInst (argtobepushed, paramTy, "");
            //mysext->insertBefore(insertBeforeMe);
            //castToHookArgType = mysext;
            arglist.push_back(mysext);
        }
        else if (paramTy->isIntegerTy() && argtobepushed->getType()->isIntegerTy()) {
            //errs()<<"(paramTy->getIntegerBitWidth(): "<<paramTy->getIntegerBitWidth() <<"\n";
            //errs()<<"(argtobepushed->getType())->getIntegerBitWidth(): "<<(argtobepushed->getType())->getIntegerBitWidth()<<"\n";
            assert(paramTy->getIntegerBitWidth() >= (argtobepushed->getType())->getIntegerBitWidth()
                    && "created arg for hook's int bitwdith is bigger than hook's original type width!\n");
            SExtInst * mysext = new SExtInst (argtobepushed, paramTy, "");
            arglist.push_back(mysext);
        }
        else {
            errs()<<"ParamTy: "<<*paramTy<<", arg: "<<*argtobepushed->getType()<<"\n";
            errs()<<"!!!Unspecified type conversion!\n";
            exit(0);
        }
        return;
    }
    else {
        arglist.push_back(argtobepushed);
        //assert (isa<Instruction>(argtobepushed) 
        //&& "argtobepushed is an instruction. change the code of insertCastInstForArg so that arg duplicates are not inserted. \n");
    }
}

void MyPrintPass::doTruncInst (TruncInst * TR, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_trunc");
    Type * SrcTy    = TR->getSrcTy(); 
    Type * DestTy   = TR->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (MyPrintPass::getBitwidth(SrcTy) > MyPrintPass::getBitwidth(DestTy))
            && "TruncInst:: Both Src and Dest should be Int typed! and #SrcTyBytes > #DestTyBytes\n");
    //TODO: op(0)'s bitwidth should be larger than trunc's bitwidth.
    
    Value * numBytesOfSrcTy    = constructValueFromFunc (MyPrintPass::getBitwidth(SrcTy)/8, hook, 1); 
    Value * numBytesOfDestTy   = constructValueFromFunc (MyPrintPass::getBitwidth(DestTy)/8, hook, 2);
    
    vector<Value *> arglist;

    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , TR,                arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfSrcTy,   arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfDestTy,  arglist);
   
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);

}


void MyPrintPass::doSExtInst (SExtInst * SI, Instruction * successorInst,  Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sext");
    Type * SrcTy    = SI->getSrcTy(); 
    Type * DestTy   = SI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (MyPrintPass::getBitwidth(SrcTy) < MyPrintPass::getBitwidth(DestTy))
            && "SextInst:: Both Src and Dest should be Int typed! and #SrcTyBytes < #DestTyBytes\n");
    
    Value * numBytesOfSrcTy    = constructValueFromFunc (MyPrintPass::getBitwidth(SrcTy)/8, hook, 1); 
    Value * numBytesOfDestTy   = constructValueFromFunc (MyPrintPass::getBitwidth(DestTy)/8, hook, 2);
    
    vector<Value *> arglist;

    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , SI,                arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfSrcTy,   arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfDestTy,  arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doZExtInst (ZExtInst * ZI, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_zext");
    Type * SrcTy    = ZI->getSrcTy(); 
    Type * DestTy   = ZI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (MyPrintPass::getBitwidth(SrcTy) < MyPrintPass::getBitwidth(DestTy))
            && "ZextInst:: Both Src and Dest should be Int typed! and #SrcTyBytes < #DestTyBytes\n");
    //TODO: op(0)'s bitwidth should be larger than trunc's bitwidth.
    
    Value * numBytesOfSrcTy    = constructValueFromFunc (MyPrintPass::getBitwidth(SrcTy)/8, hook, 1); 
    Value * numBytesOfDestTy   = constructValueFromFunc (MyPrintPass::getBitwidth(DestTy)/8, hook, 2);
    
    vector<Value *> arglist;

    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , ZI,                arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfSrcTy,   arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfDestTy,  arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doOverflowBinaryOp (OverflowingBinaryOperator * OFO, Instruction * successorInst, Module & M)
{
    //errs()<<"OverflowOp: "<<*OFO<<"\n";

    switch (OFO->getOpcode()) {
        case Instruction::Add :
            {
                //if (!HookDefinitionExists.count(Instruction::Add)) {
                if (!HookDefinitionExists[Instruction::Add]) {
                    errs()<<"No hooks provided for this inst. Skipping..\n";
                    break;
                }
                
                AddOperator * AO = dyn_cast<AddOperator>(OFO);
                doAddOp (AO, successorInst, M); 
                break;
            }
        case Instruction::Sub :
            {
                //if (!HookDefinitionExists.count(Instruction::Sub)) {
                if (!HookDefinitionExists[Instruction::Sub]) {
                    errs()<<"No hooks provided for this inst. Skipping..\n";
                    break;
                }

                SubOperator * SO = dyn_cast<SubOperator>(OFO);
                doSubOp (SO, successorInst, M);
                break;
            }
        case Instruction::Mul :
            {
                if (!HookDefinitionExists[Instruction::Mul]) {
                    errs()<<"No hooks provided for this inst. Skipping..\n";
                    break;
                }

                MulOperator * MO = dyn_cast<MulOperator>(OFO);
                doMulOp (MO, successorInst, M);
                break;
            }
    }
}

void MyPrintPass::doPossiblyExactOp  (PossiblyExactOperator * PEO, Instruction * successorInst, Module & M)
{
    switch (PEO->getOpcode()) {
        case Instruction::SDiv :
            {
                if (!HookDefinitionExists[Instruction::SDiv]) {
                    errs()<<"No hooks provided for SDiv inst. Skipping..\n";
                    break;
                }

                SDivOperator * SDO = dyn_cast<SDivOperator>(PEO);
                doSDivOp (SDO, successorInst, M); 
                break;
            }
        case Instruction::UDiv :
            {
                if (!HookDefinitionExists[Instruction::UDiv]) {
                    errs()<<"No hooks provided for UDiv inst. Skipping..\n";
                    break;
                } 

                UDivOperator * UDO = dyn_cast<UDivOperator>(PEO);
                doUDivOp (UDO, successorInst, M);
                break;
            }
        case Instruction::LShr :
            {
                if (!HookDefinitionExists[Instruction::LShr]) {
                    errs()<<"No hooks provided for LShr inst. Skipping..\n";
                    break;
                } 

                LShrOperator * LSR = dyn_cast<LShrOperator>(PEO);
                doLShrOp (LSR, successorInst, M);
                break;
            }
        case Instruction::AShr :
            {
                if (!HookDefinitionExists[Instruction::AShr]) {
                    errs()<<"No hooks provided for AShr inst. Skipping..\n";
                    break;
                } 

                AShrOperator * OP = dyn_cast<AShrOperator>(PEO);
                doAShrOp (OP, successorInst, M);
                break;
            }
        default: 
            {
                errs()<<"doPossiblyExact op missing!\n";
                exit(0);
                break;
            }
    }
 
}



void MyPrintPass::doSubOp (SubOperator * SO, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_subop (int64_t operand_0, int64_t operand_1, int64_t numBytesOfIntType)
    Function * hook = M.getFunction ("FRAMER_forall_subop");
    
    Type * OpTy = SO->getType();
    
    assert ((SO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Two operands of Sub operator should be the same typed and integertyped!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
   
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , SO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , SO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
     
}

void MyPrintPass::doMulOp (MulOperator * MO, Instruction * successorInst,  Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_mulop");
    
    Type * OpTy = MO->getType();
    
    assert ((MO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of Mul operator should be the same typed, int typed!\n");

    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    
    vector<Value *> arglist;
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , MO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , MO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doAddOp (AddOperator * AO, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_addop");
    
    Type * OpTy = AO->getType();
    
    assert ((AO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of ADD operator should be the same typed, int typed!\n");
    
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , AO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , AO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
}

void MyPrintPass::doSDivOp (SDivOperator * SDO, Instruction * successorInst, Module & M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sdiv");
    
    Type * OpTy = SDO->getType();
    
    assert ((SDO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of SDiv operator should be the same typed, int typed!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
   
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , SDO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , SDO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void MyPrintPass::doUDivOp (UDivOperator * UDO, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_uDivop (int64_t operand_0, int64_t operand_1, int64_t numBytesOfIntType)

    Function * hook = M.getFunction ("FRAMER_forall_udiv");
    
    Type * OpTy = UDO->getType();
    
    assert ((UDO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of UDiv operator should be the same typed, int typed!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , UDO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , UDO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
}

void MyPrintPass::doLShrOp (LShrOperator * UDO, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_lshr");
    
    Type * OpTy = UDO->getType();
    
    assert ((UDO->getOperand(0)->getType()->isIntegerTy()) && (UDO->getOperand(1)->getType()->isIntegerTy())
            && "Both of operands of LShr operator should be int typed!\n");
   
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , UDO->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , UDO->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
 
}

void MyPrintPass::doAShrOp (AShrOperator * OP, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_ashr");
    
    Type * OpTy = OP->getType();
    
    assert ((OP->getOperand(0)->getType()->isIntegerTy()) && (OP->getOperand(1)->getType()->isIntegerTy())
            && "Both of operands of AShr operator should be int typed!\n");
   
    Value * numBytesOfIntType = constructValueFromFunc (MyPrintPass::getBitwidth(OpTy)/8, hook, 2);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , OP->getOperand(0), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , OP->getOperand(1), arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
 
}

void MyPrintPass::insertFunctionCall(Function * F, 
                                    Instruction * insertBeforeMe, 
                                    vector<Value*> & arglist) 
{
    CallInst * CI = CallInst::Create (F, arglist, "");
    CI->insertBefore (insertBeforeMe);
}

CallInst * MyPrintPass::insertHookAndReturn(Function * F, 
                                            Instruction * insertBeforeMe, 
                                            vector<Value*> & arglist) 
{
    CallInst * CI = CallInst::Create (F, arglist, "");
    CI->insertBefore (insertBeforeMe);
    return CI;
}


Value * MyPrintPass::getEndAddrforMalloc (Value * baseAddr, Value * numBytes, Type * typeToConvertTo, Instruction * insertBeforeMe, Module & M)
{
    IntegerType * my64IntTy = Type::getInt64Ty (M.getContext());

    errs()<<"numBytes:\t"<<*numBytes<<"\n";
    PtrToIntInst * baseAddrInInt = new PtrToIntInst (baseAddr, my64IntTy, "", insertBeforeMe);
    errs()<<"BaseAddr in Int: "<<*baseAddrInInt<<"\n";
    Instruction * addTotalByteNumToBaseAddr = 
                               BinaryOperator::Create (Instruction::Add, baseAddrInInt, numBytes, "", insertBeforeMe);
    errs()<<"Base+Bytes: "<<*addTotalByteNumToBaseAddr<<"\n";
    IntToPtrInst * endAddress = new IntToPtrInst (addTotalByteNumToBaseAddr, typeToConvertTo, "", insertBeforeMe); 
     
    return endAddress;
     
}

Type* MyPrintPass::getResultTypeOfMalloc (CallInst * CI)
{
    //if CI is operand(0) of bitcast following the CI, and then stored to a pointertype.
    Function* calledF= CI->getCalledFunction();
    Type* malloctype = calledF->getReturnType(); 
     
    errs()<<"\tcalledfunc: "<<*calledF<<"\n";
    for (Value::use_iterator it = CI->use_begin(), ie = CI->use_end(); it!=ie ; ++it) {
        if (BitCastInst* user = dyn_cast<BitCastInst>((&*it)->getUser()) ) {
            errs()<<"\tbitcast inst: "<<*user<<"\n";
            for (Value::use_iterator iit = user->use_begin(), iie = user->use_end(); iit!=iie ; ++iit) {
                if (StoreInst* SI = dyn_cast<StoreInst>((&*iit)->getUser())) {
                    errs()<<"\tbitcast's store user: "<<*SI<<"\n";
                    errs()<<"mallloc CI: "<<*CI<<"\n";
                    errs()<<"mallloc return pointer casted.\n";
                    errs()<<"casted returned ptr: (bitcast destTy)"<<*user->getDestTy()<<"\n"; 
                    malloctype= user->getDestTy();
                }
                else {
                    errs()<<"what situation? malloc return type\n";
                }
            }
        }
        else {
            errs()<<"??\n"; 
        }
    }
    return malloctype;
}

Instruction* MyPrintPass::doCallInstMalloc (CallInst * CI, 
                                            Instruction * successorInst, 
                                            Module & M)
{
    /* Replace malloc with wrapper function. */
    
    Function * hook = M.getFunction("FRAMER_forall_call_malloc");
   
    // -- get the (possibly casted) return type of malloc 
    Type * resultTypeOfMalloc = getResultTypeOfMalloc (CI);
    unsigned FramerTyID = getFramerTypeID(resultTypeOfMalloc); 
    
    Value * typeInstance= 
        constructValueFromFunc (FramerTyID, hook, 0);
    Value * numBytesAllocated= CI->getArgOperand(0);
    
    vector <Value*> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    typeInstance, 
                    arglist);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesAllocated, 
                    arglist);
    //TODO: typeInstance should be OUR typeid. USER TYPEID
    
    CallInst * newCI = CallInst::Create (hook, arglist, "");
    Instruction * typeRestoringPtrForReplacedUse = 
        castAndreplaceAllUsesWith (CI, newCI); 

    insertCastInstForArg (CI, arglist);
    newCI->insertBefore (CI); //then hook callinst inserted.
    
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter(newCI);
    }
    
    return CI;
}

Instruction* MyPrintPass::doCallInstFree(CallInst * CI, 
                                        Instruction * successorInst, 
                                        Module & M)
{
    Function * hook = M.getFunction("FRAMER_forall_call_free");
    
    vector <Value*> arglist;
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0),
                    CI->getArgOperand(0), 
                    arglist);
   
    CallInst * newCI= CallInst::Create (hook, arglist, "");
    Instruction* typeRestoringPtrForReplacedUse= 
        castAndreplaceAllUsesWith (CI, newCI); 
    
    insertCastInstForArg (CI, arglist);
    newCI->insertBefore (CI); //then hook callinst inserted.
    
    //insertCastToRestoreType(newCI, castinglist); 
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter(newCI);
    }
    return CI;
}

void MyPrintPass::doCallLLVMMemTransfer (MemTransferInst* MI, 
                                        Instruction * successorInst, 
                                        Module &M)
{
    // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memtransfer");
    Function * hook_for_src = M.getFunction ("FRAMER_supplementary_untag_ptr");
    
    assert(hook!=nullptr && 
            "memcpy hook funcion is empty\n");
   
    Value * destAddress     = MI->getRawDest();
    Value * srcAddress      = MI->getRawSource();
    Value * numBytesToCopy  = MI->getLength();
    Value * numAlign        = MI->getAlignmentCst();
    Value * isVolatile      = MI->getVolatileCst(); 
    
    vector<Value *> dest_arglist;
    vector<Value *> src_arglist;
    
    pushtoarglist (MI, 
                    hook->getFunctionType()->getParamType(0), 
                    destAddress,   
                    dest_arglist);
    pushtoarglist (MI, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesToCopy,
                    dest_arglist);
    pushtoarglist (MI, 
                    hook->getFunctionType()->getParamType(2), 
                    numAlign,      
                    dest_arglist);
    pushtoarglist (MI, 
                    hook->getFunctionType()->getParamType(3), 
                    isVolatile,    
                    dest_arglist);
    
    CallInst* destModifiedPtr= CallInst::Create (hook, dest_arglist, "");
    insertCastInstForArg (MI, src_arglist);
    destModifiedPtr->insertBefore (MI);
    castAndreplaceUsesOfWithBeforeInst (MI, 
                                        destAddress, 
                                        destModifiedPtr);

    //if (!isa<Constant>(srcAddress)) { // TODO: why did I make this?? I don't get it. :(
        pushtoarglist (MI, 
                hook->getFunctionType()->getParamType(0), 
                srcAddress,    
                src_arglist);
        pushtoarglist (MI, 
                hook->getFunctionType()->getParamType(1), 
                numBytesToCopy,
                src_arglist);
        pushtoarglist (MI, 
                hook->getFunctionType()->getParamType(2), 
                numAlign,      
                src_arglist);
        pushtoarglist (MI, 
                hook->getFunctionType()->getParamType(3), 
                isVolatile,    
                src_arglist);
         
    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (MI, dest_arglist);
    srcModifiedPtr->insertBefore (MI);
    castAndreplaceUsesOfWithBeforeInst (MI, 
                                        srcAddress, 
                                        srcModifiedPtr);
  //  }
}
/*
void MyPrintPass::doCallLLVMMemCpy (MemCpyInst * MCI, Instruction * successorInst, Module &M)
{
    // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memcpy_src");
    
    Value * destAddress     = MCI->getRawDest();
    Value * srcAddress      = MCI->getRawSource();
    Value * numBytesToCopy  = MCI->getLength();
    Value * numAlign        = MCI->getAlignmentCst();
    Value * isVolatile      = MCI->getVolatileCst(); 
     
    vector<Value *> arglist;
    
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(0) , destAddress,   arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(1) , srcAddress,    arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(2) , numBytesToCopy,arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(3) , numAlign,      arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(4) , isVolatile,    arglist);
    
    //insertFunctionCall (hook, successorInst, arglist);
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (MCI, arglist);
    modifiedPtr->insertBefore (MCI);
    castAndreplaceUsesOfWithBeforeInst (MCI, srcAddress, modifiedPtr);

}


void MyPrintPass::doCallLLVMMemCpyDEST (MemCpyInst * MCI, Instruction * successorInst, Module &M)
{
    // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memcpy_dest");
    
    Value * destAddress     = MCI->getRawDest();
    Value * srcAddress      = MCI->getRawSource();
    Value * numBytesToCopy  = MCI->getLength();
    Value * numAlign        = MCI->getAlignmentCst();
    Value * isVolatile      = MCI->getVolatileCst(); 

    vector<Value *> arglist;
    
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(0) , destAddress,   arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(1) , srcAddress,    arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(2) , numBytesToCopy,arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(3) , numAlign,      arglist);
    pushtoarglist (MCI, hook->getFunctionType()->getParamType(4) , isVolatile,    arglist);
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    
    insertCastInstForArg (MCI, arglist);
    modifiedPtr->insertBefore (MCI);
    
    castAndreplaceUsesOfWithBeforeInst (MCI, destAddress, modifiedPtr);

}


void MyPrintPass::doCallLLVMMemMoveSRC (MemMoveInst * MMI, Instruction * successorInst, Module &M)
{
    // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memmove_src");
    
    Value * destAddress     = MMI->getRawDest();
    Value * srcAddress      = MMI->getRawSource();
    Value * numBytesToCopy  = MMI->getLength();
    Value * numAlign        = MMI->getAlignmentCst();
    Value * isVolatile      = MMI->getVolatileCst(); 
     
    vector<Value *> arglist;
    
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(0) , destAddress,   arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(1) , srcAddress,    arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(2) , numBytesToCopy,arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(3) , numAlign,      arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(4) , isVolatile,    arglist);
    
    //insertFunctionCall (hook, MMI, arglist);
      
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (MMI, arglist);
    modifiedPtr->insertBefore (MMI);
   
    castAndreplaceUsesOfWithBeforeInst (MMI, srcAddress, modifiedPtr);


}

void MyPrintPass::doCallLLVMMemMoveDEST (MemMoveInst * MMI, Instruction * successorInst, Module &M)
{
    // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memmove_dest");
    
    Value * destAddress     = MMI->getRawDest();
    Value * srcAddress      = MMI->getRawSource();
    Value * numBytesToCopy  = MMI->getLength();
    Value * numAlign        = MMI->getAlignmentCst();
    Value * isVolatile      = MMI->getVolatileCst(); 
     
    vector<Value *> arglist;
    
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(0) , destAddress,   arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(1) , srcAddress,    arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(2) , numBytesToCopy,arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(3) , numAlign,      arglist);
    pushtoarglist (MMI, hook->getFunctionType()->getParamType(4) , isVolatile,    arglist);
    
    //insertFunctionCall (hook, MMI, arglist);
      
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (MMI, arglist);
    modifiedPtr->insertBefore (MMI);
    castAndreplaceUsesOfWithBeforeInst (MMI, destAddress, modifiedPtr);

}
*/

void MyPrintPass::doCallLLVMMemSet (MemSetInst * MSI, Instruction * successorInst, Module &M)
{
    /* (Src, Dest, numBytesToCopy, alignment, isVolatile )*/    
    
    Function * hook = M.getFunction ("FRAMER_forall_call_llvm_memset");
    
    Value * destAddress     = MSI->getRawDest();
    Value * val             = MSI->getValue();
    Value * numBytesToCopy  = MSI->getLength();
    Value * numAlign        = MSI->getAlignmentCst();
    Value * isVolatile      = MSI->getVolatileCst(); 
    
    vector<Value *> arglist;
    
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(0) , destAddress,   arglist);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(1) , val,           arglist);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(2) , numBytesToCopy,arglist);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(3) , numAlign,      arglist);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(4) , isVolatile,    arglist);
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (MSI, arglist);
    modifiedPtr->insertBefore (MSI);
    castAndreplaceUsesOfWithBeforeInst (MSI, destAddress, modifiedPtr);

}

void MyPrintPass::doCallExternalFunc (CallInst * CI, Instruction * successorInst, Module &M)
{
    errs()<<"entered external\n"; 
   
    Function * hook     = M.getFunction ("FRAMER_supplementary_untag_ptr");
    Value * calledValue = CI->getCalledValue();

   /* if (cast<Function>(calledValue)->getName().equals("printf")) {
        return;
    }*/
    for (unsigned i = 0 ; i < CI->getNumArgOperands (); i++) {
        Value * From =CI->getArgOperand(i); 
        errs()<<"\tARG: "<<*From<<"\n";
        
        if (!(From->getType()->isPointerTy())) {
            errs()<<"Neither Pointer nor aggregated. Skipping..\n";
            continue;
        }
        // can we skip constant? constant (such as gep) can be also out-of-bound, right?

        vector<Value *> arglist; 
        pushtoarglist (CI, hook->getFunctionType()->getParamType(0), From, arglist);
        insertCastInstForArg (CI, arglist);
        CallInst * tagStrippedPtr = CallInst::Create (hook, arglist);
        tagStrippedPtr->insertBefore (CI);
        CI->setOperand(i, tagStrippedPtr); 
        errs()<<"new CI: "<<*CI<<"\n";
    }
}

Instruction* MyPrintPass::doCallInst (CallInst * CI, Instruction * successorInst, Module &M)
{
    Value * calledValue;
    
    if (isa<CastInst>(CI->getCalledValue())) {
        calledValue= CI->getCalledValue()->stripPointerCasts(); 
    }
    Instruction * toBeRemoved = NULL;
    //errs()<<"\tcalledvalue: "<<*calledValue<<"\n";
    
    /*
    if ( calledValue == M.getFunction(StringRef("malloc"))  && 
        HookDefForCalledFuncExists[MallocIsCalled] ) { 
        errs()<<"\tcallling do malloc... \n";
        toBeRemoved = doCallInstMalloc (CI, successorInst, M);
    }
    else if ( calledValue == M.getFunction(StringRef("free"))  && 
        HookDefForCalledFuncExists[FreeIsCalled] ) {
        errs()<<"\tcalling free \n";
        toBeRemoved = doCallInstFree (CI, successorInst, M);
    } */
    if (Function * calledfunc = dyn_cast<Function>(calledValue))  { 
        if (calledValue == M.getFunction(StringRef("malloc")) ||
            calledValue == M.getFunction(StringRef("free"))) {
            return NULL; 
        }
        
        //when call(or invoke) function where function is defined in the uninstrumented codes.
        errs()<<"Calling outside function..\n";
        if (calledfunc->isDeclaration() && HookDefForCalledFuncExists[ExternalFuncIsCall]) {
            doCallExternalFunc (CI, successorInst, M);
        }
    } 
    else if (MemTransferInst * MCI = dyn_cast<MemTransferInst>(CI) ) {
        errs()<<"calling MemTransferInst \n"; 
        if (HookDefForCalledFuncExists[LLVMMemTransferIsCalled]) {
            doCallLLVMMemTransfer (MCI, successorInst, M);
        }
    }    
    else if (MemSetInst * MSI = dyn_cast<MemSetInst>(CI) ) {
        errs()<<"calling memset \n";
        if (HookDefForCalledFuncExists[LLVMMemSetIsCalled]) {
            doCallLLVMMemSet (MSI, successorInst, M);
        }
    }
    else if (LoadInst * li= dyn_cast<LoadInst>(calledValue)){
        //it may not be external func, but to avoid handling CFI, we just untag all the pointer args.
        
        // 1. get pointer operand li->getOperand() (func_ptr)
        // 2. get uses of func_ptr. -> if store inst && func_ptr is SI's pointer ptr_op
            // && no SI uses between the SI and li, where each SI's ptr op is not func_ptr
            //, if it's external function. then docallexternalfunc. otherwise do nothing. 
        errs()<<"sort out indirect call in a different way? like CFG? dunno.. anyway exiting..\n"; 
        exit(0);    
        doCallExternalFunc (CI, successorInst, M); 
    }
    else {
        ;
    }
    /*  else if ((!isa<Function>(calledValue))) {
        errs()<<"CallInst called non-function. what case is this?\n";
        exit(0);
        }
        else {
        errs()<<"CallInst: neither memIntrinsic function. skipping..\n";
    //return NULL;
    } */
    return toBeRemoved;

}

void MyPrintPass::pushArgForBitCastInst (FunctionType *FTy, BitCastInst * BCI, vector<Value*> & arglist)
{

    Value * argToBePushed = castingArgToParam (BCI, FTy->getParamType(0), BCI); //TODO: BCI or successorInst??
    arglist.push_back(argToBePushed);
}

void MyPrintPass::doBitCastInst (BitCastInst * BCI, Instruction * successorInst, Module &M)
{
     // TODO. print addresses of op(0) and BCI itself.
    //void FRAMER_forall_bitcast (unsigned sourceTypeID, unsigned targetTypeID, unsigned numBytes)
    
    errs()<<"inside doBitcast\n";

    Function * hook = M.getFunction("FRAMER_forall_bitcast");
    
    Type * srcType      = BCI->getSrcTy();
    Type * destType     = BCI->getDestTy();
    
    assert (srcType->isFirstClassType() && destType->isFirstClassType() && "Both source and destination types must be a first class type.\n");
    
    Value * srcTypeID   = constructValueFromFunc (srcType->getTypeID(),     hook, 0);
    Value * destTypeID  = constructValueFromFunc (destType->getTypeID(),    hook, 1);
    Value * numBytesOfTy= constructValueFromFunc ((MyPrintPass::getBitwidth(destType)/8),hook, 2);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0), srcTypeID ,     arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1), destTypeID,     arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2), numBytesOfTy,   arglist);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(3), BCI,            arglist);
  
    CallInst * modified = CallInst::Create(hook, arglist, "");
    insertCastInstForArg (successorInst, arglist);
    modified->insertBefore(successorInst);
}


uint64_t  MyPrintPass::getArraySizeforGV (Type * allocatedObjTy) 
{
    if (ArrayType * arr = dyn_cast<ArrayType>(allocatedObjTy)){
        uint64_t size = arr->getNumElements();
        return size; //uint64_t type..
    }
    else {
        return 1;
    }
}

Value * MyPrintPass::getEndAddressGV (GlobalVariable * GV, uint64_t numElems, unsigned numBitsOfElemTy, 
                                       Type * typeToConvertTo ,Instruction * insertBeforeMe, Module & M)
{
    IntegerType * my64IntTy = Type::getInt64Ty (M.getContext());
    
    ConstantInt * numElemsInConst = ConstantInt::get(my64IntTy, numElems);
    ConstantInt * numByteOfElem = ConstantInt::get(my64IntTy, (numBitsOfElemTy/8));
    PtrToIntInst * baseAddrInInt = new PtrToIntInst (GV, my64IntTy, "", insertBeforeMe);
    Instruction * totalNumBytes = 
                                BinaryOperator::Create (Instruction::Mul, numByteOfElem, numElemsInConst, "", insertBeforeMe);
    
    Instruction * addTotalByteNumToBaseAddr = 
                               BinaryOperator::Create (Instruction::Add, baseAddrInInt, totalNumBytes, "", insertBeforeMe);
    IntToPtrInst * endAddress = new IntToPtrInst (addTotalByteNumToBaseAddr, typeToConvertTo, "", insertBeforeMe); 
    
    return endAddress;

}

size_t MyPrintPass::pow2roundup (size_t x)
{
    assert (x >= 0 && "Size Of object is negative! \n");
    --x;
    
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    
    return x+1;
}

size_t MyPrintPass::getNewAlignment (size_t totalsize)
{
    return pow2roundup(totalsize);
}

void MyPrintPass::insertCastInstForArg(Instruction * insertBeforeMe, vector<Value*> & arglist )
{
    for(vector<Value*>::iterator it = arglist.begin(), ie = arglist.end(); it!=ie ; ++it){
        if (Instruction * mycast = dyn_cast<Instruction>(*it)){
            if (!mycast->getParent()) {
                mycast->insertBefore (insertBeforeMe);
                errs()<<"INSERTED: "<<*mycast<<"\n";
            }
        }
    }
}

bool MyPrintPass::isToBeTaggedType (Type* t)
{
    bool isToBeTagged = 0;

    if ( t->isVectorTy() 
        //t->isPointerTy() 
        || t->isStructTy() 
        || t->isArrayTy()){ 
         isToBeTagged = 1;
    }
    return isToBeTagged; 
}
/*
Value* MyPrintPass::createPads(Value* val, Module &M)
{
    vector<Type*> paddedObjTyList= {HeaderTy, val->getType(), OffByOneTy};
    StructType* paddedTy= StructType::get(M.getContext(), paddedObjTyList, "paddedStruct");
    
    Constant * nullHeader = Constant::getNullValue(HeaderTy);
    Constant * nullPad = Constant::getNullValue(OffByOneTy);
    Value* paddedObj;

    if (GlobalVariable* GV= dyn_cast<GlobalVariable>(val)) {
        vector<Constant*> GVinitializer= {nullHeader, GV, nullPad}; 
        
        GlobalVariable* PaddedGV = new GlobalVariable( 
                M,
                paddedTy,
                false,
                GV->getLinkage(),
                GVinitializer,
                "");
        paddedObj=PaddedGV; 
    }
    else if (AllocaInst * AI = dyn_cast<AllocaInst>(val)) {
        
        AllocaInst * paddedAI= new AllocaInst (paddedTy, AI->getName());
        paddedObj= paddedAI;
    }
    else {
        errs()<<"to-be-padded is neither GV nor AI. Exiting..\n";
        exit(0);
    }
    return paddedObj; 
}
*/

void MyPrintPass::padObject (Value* obj, Module &M)
{
    Constant * nullHeader = Constant::getNullValue(HeaderTy);
    Constant * nullPad = Constant::getNullValue(OffByOneTy);
     
    if (GlobalVariable* GV= dyn_cast<GlobalVariable>(obj)) {
        unsigned gvalign = GV->getAlignment();
        
        assert( (((uint64_t)gvalign <= headerTySize) 
            || ((uint64_t)gvalign == 2*headerTySize)) 
            && "Header for global array is not attached with no gap to the array. Resizing or re-alignment of header is needed. \n");

        Module::global_iterator git (GV);
        git++; 

        GlobalVariable* header= new GlobalVariable( M,
                HeaderTy,
                false,
                GV->getLinkage(),
                nullHeader,
                "",
                GV);
        GlobalVariable* pad= new GlobalVariable( M,
                OffByOneTy,
                false,
                GV->getLinkage(),
                nullPad,
                "",
                &*git);

        if (gvalign == 16) {
            GlobalVariable* dummyheader= new GlobalVariable( M,
                    HeaderTy,
                    false,
                    GV->getLinkage(),
                    nullHeader,
                    "",
                    header);
            errs()<<"\tAlignment of GV is 16, hence, 2 headers added\n";
        }
    }
    else if (AllocaInst * AI = dyn_cast<AllocaInst>(obj)) {
         unsigned allocaAlign = AI->getAlignment();
         
         assert( (((uint64_t)allocaAlign <= headerTySize) 
            || ((uint64_t)allocaAlign == 2*headerTySize)) 
            && "Header for Alloca array is not attached with no gap to the array. Resizing or re-alignment of header is needed. \n");
         
        BasicBlock::iterator it (AI);
        it++; 
        
        AllocaInst * header= new AllocaInst (HeaderTy, "", AI);
        AllocaInst * pad= new AllocaInst (OffByOneTy, "",&*it);
        
        if (allocaAlign == 16) {
            AllocaInst * dummyheader= new AllocaInst (HeaderTy, "", header);
        } 
    }
}

Constant* MyPrintPass::tagConstantPtr (Constant* ptr, 
                                        Constant* tag, 
                                        Constant* flag, 
                                        Module & M)
{
    errs()<<"entered tagConstantPtr\n";
    Constant* tagInPosition= 
        ConstantExpr::getShl(tag,ConstantInt::getSigned(Type::getInt64Ty(M.getContext()),48));
    Constant* flagInPosition=
        ConstantExpr::getShl(flag, 
                            ConstantInt::getSigned(Type::getInt64Ty(M.getContext()), 63));
    errs()<<"exiting tagConstantPtr\n\n";
    
    return ConstantExpr::getOr (ConstantExpr::getPtrToInt(ptr, tagInPosition->getType()), 
                                ConstantExpr::getOr(tagInPosition, flagInPosition));   
}

Constant* MyPrintPass::getPaddedEndInt(GlobalVariable* paddedGV, Module & M)
{
    vector<Value*> idx={ConstantInt::get(Type::getInt32Ty(M.getContext()), 0),
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 2)};
    Constant* endAddr= 
        ConstantExpr::getInBoundsGetElementPtr (cast<PointerType>(paddedGV->getType()->getScalarType())->getContainedType(0u),
                                                paddedGV,
                                                idx);
    return ConstantExpr::getPtrToInt(endAddr, Type::getInt64Ty(M.getContext()));
}

Constant* MyPrintPass::getLogFrameSize (Constant* base, Constant* end, Module & M)
{
    errs()<<"inside getlogframesize\n";
    
    //vector<Constant*> args= {xorResult};
    //vector<Type *> arg_type={xorResult->getType()};
    //Function *fun = Intrinsic::getDeclaration(&M, Intrinsic::ctlz, arg_type);
    //Constant* clzResult= ConstantFoldCall(fun, args);  
    //Constant* clzResult= xorResultInt->countLeadingZeros();  
            //Intrinsic::ctlz, 
    
    //-- 
    Constant* xorResult= ConstantExpr::getXor(base, end);
    
    Constant* shiftedby63= constCLZ(63);
    
    Constant* shiftedby62= 
        ConstantExpr::getSelect(MacroEqualTo( 62), 
                                constCLZ(62),
                                shiftedby63);    
    Constant* shiftedby61= 
        ConstantExpr::getSelect(MacroEqualTo( 61), 
                                constCLZ(61),
                                shiftedby62);    
    Constant* shiftedby60= 
        ConstantExpr::getSelect(MacroEqualTo( 60), 
                                constCLZ(60),
                                shiftedby61);    
    Constant* shiftedby59= 
        ConstantExpr::getSelect(MacroEqualTo( 59), 
                                constCLZ(59),
                                shiftedby60);    
    Constant* shiftedby58= 
        ConstantExpr::getSelect(MacroEqualTo( 58), 
                                constCLZ(58),
                                shiftedby59);    
    Constant* shiftedby57= 
        ConstantExpr::getSelect(MacroEqualTo( 57), 
                                constCLZ(57),
                                shiftedby58);    
    Constant* shiftedby56= 
        ConstantExpr::getSelect(MacroEqualTo( 56), 
                                constCLZ(56),
                                shiftedby57);    
    Constant* shiftedby55= 
        ConstantExpr::getSelect(MacroEqualTo( 55), 
                                constCLZ(55),
                                shiftedby56);    
    Constant* shiftedby54= 
        ConstantExpr::getSelect(MacroEqualTo( 54), 
                                constCLZ(54),
                                shiftedby55);    
    Constant* shiftedby53= 
        ConstantExpr::getSelect(MacroEqualTo( 53), 
                                constCLZ(53),
                                shiftedby54);    
    Constant* shiftedby52= 
        ConstantExpr::getSelect(MacroEqualTo( 52), 
                                constCLZ(52),
                                shiftedby53);    
    Constant* shiftedby51= 
        ConstantExpr::getSelect(MacroEqualTo( 51), 
                                constCLZ(51),
                                shiftedby52);    
    Constant* shiftedby50= 
        ConstantExpr::getSelect(MacroEqualTo( 50), 
                                constCLZ(50),
                                shiftedby51);    
    Constant* shiftedby49= 
        ConstantExpr::getSelect(MacroEqualTo( 49), 
                                constCLZ(49),
                                shiftedby50);    
    Constant* shiftedby48= 
        ConstantExpr::getSelect(MacroEqualTo( 48), 
                                constCLZ(48),
                                shiftedby49);    
    Constant* shiftedby47= 
        ConstantExpr::getSelect(MacroEqualTo( 47), 
                                constCLZ(47),
                                shiftedby48);    
    Constant* shiftedby46= 
        ConstantExpr::getSelect(MacroEqualTo( 46), 
                                constCLZ(46),
                                shiftedby47);    
    Constant* shiftedby45= 
        ConstantExpr::getSelect(MacroEqualTo( 45), 
                                constCLZ(45),
                                shiftedby46);    
    Constant* shiftedby44= 
        ConstantExpr::getSelect(MacroEqualTo(44), 
                                constCLZ(44),
                                shiftedby45);    
    Constant* shiftedby43= 
        ConstantExpr::getSelect(MacroEqualTo( 43), 
                                constCLZ(43),
                                shiftedby44);    
    Constant* shiftedby42= 
        ConstantExpr::getSelect(MacroEqualTo( 42), 
                                constCLZ(42),
                                shiftedby43);    
    Constant* shiftedby41= 
        ConstantExpr::getSelect(MacroEqualTo( 41), 
                                constCLZ(41),
                                shiftedby42);    
    Constant* shiftedby40= 
        ConstantExpr::getSelect(MacroEqualTo( 40), 
                                constCLZ(40),
                                shiftedby41);    
    Constant* shiftedby39= 
        ConstantExpr::getSelect(MacroEqualTo( 39), 
                                constCLZ(39),
                                shiftedby40);    
    Constant* shiftedby38= 
        ConstantExpr::getSelect(MacroEqualTo( 38), 
                                constCLZ(38),
                                shiftedby39);    
    Constant* shiftedby37= 
        ConstantExpr::getSelect(MacroEqualTo( 37), 
                                constCLZ(37),
                                shiftedby38);    
    Constant* shiftedby36= 
        ConstantExpr::getSelect(MacroEqualTo( 36), 
                                constCLZ(36),
                                shiftedby37);    
    Constant* shiftedby35= 
        ConstantExpr::getSelect(MacroEqualTo( 35), 
                                constCLZ(35),
                                shiftedby36);    
    Constant* shiftedby34= 
        ConstantExpr::getSelect(MacroEqualTo( 34), 
                                constCLZ(34),
                                shiftedby35);    
    Constant* shiftedby33= 
        ConstantExpr::getSelect(MacroEqualTo( 33), 
                                constCLZ(33),
                                shiftedby34);    
    Constant* shiftedby32= 
        ConstantExpr::getSelect(MacroEqualTo( 32), 
                                constCLZ(32),
                                shiftedby33);    
    Constant* shiftedby31= 
        ConstantExpr::getSelect(MacroEqualTo( 31), 
                                constCLZ(31),
                                shiftedby32);    
    Constant* shiftedby30= 
        ConstantExpr::getSelect(MacroEqualTo( 30), 
                                constCLZ(30),
                                shiftedby31);    
    Constant* shiftedby29= 
        ConstantExpr::getSelect(MacroEqualTo( 29), 
                                constCLZ(29),
                                shiftedby30);    
    Constant* shiftedby28= 
        ConstantExpr::getSelect(MacroEqualTo( 28), 
                                constCLZ(28),
                                shiftedby29);    
    Constant* shiftedby27= 
        ConstantExpr::getSelect(MacroEqualTo( 27), 
                                constCLZ(27),
                                shiftedby28);    
    Constant* shiftedby26= 
        ConstantExpr::getSelect(MacroEqualTo( 26), 
                                constCLZ(26),
                                shiftedby27);    
    Constant* shiftedby25= 
        ConstantExpr::getSelect(MacroEqualTo( 25), //xor == 1000....
                                constCLZ(25),
                                shiftedby26);    
    Constant* shiftedby24= 
        ConstantExpr::getSelect(MacroEqualTo( 24), //xor == 1000....
                                constCLZ(24),
                                shiftedby25);    
    Constant* shiftedby23= 
        ConstantExpr::getSelect(MacroEqualTo( 23), //xor == 1000....
                                constCLZ(23),
                                shiftedby24);    
    Constant* shiftedby22= 
        ConstantExpr::getSelect(MacroEqualTo( 22), //xor == 1000....
                                constCLZ(22),
                                shiftedby23);    
    Constant* shiftedby21= 
        ConstantExpr::getSelect(MacroEqualTo( 21), //xor == 1000....
                                constCLZ(21),
                                shiftedby22);    
    Constant* shiftedby20= 
        ConstantExpr::getSelect(MacroEqualTo( 20), //xor == 1000....
                                constCLZ(20),
                                shiftedby21);    
    Constant* shiftedby19= 
        ConstantExpr::getSelect(MacroEqualTo( 19), //xor == 1000....
                                constCLZ(19),
                                shiftedby20);    
    Constant* shiftedby18= 
        ConstantExpr::getSelect(MacroEqualTo( 18), 
                                constCLZ(18),
                                shiftedby19);    
    Constant* shiftedby17= 
        ConstantExpr::getSelect(MacroEqualTo( 17), 
                                constCLZ(17),
                                shiftedby18);    
    Constant* shiftedby16= 
        ConstantExpr::getSelect(MacroEqualTo( 16), 
                                constCLZ(16),
                                shiftedby17);    
    Constant* shiftedby15= 
        ConstantExpr::getSelect(MacroEqualTo( 15), 
                                constCLZ(15),
                                shiftedby16);    
    Constant* shiftedby14= 
        ConstantExpr::getSelect(MacroEqualTo( 14), 
                                constCLZ(14),
                                shiftedby15);    
    Constant* shiftedby13= 
        ConstantExpr::getSelect(MacroEqualTo( 13), 
                                constCLZ(13),
                                shiftedby14);    
    
    Constant* shiftedby12= 
        ConstantExpr::getSelect(MacroEqualTo( 12), 
                                constCLZ(12),
                                shiftedby13);    
    Constant* shiftedby11= 
        ConstantExpr::getSelect(MacroEqualTo( 11), 
                                constCLZ(11),
                                shiftedby12);    
    Constant* shiftedby10= 
        ConstantExpr::getSelect(MacroEqualTo( 10),
                                constCLZ(10),
                                shiftedby11);    
    Constant* shiftedby9= 
        ConstantExpr::getSelect(MacroEqualTo( 9), 
                                constCLZ(9),
                                shiftedby10);    
    Constant* shiftedby8= 
        ConstantExpr::getSelect(MacroEqualTo( 8), 
                                constCLZ(8),
                                shiftedby9);    
    Constant* shiftedby7= 
        ConstantExpr::getSelect(MacroEqualTo( 7), 
                                constCLZ(7),
                                shiftedby8);    
    Constant* shiftedby6= 
        ConstantExpr::getSelect(MacroEqualTo( 6), 
                                constCLZ(6),
                                shiftedby7);    
    Constant* shiftedby5= 
        ConstantExpr::getSelect(MacroEqualTo( 5), 
                                constCLZ(5),
                                shiftedby6);    
    Constant* shiftedby4= 
        ConstantExpr::getSelect(MacroEqualTo( 4), 
                                constCLZ(4),
                                shiftedby5);    
    Constant* shiftedby3= 
        ConstantExpr::getSelect(MacroEqualTo( 3), 
                                constCLZ(3),
                                shiftedby4);    
    Constant* shiftedby2= 
        ConstantExpr::getSelect(MacroEqualTo( 2), 
                                constCLZ(2),
                                shiftedby3);    
    Constant* shiftedby1= 
        ConstantExpr::getSelect(MacroEqualTo( 1), 
                                constCLZ(1),
                                shiftedby2);    
     
    Constant* shiftedby0= 
        ConstantExpr::getSelect(MacroEqualTo( 0), 
                                constCLZ(0),
                                shiftedby1);    
    //--- 
    Constant* isEqualToZero= 
        ConstantExpr::getICmp(CmpInst::ICMP_EQ, 
                                       xorResult,
                                       ConstantInt::get(Type::getInt64Ty(M.getContext()), 0)); 
                                                   //check left/right is right.
    Constant* clzResult= ConstantExpr::getSelect(isEqualToZero, 
                                ConstantInt::get(Type::getInt64Ty(M.getContext()), 64), 
                                shiftedby0);
    
     
    //----------------------
    errs()<<"exiting getlogframesize..\n";
    return ConstantExpr::getSub(ConstantInt::get(Type::getInt64Ty(M.getContext()), 64),
                                clzResult);
}

Constant* MyPrintPass::getOffset (Constant* base, Module & M)
{
    //mask=. flag =1
    Constant* getOffsetMask= 
        ConstantInt::getSigned(Type::getInt64Ty(M.getContext()), 0x7FFF);
    return ConstantExpr::getAnd(base, getOffsetMask);
}

Constant* MyPrintPass::getTaggedConstantPtr(GlobalVariable* basePadded,
                                            Constant* origPtr,
                                            Module & M)
{
    
    Constant* basePaddedInt= ConstantExpr::getPointerCast(basePadded,
                                                        Type::getInt64Ty(M.getContext()));
    errs()<<"basePaddedInt: "<<*basePaddedInt<<"\n";
    Constant* N= getLogFrameSize(basePaddedInt, 
                                getPaddedEndInt(basePadded, M),
                                M);

    Constant* isBigFrame=ConstantInt::get(Type::getInt64Ty(M.getContext()), 0);
    Constant* isSmallFrame=ConstantInt::get(Type::getInt64Ty(M.getContext()), 1);
    
    Constant* NTagged= 
        tagConstantPtr(origPtr, //?? or basepadded? ptr or int type? 
                       N, 
                       isBigFrame, 
                       M);
    Constant* offsetTagged= 
        tagConstantPtr (origPtr, 
                        getOffset(basePaddedInt, M), 
                        isSmallFrame,
                        M);
    Constant* cond= ConstantExpr::getICmp (CmpInst::ICMP_SGT, 
                                           N, 
                                           ConstantInt::get(N->getType(), FRAMER_log_slotsize));
    Constant* taggedPtr= ConstantExpr::getSelect (cond, NTagged, offsetTagged); 
        
    errs()<<"exiting getTaggedConstantPtr\n";
    return ConstantExpr::getIntToPtr(taggedPtr, origPtr->getType());
}

/*void MyPrintPass::updateHeaderIfSmalledFramed (Constant* tagged, GlobalVariable* ) 
{
    //extract flag. (1) create mask (1000..). (2) And (mask, tagged)  
    Constant* getFlag= ConstantExpr::getAnd(initVec, tagged);
    Constant* cond_isSmallFrame= ConstantExpr::getICmp (ICMP_EQ, getFlag, initVec);
    Constant* header?= ConstantExpr::getSelect (cond_isSmallFrame, 

    //if small-frame (1?), get header address (idx 0 0? create gep etc)
    
    // write in the header. store id and size. changes to headerT should be caught by assertion here.
    
    // then what should be changed to avoid duplicate updates?  
}*/

Constant* MyPrintPass::createHeaderInitializer (GlobalVariable* GV,
                                                unsigned Tid,
                                                unsigned gvsize)
{
    vector<Constant*> fields= { ConstantInt::get(HeaderTy->getElementType(0), Tid, true), 
                                ConstantInt::get(HeaderTy->getElementType(1), gvsize, true), 
                                Constant::getNullValue(HeaderTy->getElementType(2)) };
    return ConstantStruct::get(HeaderTy, fields);
}

GlobalVariable* MyPrintPass::doGlobalVariable (GlobalVariable * GV, 
                                    Function * F, 
                                    Instruction * insertBeforeMe, 
                                    Module & M)
{
    /*  Hook sig: void * FRAMER_global_variable 
        (void * gv, enum BASICType assignedTy, uint64_t numElems, unsigned numBytes) where
        GV is the location of GV, assignedTY is the typeID of allocated object in enumtype,
        numElems is #elements of Array (1 for a non-array), 
        numBytes is #num of bytes of allocated obj (numbytes of an element of an Array if it's array).
        currently inserBeforeMe is the 1st inst of 1st BB of main. (new BB)
     */
    errs()<<"\nGV::: "<<*GV<<"\n";
    if (GV->use_empty()) {
        errs()<<"\tuse list empty. skipping..\n";
        return nullptr;
    }
    
    unsigned FramerTyID;
    unsigned numElems;
    unsigned numBytesOfElemTy;
    unsigned theTotalSize;

    Type * assignedObjTy = 
        cast<PointerType>(GV->getType())->getElementType();
    Type* mytype=nullptr;
     
    if (ArrayType * arr = dyn_cast<ArrayType>(assignedObjTy)) {
        numElems = arr->getNumElements();
        Type* elemTyOfArray = arr->getElementType();
        mytype= PointerType::get(elemTyOfArray, GV->getType()->getPointerAddressSpace());
        errs()<<"mytype: "<<*mytype<<"\n";
        numBytesOfElemTy = (MyPrintPass::getBitwidth (elemTyOfArray))/8;
        FramerTyID = getFramerTypeID(elemTyOfArray);
    }
    else if (StructType* st=dyn_cast<StructType>(assignedObjTy)){
        numElems= 1;
        numBytesOfElemTy= (MyPrintPass::getBitwidth (assignedObjTy))/8; 
        FramerTyID= getFramerTypeID(assignedObjTy); 
        mytype=st->getElementType(0); 
        //get argument for getbitwidth. (it should be elemty)
    }
    else {
        errs()<<"Allocated global variable is vector typed! do something\n";
        exit(0);
    }
    theTotalSize = numElems * numBytesOfElemTy;
    
    //----- wrap an object into struct from here.
    vector<Type*> paddedObjTyList= {HeaderTy, assignedObjTy, OffByOneTy};
    
    StructType* paddedTy= StructType::create (M.getContext(), 
                                            paddedObjTyList, 
                                            "paddedStruct",
                                            true);
    // -- create initializer from here.
    Constant* GVinitializer;
    Constant* hdInitializer;
    bool isConstant=false;
    
    if (GV->hasInitializer()) {
        GVinitializer= GV->getInitializer();    
    }
    else {
        GVinitializer= Constant::getNullValue(assignedObjTy); 
    }
    
        // ?? difference between hasInitializer (above) and isConstant? forgot..  
    if (GV->isConstant()) {
        hdInitializer= createHeaderInitializer (GV, 
                                            FramerTyID,
                                            numElems*numBytesOfElemTy);
        isConstant=true;
    }
    else {
        hdInitializer= Constant::getNullValue(HeaderTy);
    }
    
     
    vector<Constant*> paddedObjlist={hdInitializer, //Constant::getNullValue(HeaderTy), 
                                     GVinitializer, 
                                     Constant::getNullValue(OffByOneTy)}; 
    Constant* paddedObj= ConstantStruct::get(paddedTy, paddedObjlist); 
    // --- create initializer upto here.

    //--- created/inserted wrapped object.
    GlobalVariable* paddedGV= new GlobalVariable(M,
                                                paddedTy, 
                                                GV->isConstant(),
                                                GV->getLinkage(),
                                                paddedObj,
                                                "paddedGV",
                                                GV);
    
    paddedGV->setAlignment(16); //set it as 16, since sometimes memset's alignment is 16.
    // the pointer to the original obj 
    vector<Value*> idx={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
    
    Constant* origObj= 
        ConstantExpr::getGetElementPtr (
                cast<PointerType>(paddedGV->getType()->getScalarType())->getContainedType(0u), 
                paddedGV,
                idx);
    assert(origObj->getType()==GV->getType() 
            && "Original GV's type must be equal to "
            "our new GV (field in padded struct)'s type! Exiting.. \n");
    //--- wrap an object upto here.
   
     
    // get tag for constantGV, and tag it.
    Constant* taggedConstantPtr= getTaggedConstantPtr(paddedGV, origObj, M);
    
    vector<Value *> arglist;
    
    pushtoarglist (insertBeforeMe, 
            F->getFunctionType()->getParamType(0), 
            taggedConstantPtr, //ptrtype //origObj, //GV, 
            arglist);

    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(1) , 
                    constructValueFromFunc(FramerTyID, F, 1), 
                    arglist); 

    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(2) , 
                    constructValueFromFunc (numElems, F, 2), 
                    arglist); 
                    //numElemsCons, arglist); 
    
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(3) , 
                    constructValueFromFunc(numBytesOfElemTy, F, 3), 
                    arglist);
     
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(4) , 
                    constructValueFromFunc(isConstant, F, 4), 
                    arglist);
    
    //-- delete later from here.

    vector<Value*> idx_base={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
    vector<Value*> idx_end={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 2)};
    Constant* mybase= 
        ConstantExpr::getGetElementPtr (
                cast<PointerType>(paddedGV->getType()->getScalarType())->getContainedType(0u), 
                paddedGV,
                idx_base);
    Constant* myend= 
        ConstantExpr::getGetElementPtr (
                cast<PointerType>(paddedGV->getType()->getScalarType())->getContainedType(0u), 
                paddedGV,
                idx_end);
    pushtoarglist (insertBeforeMe, 
                    F->getFunctionType()->getParamType(5), 
                    mybase, //ptrtype //origObj, //GV, 
                    arglist);
    pushtoarglist (insertBeforeMe, 
                    F->getFunctionType()->getParamType(6), 
                    myend, //ptrtype //origObj, //GV, 
                    arglist);
    
    // upto here. delete.
 
    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    
    //errs()<<"taggedConstantPtr type: "<<*taggedConstantPtr->getType()<<", orig ptr type: "<<*GV->getType()<<"\n";
    
    Instruction * typeRestoringPtrForReplacedUse = 
        castAndreplaceAllUsesWith (GV, taggedConstantPtr);
    
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
    
    if (typeRestoringPtrForReplacedUse!=nullptr){
        typeRestoringPtrForReplacedUse->insertAfter(CI);
        errs()<<"different type between orig and new ptr for GV\n";
        exit(0);
    }
    //insertCastToRestoreType (CI, castinglist);
     
    if(!GV->use_empty()) {
        for (Value::use_iterator it = GV->use_begin(), ie = GV->use_end(); it!=ie ; ++it) {
        }
    }
    /*if (isa<ArrayType>(assignedObjTy) || isa<StructType>(assignedObjTy)) {
        padObject (GV, M);
    }*/
    return GV;
}

/*
void MyPrintPass::doGlobalVariable (GlobalVariable * GV, Function * F, Instruction * insertBeforeMe, Module & M)
{
      Hook sig: void FRAMER_global_variable (void * gv, enum BASICType assignedTy, uint64_t numElems, unsigned numBytes) where
        GV is the base address of GV, assignedTY is the typeID of allocated object in enumtype,
        numElems is #elements of Array (1 for a non-array), 
        numBytes is #num of bytes of allocated obj (numbytes of an element of an Array if it's array).
    

    errs()<<"\nGV::: "<<*GV<<"\n";
    Value * baseAddrOfGV = GV;
    Type * assignedObjTy = cast<PointerType>(GV->getType())->getElementType();
    uint64_t numElems = getArraySizeforGV (GV);
    unsigned numBytesOfElemTy;

    if (numElems == 1) {
        numBytesOfElemTy = (MyPrintPass::getBitwidth (assignedObjTy))/8; //get argument for getbitwidth. (it should be elemty)
        errs()<<"GV non Array. #bytesofElemTy: "<<numBytesOfElemTy<<"\n";
    }
    else {
        //numBitsOfElemTy = MyPrintPass::getBitwidth (cast<ArrayType>(GV->getType())->..? //how can I get the type of global array?
        numBytesOfElemTy = (MyPrintPass::getBitwidth (cast<ArrayType>(assignedObjTy)->getElementType()))/8; //get argument for getbitwidth. (it should be elemty)
        errs()<<"GV Array. #bytesofElemTy: "<<numBytesOfElemTy<<"\n";
    }
    errs()<<"ElemTypeID: "<<GV->getType()->getTypeID()<<"\n";

    ConstantInt * numElemsCons          = ConstantInt::get(Type::getInt64Ty(M.getContext()), numElems);
    ConstantInt * numBitsofElemTyCons   = ConstantInt::get(Type::getInt32Ty(M.getContext()), numBytesOfElemTy); 
    
    vector<Value *> arglist;
    pushtoarglist ( insertBeforeMe, F->getFunctionType()->getParamType(0) , baseAddrOfGV, arglist);
    pushtoarglist ( insertBeforeMe, F->getFunctionType()->getParamType(1) , 
                                            constructValueFromFunc (assignedObjTy->getTypeID(), F, 1), arglist); //<<- bug!
    
    pushtoarglist ( insertBeforeMe, F->getFunctionType()->getParamType(2) , numElemsCons, arglist); 
    pushtoarglist ( insertBeforeMe, F->getFunctionType()->getParamType(3) , numBitsofElemTyCons, arglist);
    //pushtoarglist ( insertBeforeMe, F->getFunctionType()->getParamType(3) , endAddr, arglist);
    
    insertFunctionCall (F, insertBeforeMe, arglist);
 
}

*/

/* check if the GV is a string in printf function. */
bool MyPrintPass::isPrintfStr ( GlobalVariable * GV )
{
    //exit(0); 
    return (GV->hasPrivateLinkage() && GV->hasGlobalUnnamedAddr() && GV->isConstant());
   // && GV->getName().startswith(".str")); commented out since there are other strings named with something else.
}

bool MyPrintPass::hasConstructorAttribute (GlobalVariable * GV)
{
    return (GV->hasAppendingLinkage() && GV->getName().equals(StringRef("llvm.global_ctors"))); 
}

bool MyPrintPass::hasDestructorAttribute(GlobalVariable *GV)
{
    return (GV->hasAppendingLinkage() && GV->getName().equals(StringRef("llvm.global_dtors"))); 
}

void MyPrintPass::runOnGlobalVariables (Module &M)
{
    errs()<<"runOnGlobalVariables starting..\n";
      
    Function * hook = M.getFunction("FRAMER_forall_global_variable");
    if (hook == NULL) { return; }

    /* getting the place where the new instruction should be inserted to 
    Function::iterator it_fstBB = Func_main->begin(); 
    it_fstBB++; // the second BB of Main (BB in charge of global variables)
    Instruction * insertBeforeMe = --(it_fstBB->end());
    */
    
    Instruction * insertBeforeMe = getNextInst(initHookCall); 
    GlobalVariable* successorGV = &*M.global_begin();
    vector<GlobalVariable*> toBeRemovedList; 
   
    for (Module::global_iterator gi = M.global_begin(), ge=M.global_end(); gi!=ge ; ++gi) {
        
        //errs()<<"GI:: "<<*gi<<"\n";
        if (&*gi != &*successorGV) {
            //errs()<<"\tAdded by hook. skipping..\n";
            continue;
        }
        successorGV = getNextGV(&*gi, M);
        
        if (((&*gi)->getName()).startswith(prefix_of_hookGV_name)) {
            //errs()<<"\tSKIP: Hook Global value.\n";
        }
        else if ( isPrintfStr(&*gi)) {
            //errs()<<"\tSKIP: (printf str).\n";
        }
        else if (hasConstructorAttribute(&*gi) 
                || hasDestructorAttribute(&*gi)) {
            //errs()<<"\tSKIP: (ctor/dtor attr).\n";
        }
        else if (!isToBeTaggedType ((&*gi)->getValueType())){
            //errs()<<"\tSKIP: non-aggregated type or non-pointer.\n";
        }
        else {
            GlobalVariable* GVToBeRemoved= doGlobalVariable (&*gi, hook, insertBeforeMe, M);
            if (GVToBeRemoved!= nullptr) {
                toBeRemovedList.push_back(GVToBeRemoved); 
            }
        }
    }
    
    if (toBeRemovedList.size()>0) {
        for (vector<GlobalVariable*>::iterator ii=toBeRemovedList.begin();
            ii!= toBeRemovedList.end();++ii) {
            errs()<<"GV TO BE REMOVED: "<<**ii<<"\n";
            (*ii)->eraseFromParent();
        }
    }
}

void MyPrintPass::flagHooksDefinitionExists (Module &M)
{
    /* insert an entry (key: instruction number, value: exists/not exists) to the table. 
        Only instructions whose hook functions are provuded by users are processed at the iteration based on this table. */
    
    //TODO: insert  an entry to the table. unsigned int key: 0...2^8, bool hookexists.. ..(or just one int, and ...use POS, or SOP operation?) 
    size_t hookPrefixStrlen = StringRef(prefix_of_hookfunc_name).size();  
    
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
        if (((&*mi)->getName()).startswith(prefix_of_hookfunc_name)) {
            errs()<<"mi->getName():: "<<mi->getName()<<"\n";
            StringRef instKindInStr = (mi->getName()).drop_front(hookPrefixStrlen);
            
            errs()<<"\tHook Prefix Name: "<<instKindInStr<<"\n";
            
            /* memory access inst hooks */
            //if      (instKindInStr.equals("alloca"))        {HookDefinitionExists.insert (make_pair(Instruction::Alloca, true));}
            if  (instKindInStr.equals("alloca"))        
                //{HookDefinitionExists.insert (Instruction::Alloca);}
                {HookDefinitionExists[Instruction::Alloca]=1;}
            else if (instKindInStr.equals("store"))         
                {HookDefinitionExists[Instruction::Store]=1;}
            else if (instKindInStr.equals("load"))          
                {HookDefinitionExists[Instruction::Load]=1;}
            else if (instKindInStr.equals("getelementptr")) 
                {HookDefinitionExists[Instruction::GetElementPtr]=1; }
            
            /* call inst hook */
            else if (instKindInStr.equals("call_malloc")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[MallocIsCalled]=1; 
                errs()<<" moved malloc hook to separate obj! how come??\n";
                exit(0);
            }
            else if (instKindInStr.equals("call_free")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[FreeIsCalled]=1; 
            }
            /*else if (instKindInStr.equals("call_llvm_memcpy_src")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemCpySRCIsCalled]=1; 
            }
            else if (instKindInStr.equals("call_llvm_memcpy_dest")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemCpyDESTIsCalled]=1; 
            }*/
            else if (instKindInStr.equals("call_llvm_memtransfer")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemTransferIsCalled]=1; 
            }
            /*else if (instKindInStr.equals("call_llvm_memmove_src")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemMoveSRCIsCalled]=1; 
            }
            else if (instKindInStr.equals("call_llvm_memmove_dest")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemMoveDESTIsCalled]=1; 
            }
            */
            else if (instKindInStr.equals("call_llvm_memset")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[LLVMMemSetIsCalled]=1; 
            } 
            else if (instKindInStr.equals("call_external_function")){
                HookDefinitionExists[Instruction::Call]=1; 
                HookDefForCalledFuncExists[ExternalFuncIsCall]=1; 
            } 
            
            /* type conversion inst hooks */
            else if (instKindInStr.equals("bitcast"))   
                {HookDefinitionExists[Instruction::BitCast]=1;}
            else if (instKindInStr.equals("ptrtoint"))  
                {HookDefinitionExists[Instruction::PtrToInt]=1;}
            else if (instKindInStr.equals("inttoptr"))  
                {HookDefinitionExists[Instruction::IntToPtr]=1;}
            else if (instKindInStr.equals("sitofp"))    
                {HookDefinitionExists[Instruction::SIToFP]=1;}
            else if (instKindInStr.equals("fptosi"))    
                {HookDefinitionExists[Instruction::FPToSI]=1;}
            else if (instKindInStr.equals("trunc"))     
                {HookDefinitionExists[Instruction::Trunc]=1;}
            else if (instKindInStr.equals("zext"))      
                {HookDefinitionExists[Instruction::ZExt]=1;}
            else if (instKindInStr.equals("sext"))      
                {HookDefinitionExists[Instruction::SExt]=1;}
           
            /* binary operator hooks */
            else if (instKindInStr.equals("addop"))     {HookDefinitionExists[Instruction::Add]=1;}
            else if (instKindInStr.equals("subop"))     {HookDefinitionExists[Instruction::Sub]=1;}
            else if (instKindInStr.equals("mulop"))     {HookDefinitionExists[Instruction::Mul]=1;}
            
            else if (instKindInStr.equals("udiv"))      {HookDefinitionExists[Instruction::UDiv]=1;}
            else if (instKindInStr.equals("sdiv"))      {HookDefinitionExists[Instruction::SDiv]=1;}
            else if (instKindInStr.equals("lshr"))      {HookDefinitionExists[Instruction::LShr]=1;}
            
            else { 
                errs()<<"\tno hook provided!! Skipping..\n";
            } 

        }
    }
}

void MyPrintPass::create1stBBOfMain (Module &M)
{
   fstBBOfMainFunction->splitBasicBlock(&*fstBBOfMainFunction->begin(), "fstBBOfMain");
}

void MyPrintPass::doInitFuncHook (Module &M)
{
    Function * F = M.getFunction("do_initializing");
    assert(F!= nullptr && "do_initializing empty!\n");
    Instruction* insertBeforeMe = &*(Func_main->begin()->begin());
    Value * numStructTy = constructValueFromFunc (structTyCount, F, 0);
    Value * addressOfStructTable = StructTyTable;
    
    vector<Value *> arglist;
    pushtoarglist (insertBeforeMe, F->getFunctionType()->getParamType(0), numStructTy, arglist);
    pushtoarglist (insertBeforeMe, F->getFunctionType()->getParamType(1), addressOfStructTable, arglist);

    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    // before any insertion of new insts, replace all uses.
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
    
    initHookCall= CI;    
}
    
void MyPrintPass::assertBasicTyTable(Module &M)
{
    basicTypeTable= M.getGlobalVariable ("FRAMER_BasicTy_table");
    assert(basicTypeTable!=nullptr && "ERROR: cannot basic type table. \n");
    assert((Type::VectorTyID+1)==llvmbasicTyCount && "llvm's typeID enum has been updated?? check the count of enum, typeid\n"); 
    //assert((Type::TypeID).GetNames(typeof(Type::TypeID)).Length==llvmbasicTyCount && "llvm's typeID enum has been updated?? check the count of enum, typeid\n"); 
}

void MyPrintPass::createUserStructTyList (Module &M)
{
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    for(vector<StructType*>::iterator it = temp.begin(), ie=temp.end();it!=ie;++it)
    {
        StringRef str=(*it)->getName();
        if (str.startswith("struct.FRAMER_")){
            continue; //Framer's struct type is skipped.

        }
        allStructTyList.push_back(*it); //create constant. then push?
    }
    structTyCount = allStructTyList.size(); 
    //contains only used one. includes substruct, anonymous struct.  
}

unsigned MyPrintPass::getMaxFieldCountOfStruct()
{
    unsigned maxcount=0;
    for (vector<StructType*>::iterator it=allStructTyList.begin(), ie=allStructTyList.end();it!=ie;++it) {
        unsigned count = (*it)->getNumElements();
        if (count > maxcount) {
            maxcount = count;
        }
    }
    errs()<<"final max count:: "<<maxcount<<"\n";
    return maxcount; 
}

void MyPrintPass::createStructTypeTable(Module &M) 
{
    unsigned max_field_count= getMaxFieldCountOfStruct();
    Type* structsizeT =  IntegerType::getInt32Ty (M.getContext()); 
    ArrayType* FieldsArrayT=  ArrayType::get(IntegerType::get(M.getContext(),32), max_field_count);
    vector<Type*> onestructTylsit = {structsizeT, FieldsArrayT}; 
    StructType* oneStructT = StructType::create(
        M.getContext(), onestructTylsit, StringRef("FRAMER_oneStryctTy")); 
    
    vector<Constant*> StructTypeVector;
    for (vector<StructType*>::iterator it=allStructTyList.begin(), ie=allStructTyList.end();it!=ie;++it) {
        uint64_t temp = (dlayout->getTypeSizeInBits(*it)); 
        unsigned structsize = (unsigned)temp; 
        assert(temp == (uint64_t)structsize && "type conversion (uint64_t->unsigned) failed.\n");
        int framertyid;
        vector<Constant*> fields;
       
        Constant * fieldconst; 
        StructType::element_iterator elemit = (*it)->element_begin(); 
        unsigned fieldindex= 0;
        
        for(unsigned i=0 ; i< max_field_count ; i++) {  
            if(fieldindex >= (*it)->getNumElements() ) {
                framertyid=-1; 
            }
            else {
                framertyid= (int)getFramerTypeID(*elemit);   
            }
            fieldconst = ConstantInt::get(IntegerType::get(M.getContext(), 32),(unsigned)framertyid); 
            fields.push_back(fieldconst);
            assert(fields.size() <= max_field_count && "fields vector pushing wrong!\n");
            elemit++;
            fieldindex++;
        }
        Constant * structsizeconst = 
            ConstantInt::get(
                            IntegerType::get(M.getContext(), 32), 
                            structsize, 
                            true);  
        Constant * onestructarrayconst = ConstantArray::get(FieldsArrayT,fields);
        
        vector<Constant*> onestruct = {structsizeconst, onestructarrayconst};
        Constant* onestructconst = ConstantStruct::get(oneStructT, onestruct); 
        
        StructTypeVector.push_back(onestructconst);
        errs()<<"Struct info inserted: "<<*onestructconst<<"\n";
    }
    ArrayType* StructsT=    ArrayType::get(oneStructT, StructTypeVector.size());
    Constant* structTableArray = ConstantArray::get(StructsT, StructTypeVector);
     
    GlobalVariable* pointerTyTable = M.getGlobalVariable(StringRef("FRAMER_PointerTy_Table"));
    
    assert((pointerTyTable!=nullptr) && "global pointerTyTable does not exist.Check pass code..\n");
    StructTyTable = new GlobalVariable (M, 
                                        StructsT, //StructTyArr, 
                                        true, 
                                        GlobalValue::ExternalLinkage,
                                        structTableArray,//nullStructTbl,
                                        "FRAMER_StructTyTable",
                                        pointerTyTable);
}

void MyPrintPass::doInitialSetup (Module &M)
{
    errs()<<"itializing starting..\n";
    dlayout = &(M.getDataLayout());
   
    Func_main               = M.getFunction ("main");
    assert(Func_main!=nullptr && "main empty!\n");
    fstBBOfMainFunction     = &*Func_main->begin();
    fstInstOfMainFunction   = &*((Func_main->begin())->begin());
    assert(fstInstOfMainFunction!= nullptr && "fstInstOfMainFunction empty!\n"); 
    HeaderTy= M.getTypeByName(StringRef("struct.FRAMER_Headers"));
    OffByOneTy= Type::getInt8Ty (M.getContext());
    
    assert((HeaderTy!= nullptr)
        && "HeaderTy is empty. Check if FRAMER_Headers is re-named or ever used. \n");

    const StructLayout * headerTyLayout= dlayout->getStructLayout (HeaderTy);
    headerTySize = headerTyLayout->getSizeInBytes (); 
    errs()<<"headerTySize: "<<headerTySize<<"\n";
    headerTyAlign = headerTyLayout->getAlignment();
    
    assert (headerTySize==16 && "check headerTy size.\n"); 
    assert (!headerTyLayout->hasPadding() && "type must be packed!!\n"); 
    //assert (headerTyAlign==16 && "HeaderTy align must be 16\n"); 
    //--> alignment is set for each alloca. for GV..no

    assertBasicTyTable(M); 
    createUserStructTyList(M);
    createStructTypeTable(M); 
    flagHooksDefinitionExists(M);
    create1stBBOfMain (M); // BB processing global vars.
    
    errs()<<"doinitialfunc\n";
    doInitFuncHook(M);  
}

bool MyPrintPass::isHookFamilyFunction (Function * F ) 
{ /* False when this function is from static lib whose functions are added to target */ 
    StringRef funcName = F->getName();

    if ( funcName.startswith(prefix_of_hookfunc_name)  //if it's hook func
        || funcName.startswith ("FRAMER_") 
        || funcName.startswith(prefix_of_supplementary_funcName)
        || funcName.equals( StringRef("do_initializing"))) 
        {
          //or sumplementary hook
        
        return true; 
    }
    else {
        return false;
    }
}


bool MyPrintPass::runOnBasicBlock (BasicBlock &BB, Module &M)//, PostDominatorTree & postDT) 
{
    /* successorInst is introduced to store the original next instruction distinguished from insts added by the pass. */ 
    Instruction * successorInst = &*BB.begin();
    vector<Instruction*> toBeRemovedList; 
    for (BasicBlock::iterator it = BB.begin(), ie = BB.end();it != ie; ++it) {
        errs()<<"\nInst:::\t"<<*it<<"\n"; 

        if (&*it != &*successorInst) {
            errs()<<"\tadded by hook? skipping..\n";
            continue;
        }
        successorInst = getNextInst(&*it);
        
        if (AllocaInst * AI = dyn_cast<AllocaInst>(it) ){
            if (!HookDefinitionExists[Instruction::Alloca]) {
                errs()<<"No hooks provided for alloca inst. Skipping..1\n";
                continue;
            }
            Instruction* toBeRemoved= doAllocaInst (AI, successorInst, M);//, postDT);
            if (toBeRemoved!= 0x0) { 
                toBeRemovedList.push_back(toBeRemoved);
            }
        }
        else if (LoadInst * LI = dyn_cast<LoadInst>(it) ) {
          /*  TODO: this is an optimization.. let it be in userhook.c
            if (PointersAreTagged) {
                restoreModifiedPtr (LI);
            }
          */  
            if (!HookDefinitionExists[Instruction::Load]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            doLoadInst (LI, successorInst, M);
        }
        else if (StoreInst * SI = dyn_cast<StoreInst>(it) ) {
            if (!HookDefinitionExists[Instruction::Store]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            doStoreInst (SI, successorInst, M);
        }
        else if (GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst>(it)) {
            errs()<<"entering GEP..?\n";
            if (!HookDefinitionExists[Instruction::GetElementPtr]) {
                errs()<<"No hooks provided for this inst. Skipping..4\n";
                continue;
            }
            doGetElementPtrInst (GEP, successorInst, M);
        }

        else if (CallInst * CI = dyn_cast<CallInst>(it)) {
            if (!HookDefinitionExists[Instruction::Call]) {
                errs()<<"No hooks provided for Call (llvm.memcpy) inst. Skipping..\n";
                continue;
            }
            Instruction * toBeRemoved = doCallInst (CI, successorInst, M);
            if (toBeRemoved!= 0x0) { 
                toBeRemovedList.push_back(toBeRemoved);
            }
        }
        
        else if (BitCastInst * BCI = dyn_cast<BitCastInst>(it)){
            if (!HookDefinitionExists[Instruction::BitCast]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            doBitCastInst (BCI, successorInst, M);        
        }
        else if (PtrToIntInst * PTI = dyn_cast<PtrToIntInst>(it)) {
            if (!HookDefinitionExists[Instruction::PtrToInt]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            doPtrToIntInst (PTI, successorInst, M);
        }
        else if (IntToPtrInst * ITP = dyn_cast<IntToPtrInst>(it)) {
            //errs()<<"implemented Codes, but not is not tested. Do it. probably correctly witten.\n";
            //exit(0);
            doIntToPtrInst (ITP, successorInst, M);
        }
        else if (SIToFPInst * STF = dyn_cast<SIToFPInst>(it)) {
            if (!HookDefinitionExists[Instruction::SIToFP]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            
            doSIToFPInst (STF, successorInst, M);
        }
        else if (FPToSIInst * STF = dyn_cast<FPToSIInst>(it)) {
            if (!HookDefinitionExists[Instruction::FPToSI]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            }
            
            doFPToSIInst (STF, successorInst, M);
        }
        
        else if (TruncInst * TR = dyn_cast<TruncInst>(it)) {
            if (!HookDefinitionExists[Instruction::Trunc]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            } 
            
            doTruncInst (TR, successorInst, M);
        }
        else if (SExtInst * SI = dyn_cast<SExtInst>(it)) {
            if (!HookDefinitionExists[Instruction::SExt]) {
                errs()<<"No hooks provided for this inst. Skipping..\n";
                continue;
            } 
            doSExtInst (SI, successorInst, M);
        }
        //else if (Instruction::Mul * MO = dyn_cast<Instruction::Mul>(it)) {
        else if (OverflowingBinaryOperator * BO = dyn_cast<OverflowingBinaryOperator>(it)) {
            doOverflowBinaryOp (BO, successorInst, M);
        }
        else if (PossiblyExactOperator * PEO = dyn_cast<PossiblyExactOperator>(it)) {
            doPossiblyExactOp (PEO, successorInst, M);
        }
        else {
            //errs()<<">>>> Else: "<<*it<<"\n";
            //TODO: add other cases such as cast.
            //errs()<<"else: "<<*it<<"\n";
            ;
        }

    }
    // remove existing instruction (such as x=call malloc(n)..) 
    errs()<<"to be removed size: "<<toBeRemovedList.size()<<"\n"; 
    if (toBeRemovedList.size()>0) {
        for (vector<Instruction*>::iterator ii=toBeRemovedList.begin(), ie= toBeRemovedList.end();
            ii!=ie; ++ii) {
            errs()<<"TO BE REMOVED: "<<**ii<<"\n";
            (*ii)->eraseFromParent();
        } 
    }
    return false;
}

bool MyPrintPass::isLeafOfDomTree (BasicBlock* bb, PostDominatorTree & postDT)
{
    bool isLeaf=true;
    TerminatorInst *TI= bb->getTerminator();
    for (unsigned i=0, NSucc = TI->getNumSuccessors(); i<NSucc; ++i) {
        BasicBlock *Succ = TI->getSuccessor(i);
        if (postDT.properlyDominates(bb, Succ)) {
            isLeaf=false;   // what if it is itself? 
            break;
        }
    }
    return isLeaf;
}
void MyPrintPass::insertEpilogueOfFunc (Instruction* tagged, 
                                        Module &M)//, 
                                        //PostDominatorTree & postDT)
{
    errs()<<"Epilog:: "<<*tagged<<"\n";

    vector <Value*> arglist= {tagged};
    CallInst * CI = CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), 
                                    arglist, 
                                    "");

    Function* F= tagged->getFunction(); 
    BasicBlock* allocaBB= tagged->getParent();
    Function::iterator mainit= Func_main->begin(); 
    advance(mainit, 1);
    if (allocaBB== &(F->front())
        || (F==Func_main && &*mainit==allocaBB)) {
        //assert. alloca should (post?)dominates lastBB or all the uses of alloca (post)dominates lastbb?  
        Function::iterator lastbb= F->end();
        --lastbb;
        TerminatorInst* lastinst= lastbb->getTerminator();
        
        assert(isa<TerminatorInst>(lastinst) && "the last inst is not terminalinst! exiting..\n");
        CI->insertBefore(&*lastinst);
    }
    else {
        Value* scopeStart=nullptr; //call llvm.stacksave
        Value* mySavedStack= nullptr; 
        TerminatorInst* insertBeforeMe=nullptr;

        // get scopestart 
        unsigned stackSaveCount=0;
        for (BasicBlock::iterator it= allocaBB->begin(), ie=allocaBB->end(); it!=ie; ++it) {
            if (CallInst * ci= dyn_cast<CallInst>(&*it)) {
                if (ci->getCalledFunction()->getName().equals("llvm.stacksave")) {
                    scopeStart= &*it;
                    stackSaveCount++;
                }
            }
            else if (StoreInst* si= dyn_cast<StoreInst>(it)) {
                if (scopeStart==nullptr) {continue;}
                if (scopeStart==si->getOperand(0)) {
                    if (isa<AllocaInst>(si->getPointerOperand()->stripPointerCasts())) {
                        mySavedStack= si->getPointerOperand()->stripPointerCasts();
                    }
                    else if (CallInst* ci= dyn_cast<CallInst>(si->getPointerOperand()->stripPointerCasts())) {
                        if (ci->getCalledFunction()->getName().equals("FRAMER_forall_store")) {
                            mySavedStack= (ci->getArgOperand(0))->stripPointerCasts();           
                        }
                        else {errs()<<"??? not hook familly?\n"; exit(0); }
                    }
                    else { errs()<<"what case is this in epilogue?\n"; exit(0);} 
                }
            }
            else {;}
        }
        assert (stackSaveCount==1 && scopeStart !=nullptr && mySavedStack != nullptr
                && "finding stacksave failed..\n");
        errs()<<"got scopstart\n"; 
        // get scope_end
        for (Function::iterator it=F->begin(), ie= F->end(); it!=ie; ++it) {
            unsigned stackrestorecount=0;
            for (BasicBlock::iterator bit= (&*it)->begin(), bie=(&*it)->end(); bit!=bie; ++bit) {
                errs()<<"bit: "<<*bit<<"\n";
                if (!isa<CallInst>(&*bit)) {
                    continue; 
                }
                CallInst * restore=cast<CallInst>(&*bit);     
                if (!(restore->getCalledFunction()->getName()).equals("llvm.stackrestore")){ 
                    continue;
                }
                if (LoadInst * argli= dyn_cast<LoadInst>(restore->getArgOperand(0))) { //arg, not hooked.
                    assert (restore->getNumArgOperands ()==1
                            && "saveorrestore's arg num is more than 1! CHECK. exiting..\n");  
                    if (argli->getPointerOperand()== mySavedStack) {
                        insertBeforeMe= restore->getParent()->getTerminator(); // -->>>  
                        stackrestorecount++;  
                    }
                    else {
                        errs()<<"mysavedstack::: "<<*mySavedStack<<"\n";
                        errs()<<"how getting here: "<<*argli->getPointerOperand()<<"\n"; //-->>>
                        exit(0);
                    }
                }
                else if (CallInst* ci= dyn_cast<CallInst>(restore->getArgOperand(0)->stripPointerCasts())) {
                    if (ci->getCalledFunction()->getName().equals("FRAMER_forall_load")
                        && (ci->stripPointerCasts() == mySavedStack)) {
                        insertBeforeMe= restore->getParent()->getTerminator();  //--->>>
                        stackrestorecount++;  
                    }
                    else {errs()<<"??? not hook familly?\n"; exit(0); }
                }
                else {errs()<<"weird case..\n"; exit(0);}
            }
            assert(stackrestorecount<2 && "stackrestorecount is above 1?? then reimplement?\n");
        }
        assert(insertBeforeMe!=nullptr && "insertbeforeme in reset_alloca is null!\n");
        CI->insertBefore(insertBeforeMe);
    }
    /*
    // when alloca post-dominates bb_x, alloca's all use post-domintes bb_x also? i think so... 
    DomTreeNode * allocNode= postDT.getNode(tagged->getParent());  
    //errs()<<"alloc node: "<<allocNode<<"\n";
    errs()<<"alloc BB: "<<*(tagged->getParent())->begin()<<"\n"; 
    BasicBlock * immeRoot= postDT.findNearestCommonDominator(tagged->getParent(), tagged->getParent());  
    errs()<<"immeRoot: "<<*(immeRoot->begin())<<"\n";
    */
}

/*
void MyPrintPass::insertEpilogueOfFunc (AllocaInst* tagged, Module &M, DominatorTree & FDomTree)
{
    // at the memomtn, resetting entries for big-framed alloca.
    
    Function* F= tagged->getFunction(); 
    Function::iterator lastbb= F->end();
    --lastbb;
    BasicBlock::iterator lastinst = lastbb->end();
    --lastinst;
    
    vector<BasicBlock*> selected; 
    
    if (((F->front())->getTerminator()).dominates(tagged->getParent())) { // F's entryBB dominates allocaBB
        //TODO: insert reset at the end BB? exit to check what case this is.    
        errs()<<"lastinst: "<<*lastinst<<"\n"; 
        
        assert (FDomTree.dominates(tagged, lastbb) 
                && "FRAMER: alloca in the entryBB does not dominate"
                " the last basicblock of the function. Exiting..\n");
        assert(isa<TerminatorInst>(lastinst) && "the last inst is not terminalinst!exiting..\n");

        CI->insertBefore(&*lastinst);
    }
    else if (isLeafOfDomTree(tagged->getParent())) { //allocabb is the leaf of domtree
        //TODO: insert reset in the same BB. (after the last use of alloca?)    
        selected.push_back(tagged->getParent());
    }
    else { //allocabb is neither leaf nor entry 
        list<BasicBlock*> trav ={tagged->getParent()};
        while (!trav.empty()) {
            BasicBlock* head= trav.pop_front();  
            TerminatorInst *TI= head->getTerminator();
            
            for (unsigned i=0, NSucc = TI->getNumSuccessors(); i<NSucc; ++i) {
                BasicBlock *Succ = TI->getSuccessor(i);
                vector<BasicBlock*>::iterator it= 
                    find(trav.begin(), trav.end(), Succ); 
                if (it != trav.end()) { //already in the list.
                    continue;
                }
                if (isLeafOfDomTree()) {
                    selected.push_back(Succ);
                }
                trav.push_back(Succ);
            }
        }

     }
     //correct followings
    vector <Value*> arglist= {tagged};
    CallInst * CI = CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), 
                                    arglist, 
                                    "");
    for (BasicBlock::iterator it=selected.begin(), ie=selected.end(); it!=ie;it++){
        TerminatorInst* insertBeforeMe = (&*it)->getTerminator(); 
        CI->insertBefore(&*insertBeforeMe); 
    }
}
*/

void MyPrintPass::doExitingMain (Module &M)
{
    Function::iterator lastbb= Func_main->end();
    --lastbb; 
    BasicBlock::iterator lastinst= lastbb->end();
    --lastinst; 
    vector <Value*> arglist;
    CallInst * CI = CallInst::Create(M.getFunction ("FRAMER_exit_main"), 
                                    arglist, 
                                    "");
    CI->insertBefore(&*lastinst);
}

bool MyPrintPass::runOnFunction(Function &F, Module &M)//, PostDominatorTree & postDT)
{
    errs()<<"\tProcessing...\n";
    
    //PostDominatorTree & postDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree(); 
    
    for (Function::iterator fi = F.begin(), fe = F.end(); fi!=fe ; ++fi ){
        if (&*fi == &*Func_main->begin() && (F.getName() == "main")) {
            //skip // since it is basicblock for global variable processing hooks.     
            continue; 
        }
        MyPrintPass::runOnBasicBlock(*fi, M);//, postDT); 
    }
    errs()<<"after func iteration\n";
    if (F.getName().equals("main")) {
        doExitingMain(M);
    }
    errs()<<"after do exiting main\n";

}

bool MyPrintPass::runOnModule (Module &M) 
{
    memfispasscounter++;
    
    //PostDominatorTree & postDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree(); 
    
    doInitialSetup (M);
    runOnGlobalVariables(M); 
    errs()<<"runonglobal\n"; 
    /* processing each instruction for each BB for each function */
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
        //errs()<<"Function:  "<<mi->getName()<<"\t"; 
        
        if ( isHookFamilyFunction (&*mi)) {
        //    errs()<<"\t::Hook.Skipping..\n"; 
            continue;
        }
        if ((&*mi)->isDeclaration()) {
        //    errs()<<"\t::decl.skipping..\n"; 
            continue; 
        }
      //  PostDominatorTree & postDT = 
      //      getAnalysis<PostDominatorTreeWrapperPass>(*mi).getPostDomTree(); 
        
        runOnFunction(*mi, M);//, postDT);
        errs()<<"after run on all function\n";
    }
}

static void registerMyPrintPass(const PassManagerBuilder &,
                           legacy::PassManagerBase &PM) {
    PM.add(new MyPrintPass());
}
/*
static RegisterStandardPasses
    RegisterMyPrintPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                        registerMyPrintPass);
static RegisterStandardPasses
    RegisterMyPrintPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                        registerMyPrintPass); 
*/
/*
static void AddStandardLinkPasses(legacy::PassManagerBase &PM) {
   builder.VerifyInput = true;
   //if (DisableOptimizations)
   //  Builder.OptLevel = 0;
 
   //if (!DisableInline)
   //  Builder.Inliner = createFunctionInliningPass();
   builder.populateThinLTOPassManager(PM);
}*/
