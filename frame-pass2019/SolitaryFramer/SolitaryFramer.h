
//==------ SolitaryFramer.h --------==//

#ifndef SOLITARYFRAMER_H_
#define SOLITARYFRAMER_H_

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
#include "../../llvm-4.0.0.src/lib/IR/ConstantsContext.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/PostDominators.h" 
#include "llvm/Support/CommandLine.h"
#include "llvm/PassRegistry.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include "llvm/IR/LegacyPassManager.h"


//#include "llvm/Transforms/frame-pass.h"

//using namespace llvm;
using namespace std;

//namespace llvm {
struct SolitaryFramer : public ModulePass {
  public:
    static char ID;
    SolitaryFramer() : ModulePass(ID) {
        //llvm::initializeSolitaryFramerPass(*PassRegistry::getPassRegistry());    
    }
    //virtual ~SolitaryFramer() {}

    virtual bool runOnModule(Module &M);
    virtual bool runOnFunction (Function &F, Module &M); 
    virtual bool runOnBasicBlock (BasicBlock &BB, 
                                  DominatorTree & dt, 
                                  AAResults & AA,
                                  //vector <GetElementPtrInst*> & LocalUnions,
                                  vector <AllocaInst*> & LocalUnions,
                                  Module &M);
    
    StringRef getPassName() const override {
      return "SolitaryFramer Pass";
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        //AU.addRequired<DominatorTree>(Function & F);
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>(); 
    }

  protected:
      //Instruction * getNextInst (Instruction * Inst);
      GlobalVariable * getNextGV (GlobalVariable * GV, Module &M); 

      //bool isHookFamilyFunction   (Function * F); 

      void insertCastInstForArg   (Instruction * insertBeforeMe, 
              vector<Value*> & arglist);
    
      Instruction* createCastInst (Value * val, Type * Ty);
      /*void pushtoarglist (Instruction * insertBeforeMe,//2017.9.10. changed from insertAfterMe 
              Type * paramTy, 
              Value * arg, 
              vector<Value*> & arglist,
              Module & M); */

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
      void insertEpilogueOfFunc (Instruction* tagged, Module &M);
                                //, PostDominatorTree & postDT);  
      void doInitialSetup     (Module &M);

      void create1stBBOfMain          (Module &M); 
      void flagHooksDefinitionExists  (Module &M);
      void assertBasicTyTable         (Module &M);
      void runOnGlobalVariables       (Module &M);       
      void padObject                  (Value* obj, Module &M);
      unsigned getFramerTypeID        (Type* ty);
      void getFramerReplacement       (Use* use, Constant* untagged, Constant* tagged);
      
      int getUserIntegerTypeID   (IntegerType* ty);
      Constant* constructAddressValue (Module &M, GlobalVariable* tab, unsigned subindex);
      //Constant* getFramerTyEntryAddress(Module &M, unsigned ftid);
      int insertLiteralToStructList   (StructType* ty);
      int  getUserStructTypeID        (StructType* ty);
      void createStructTypeTable      (Module &M); 
      void createUserStructTyList     (Module &M);
      unsigned  getMaxFieldCountOfStruct   ();
      bool isFramerIntID              (unsigned id);
      bool isFramerStructID           (unsigned id);
      Value* tagFramerTyID            (Value * val, 
                                       unsigned id, 
                                       Module &M,
                                       Instruction * valsUser); 

      bool hasConstructorAttribute (GlobalVariable * GV);
      bool hasDestructorAttribute  (GlobalVariable * GV);
     // bool isPrintfStr             (GlobalVariable * GV);

      Constant* tagConstantPtr (Constant* ptr, 
              Constant* tag, 
              Constant* flag, 
              Module & M); 
      Constant* getPaddedEndInt (GlobalVariable* paddedGV, Module & M); 
      Constant* getLogFrameSize (Constant* base, Constant* end, Module & M); 
      Constant* getOffset (Constant* base, Module & M); 
      Constant* getTaggedConstantPtr (GlobalVariable* basePadded,
              Constant* origPtr,
              Module & M); 
      Constant* createHeaderInitializer (GlobalVariable* GV,
              unsigned Tid,
              unsigned numElems,
              unsigned numBytesOfElemTy);
          //unsigned gvsize);

      GlobalVariable* doGlobalVariable (GlobalVariable * GV, 
                                  Function * F, 
                                  Instruction * insertBeforeMe, 
                                  Module & M,
                                  set<tuple<GlobalVariable*, Constant*, Constant*>> & inits);
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

      //Constant* getNewConstExpr (Constant *CE, Constant* newGV, GlobalVariable* origGV);
      Constant* getNewConstExpr (Use * use, Constant* newGV, 
                        GlobalVariable* origGV, vector <Constant*>& oplist);
      //ConstantAggregate* getNewConstAggr(int opnum, Constant * CA, Constant * newGV);
      //Constant * getReplacement (Use* use, Constant* newGV, GlobalVariable * origGV);
      //unsigned getopidx (User *user, Use * op);
      //void handleUsesOfGV(Use* use, Constant* tagged, Constant* untagged, GlobalVariable * origGV);
     // void castAndreplaceAllUsesWithForGV (GlobalVariable * originalGV, 
     //                                      Constant * taggedGV,
     //                                      Constant * untaggedGV);
 
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

      unsigned getBitwidth    (Type * allocatedType);
      //unsigned getPrimTyBits  (unsigned Typeid);
      //uint64_t getBitwidthOfStruct ( StructType * STy );

      size_t getNewAlignment (size_t totalsize);
      size_t pow2roundup (size_t x);

      /* process memory access instruction */
      Instruction* doAllocaInst           (AllocaInst * AI, 
              Instruction * successorInst,
              //vector <GetElementPtrInst*> & LocalUnions, 
              vector <AllocaInst*> & LocalUnions, 
              Module & M);
      
      Instruction* doPrimitiveAllocaInst  (AllocaInst * AI, 
              Instruction * successorInst, 
              //vector <GetElementPtrInst*> & LocalUnions, 
              vector <AllocaInst*> & LocalUnions, 
              Module & M);
      
      Instruction* doArrayAllocaInst      (AllocaInst * AI, 
              Instruction * successorInst, 
              bool arraykind, 
              //vector <GetElementPtrInst*> & LocalUnions, 
              vector <AllocaInst*> & LocalUnions, 
              Module & M);
      
      void doLoadInstForSpaceMiu (LoadInst * LI, 
                       Instruction * successorInst, 
                       DominatorTree & dt, 
                       AAResults & AA,
                       vector <AllocaInst*> & ais,
                       Module & M);

      void doLoadInst (LoadInst * LI, 
                       Instruction * successorInst, 
                       DominatorTree & dt, 
                       AAResults & AA, 
                       Module & M);

      void doStoreInstForSpaceMiu (StoreInst * SI, 
                       Instruction * successorInst, 
                       DominatorTree & dt, 
                       AAResults & AA,
                       vector <AllocaInst*> & ais,
                       Module & M);

      void doStoreInst (StoreInst * SI, 
                        Instruction * successorInst, 
                        DominatorTree & dt, 
                        Module &M);

      void doGetElementPtrInst    (GetElementPtrInst * GEP, Instruction * successorInst, Module &M);

      /* process Call Instruction */
      Instruction* doCallInst (CallInst * CI, 
                               Instruction * successorInst,
                               AAResults & AA, 
                               vector <AllocaInst*> & LocalUnions,
                               Module &M);
      Instruction* doCallInstMalloc(CallInst * CI,Instruction * successorInst, Module & M);
      Instruction* doCallInstFree (CallInst * CI, Instruction * successorInst, Module & M);

      //void doCallLLVMMemTransfer  (CallInst * CI, Instruction * successorInst, Module &M);            
      void doCallLLVMMemTransfer (CallInst * CI,
                                Instruction * sucIns, 
                                AAResults & AA,
                                vector <AllocaInst*> & ais,
                                Module &M);

      void doCallLLVMMemSet       (CallInst * MSI,Instruction * successorInst, Module &M);            
      void doCallmem___           (CallInst * CI, Instruction * successorInst, Module &M);
      void doCallstrcpy           (CallInst * CI, Instruction * successorInst, Module &M); 
      void doCallstrn___          (CallInst * CI, Instruction * successorInst, Module &M, unsigned temp);  //delte the last arg later!
      void doCallstrchr           (CallInst *CI,Instruction *successorInst, Module &M); 
      void doCallstrlentemp       (CallInst *CI,Instruction *successorInst, Module &M); 
      void doCallExternalFunc     (CallInst * CI, Instruction * successorInst, Module &M);

      /* process Cast Instruction */
      void doBitCastInst  (BitCastInst * BCI, 
                           Instruction * successorInst,
                           AAResults & AA,
                           vector <AllocaInst*> & ais, 
                           Module &M);
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
      //void doOverflowBinaryOp (OverflowingBinaryOperator * OFO, Instruction * successorInst, Module & M);
      void doBinaryOp (BinaryOperator * OFO, Instruction * successorInst, Module & M);
      void doSubOp    (SubOperator * SO, Instruction * successorInst, Module &M);
      void doMulOp    (MulOperator * MO, Instruction * successorInst, Module &M);
      //void doAddOp    (AddOperator * AO, Instruction * successorInst, Module &M);
      void doAddOp    (BinaryOperator * OFO, Instruction * successorInst, Module &M);

      bool isItsUser (Value * useuser, User * useruser);
      Value * getOriginalAlloca (Value* ptr); 
      bool isToBeTaggedType (Type* t);
      void handleArgAttr (CallInst * CI, Module & M);
//      bool isSafePtr (Value * p);
      bool isuntaggedPtr(Value * ptrop);
      GlobalVariable * createGVHoldingTag (Constant * origGV, 
            Constant * tagged, Module & M, GlobalVariable * paddedGV, 
            GlobalVariable * GVToDel);

      //bool isHookedAllocaOrGV(Value * p);
      //bool isSafeAccess(Value * op_, DominatorTree & dt);
      //bool isStaticInBound (unsigned offset, unsigned sizeToAccess, unsigned totalsize);
      //unsigned getTotalSize(GEPOperator * gep);
      bool checkSafeWithDomTree (Value * op, DominatorTree & dt);
      //unsigned getStaticOffset (GEPOperator * gep);
      bool isInbound (GetElementPtrInst * gep);
      Value* getAssignment(LoadInst * LI, DominatorTree & dt);
       
      //bool isTaggedPointer        (Value* ptrop); 
      
      void restoreModifiedPtr (LoadInst * LI); 
      void castAndreplaceUsesOfWithBeforeInst (Instruction * user, Value * from, Value * toThis);
      Type* getResultTypeOfMalloc (CallInst * CI);


}; // end of struct SolitaryFramer


//} // end or namespace llvm

#endif
