
//==------ FramerDelSafeAccess.h --------==//

#ifndef FRAMER_DelSafeAccess_H_
#define FRAMER_DelSafeAccess_H_

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
#include "../../../../../llvm-4.0.0.src/lib/IR/ConstantsContext.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/PassRegistry.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/AliasSetTracker.h"


using namespace llvm;
using namespace std;

namespace llvm {
struct FramerDelSafeAccess : public ModulePass {
  public:
    static char ID;
    FramerDelSafeAccess() : ModulePass(ID) {}

    virtual bool runOnModule(Module & M);
    virtual bool runOnFunction (Function & F,
                 //               vector <vector<Value*>> & EC, 
                              //  DominatorTree * DT,
                              //  AAResults & AA, 
                                Module & M);
    
    virtual bool runOnBasicBlock(BasicBlock & BB, 
                  vector <vector<CallInst*>> & EC,
                  DominatorTree * DT, 
                  AAResults & AA,
                  AliasSetTracker * AST, 
                  Module & M);
    
    StringRef getPassName() const override {
      return "FramerDelSafeAccess Pass";
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>(); 
        
    }
    
  private:
    AliasSetTracker * AST; 
     
    void handleHooks (GEPOperator * gep, 
                      DominatorTree * DT,
                      Module & M, 
                      bool isMemAccess);

    void handleDuplicates(CallInst *ci,
    //, set<CallInst*> & duplicates
        DominatorTree * DT);
    void removeLeftovers (Function * F);
    //AliasSetTracker AST;
    //bool alreadyHas(set<CallInst*> & dups, CallInst* ci);
     
    //unsigned getBitwidth (Type * allocatedType, bool isOutMost);
    
}; //end of FramerDelSafeAccess

} //end of namespace llvm

#endif


