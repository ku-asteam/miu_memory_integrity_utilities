
//==------ Obfuscation.h --------==//

#ifndef OBFUSCATION_H_
#define OBFUSCATION_H_

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
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/PassRegistry.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include "llvm/IR/LegacyPassManager.h"


//#include "llvm/Transforms/frame-pass.h"

using namespace llvm;
using namespace std;

namespace llvm {
struct Obfuscation : public ModulePass {

  public:
    static char ID;
    Obfuscation() : ModulePass(ID) {
    
    }

    virtual bool runOnModule(Module &M);
    virtual bool runOnFunction (Function &F, 
                                Module &M, 
                                CallGraph & CG); 
  /*  virtual bool runOnBasicBlock (BasicBlock &BB, 
                                  DominatorTree & dt, 
                                  AAResults & AA,
                                  CallGraph & CG, 
                                  Module &M);
   */ 
    StringRef getPassName() const override {
      return "Obfuscation Pass";
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<AAResultsWrapperPass>(); 
        AU.addRequired<CallGraphWrapperPass>(); 
    }

  protected:
      
      //Instruction * getNextInst (Instruction * Inst);
      //GlobalVariable * getNextGV (GlobalVariable * GV, Module &M); 

      //bool isHookFamilyFunction   (Function * F); 

    
}; // end of struct Obfuscation
} // end or namespace llvm

#endif
