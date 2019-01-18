
//==------ FramerLoopOpt.h --------==//

#ifndef FRAMER_LoopOpt_H_
#define FRAMER_LoopOpt_H_

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
//#include "llvm/IR/Dominators.h"
//#include "llvm/Analysis/PostDominators.h" 
#include "llvm/Support/CommandLine.h"
#include "llvm/PassRegistry.h"
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/PassManagerBuilder.h>
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Analysis/LoopAccessAnalysis.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/ScalarEvolutionAliasAnalysis.h"

//#include "llvm/Analysis/LoopPassManager.h"

using namespace llvm;
using namespace std;

namespace llvm {
struct FramerLoopOpt : public ModulePass {
  public:
    static char ID;
    FramerLoopOpt() : ModulePass(ID) {}

    virtual bool runOnModule(Module & M);
    StringRef getPassName() const override {
      return "FramerLoopOpt Pass";
    }

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addRequired<ScalarEvolutionWrapperPass>();
        //AU.setPreservesCFG();
        //AU.addRequired<DominatorTreeWrapperPass>();
    }
    //virtual bool doInitialization(Loop *L, LPPassManager &LPM); 
    //virtual bool doFinalization(); 
    
  private:
    //LoopInfo * LI;
    //ScalarEvolution * scevPass;
    //DataLayout * TD;

    std::set<Loop*> optimizedLoops;
    
    void handleLoop(Loop *L, 
                    LoopInfo &LI,  
                    ScalarEvolution * scevPass,
                    //DominatorTree * DT,
                    Module &M/*,
                    DominatorTree & dt*/);
    void skipALLChecks (Loop *L, 
                        LoopInfo &LI,
                        Module & M);
    bool optimizeCheck (Loop *L, 
                        ScalarEvolution * scevPass, 
                        //DominatorTree * DT,
                        LoopInfo &LI,
                        Module & M/*,
                        DominatorTree & dt*/); 
    bool isRuntimeCheck (Function * F);
    bool isEligibleForOptimization(const Loop * L);     
    bool isHoistableGEPToHD(GEPOperator * GEP, 
                            Loop * L, 
                            ScalarEvolution * scevPass);
    bool isHoistableGEPToExit(GEPOperator * GEP, 
                              Loop * L); 

    //static GetElementPtrInst * getGEPFromCheckCallInst(CallInst * callInst); 
    //static bool getPossibleLoopVariable(Loop * L, std::vector<PHINode*> & list); 
    bool isMonotonicLoop(Loop * L, 
                         Value * loopVar, 
                         ScalarEvolution * scevPass);
    bool isIgnorableFunc (Function * F);
    void removeLeftovers (Loop * L, LoopInfo &LI);
 
    void insertEdgeBoundsCheck (Loop * L,
            CallInst * callInst,
            GEPOperator * origGEP,
            Instruction * ptIns,
            int type, 
            ScalarEvolution * scevPass,
            set<CallInst*> & toBeRemoved,
            Module & M,
            bool HookKind
            );
    
    void insertCheckMemAccess(GEPOperator * origGEP,
                              Instruction * ptIns,
                              Instruction * castedNewGEP,
                              set<CallInst*> & toBeRemoved,
                              Loop * L,
                              const CallInst * origHook,
                              Module & M);
    void castAndreplaceUses(CallInst * orig,
                            Loop * L,
                            set<CallInst*> & toBeRemoved,
                            Instruction * newchk,
                            Module & M); 
    CallInst * createUntagHook (CallInst * orig, 
                                Instruction * ptIns,
                                Module & M);


}; //end of FramerLoopOpt

} //end of namespace llvm

#endif


