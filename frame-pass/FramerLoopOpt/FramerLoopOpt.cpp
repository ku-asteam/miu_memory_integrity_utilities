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

#include "llvm/Transforms/frame-pass/Framer.h"
#include "llvm/Transforms/frame-pass/Framers.h"
#include "llvm/Transforms/FramerLoopOpt/FramerLoopOpt.h"
//#include "safecode/MonotonicOpt.h"

#define DEBUG_TYPE "framerloopopt"

#define isGEPHook 1
using namespace llvm;
using namespace std;

STATISTIC (framerloopoptpasscounter, "FramerLoopOpt");


static RegisterPass<FramerLoopOpt> 
X ("framerloopopt", "FramerLoopOpt Pass", false, true);

char FramerLoopOpt::ID = 0;

///////////////////////////////////////////////
//     LTO porting 
INITIALIZE_PASS(FramerLoopOpt, "framerloopopt", "FramerLoopOpt Pass", false, false)
//     LTO porting. upto here 
///////////////////////////////////////////////

//debugs
int loopoptcount=0;
int hoistablecount=0;
int replacecount=0;
int elsecount=0;
//debuge

bool
FramerLoopOpt::isRuntimeCheck (Function * F)
{
    //errs()<<"  runtime check? "<<F->getName()<<"\n";
    if (F->getName().startswith("FRAMER_")) {
        //errs()<<"   yes\n";
        return true;
    }
    return false;
}
bool 
FramerLoopOpt::isIgnorableFunc (Function * F)
{
    StringRef fname= F->getName(); 
    if (fname.startswith("printf") 
            || fname.equals("putchar")
            || fname.equals("puts")) {
        return true;
    }
    return false;
}

bool
FramerLoopOpt::isEligibleForOptimization(const Loop * L) {
  
  // Determine if the loop has a preheader.
  BasicBlock * Preheader = L->getLoopPreheader();
  if (!Preheader) return false;
  // Determine whether the loop has a single exit block.
  SmallVector<BasicBlock*, 4> exitBlocks;
  L->getExitingBlocks(exitBlocks);
  if (exitBlocks.size() != 1) {
    return false;
  }

  // Scan through all of the instructions in the loop.  If any of them are
  // calls to functions (other than calls to run-time checks), then note that
  // this loop is not eligable for optimization.
  for (Loop::block_iterator I=L->block_begin(),E=L->block_end();I!=E;++I) {
    BasicBlock *BB = *I;
    for (BasicBlock::iterator I=BB->begin(),E=BB->end();I!=E;++I) {
      // Calls to LLVM intrinsics will not change the bounds of a memory
      // object.
      if (isa<IntrinsicInst>(I))
        continue;

      // If it's a call to a run-time check, just skip it.  Otherwise, if it is
      // a call, mark the loop as ineligable for optimization.
      if (CallInst * CI = dyn_cast<CallInst>(I)) {
        Function * F = CI->getCalledFunction();
        if (F && !isRuntimeCheck (F) && !isIgnorableFunc(F))
          return false;
      }
    }
  }
  // The loop has passed all of our checks and is eligable for optimization.
  return true;
}

/// Determines if a GEP can be hoisted
//FramerLoopOpt::isHoistableGEP(GetElementPtrInst * GEP, Loop * L) 

bool 
FramerLoopOpt::isHoistableGEPToHD(GEPOperator * GEP, 
                                  Loop * L, 
                                  ScalarEvolution * scevPass) 
{
  for(int i = 0, end = GEP->getNumOperands(); i != end; ++i) {
    Value * op = GEP->getOperand(i);
    if (L->isLoopInvariant(op)) {
        continue;
    }
    const SCEV * SH= scevPass->getSCEV(op);
    if (!scevPass->hasComputableLoopEvolution(SH, L)) return false;
    
     
    const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(SH);
    if (!AR || !AR->isAffine()) return false;
    const SCEV * startVal = AR->getStart();
    const SCEV * endVal = scevPass->getSCEVAtScope(op, L->getParentLoop());
    if (isa<SCEVCouldNotCompute>(startVal) ||
        isa<SCEVCouldNotCompute>(endVal)) {
      return false;
    }

// by Jins.    
    //const SCEV * & val_lower= startVal; 
    const SCEV * & val_higher= endVal;
     
    if (!(//isSafeToExpand(val_lower, *scevPass) &&
          isSafeToExpand(val_higher, *scevPass) && 
          //scevPass->dominates(val_lower, L->getLoopPreheader()) && 
          scevPass->dominates(val_higher, L->getLoopPreheader()))
    ){
        //errs()<<"NOT hoistable\n";
        return false;
    }
// by Jine    

  }
  return true;
}

/*
static GEPOperator *
getGEPFromCheckCallInst(CallInst * CI) 
{
    Value * gep= CI->getOperand(0);
    return dyn_cast<GEPOperator>(gep->stripPointerCasts());     
}
*/

/// Find the induction variable for a loop
/// Based on include/llvm/Analysis/LoopInfo.h
static bool getPossibleLoopVariable(Loop * L, std::vector<PHINode*> & list) 
{
  list.clear();
  BasicBlock *H = L->getHeader();

  BasicBlock *Incoming = 0, *Backedge = 0;
  typedef GraphTraits<Inverse<BasicBlock*> > InvBasicBlockraits;
  InvBasicBlockraits::ChildIteratorType PI = InvBasicBlockraits::child_begin(H);
  assert(PI != InvBasicBlockraits::child_end(H) &&
   "Loop must have at least one backedge!");
  Backedge = *PI++;
  if (PI == InvBasicBlockraits::child_end(H)) return 0;  // dead loop
  Incoming = *PI++;
  if (PI != InvBasicBlockraits::child_end(H)) return 0;  // multiple backedges?
  // FIXME: Check incoming edges

  if (L->contains(Incoming)) {
    if (L->contains(Backedge))
      return 0;
    std::swap(Incoming, Backedge);
  } else if (!L->contains(Backedge))
    return 0;

  // Loop over all of the PHI nodes, looking for a canonical indvar.
  for (BasicBlock::iterator I = H->begin(), E=H->end(); I != E;  ++I) {
    isa<PHINode>(I);
    PHINode *PN = dyn_cast<PHINode>(I);
    if (PN) {
      list.push_back(PN);
    }
  }
  return list.size() > 0;
}

bool
FramerLoopOpt::isMonotonicLoop(Loop * L, Value * loopVar, ScalarEvolution * scevPass) 
{
  //
  // Determine whether the loop has a constant iteration count.
  //
  bool HasConstantItCount = false;

//// debugs
if (scevPass==nullptr){
    errs()<<"scevPass null\n";
}
/// debuge

  if (scevPass->hasLoopInvariantBackedgeTakenCount(L)) {
    HasConstantItCount=isa<SCEVConstant>(scevPass->getBackedgeTakenCount(L));
  }
  //
  // Determine whether ScalarEvolution can provide information on the loop
  // induction variable.  If it cannot, then just assume that the loop is
  // non-monotonic.
  //
  if (!(scevPass->isSCEVable(loopVar->getType())))
    return false;

  //
  // If the loop iterates a fixed number of times or if the specified loop
  // variable can be expressed as an expression that is variant on the loop
  // induction variable, then attempt to see if the specified loop variable
  // is affine and amenable to our analysis.
  //
  const SCEV * SH = scevPass->getSCEV(loopVar);

  if (scevPass->hasComputableLoopEvolution(SH, L) ||
      HasConstantItCount) {
    const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(SH);
    if (AR && AR->isAffine()) {
      const SCEV * startVal = AR->getStart();
      const SCEV * endVal=scevPass->getSCEVAtScope(loopVar, L->getParentLoop());

//debugs
if (!startVal || !endVal){
  errs()<<"startval or endval null\n";
}

//debuge

      if (!isa<SCEVCouldNotCompute>(startVal) &&
          !isa<SCEVCouldNotCompute>(endVal)){
        // Success
        return true;
      }
    }
  }

  //
  // The loop does not appear monotonic, or we cannot get SCEV expressions for
  // the specified loop variable.
  //
  return false;
}

/*
static bool
opsDominatesNewIns (Value * val, 
                    Instruction * inst, 
                    DominatorTree * DT)
{
    if(!isa<Instruction>(val)) return true;
    Instruction * srcins= cast<Instruction>(val); 

    if (!DT->dominates(srcins, inst)){ 
        return false;      
    }
    
    for (int i=0;i<srcins->getNumOperands();i++){
      // if op(i) does not dominate ptins   
      if (!opsDominatesNewIns(srcins->getOperand(i), inst, DT)) {
        return false;
      }
    }
    return true; 
}
*/

/// for each op of boundsval, check if op dominates boundsval.
/// if dominating -> proceed to set ops of newGEP. 
/// if not -> erase (not delete) newGEP and bndIns (no touch of boundsVal's ops) 

/*
static bool
opsDominatesBoundsVal (Instruction * bndIns, 
                       DominatorTree * DT, 
                       SCEVExpander & Rewriter)
{
  
  for (int i=0;i<bndIns->getNumOperands();i++) {
    if (!isa<Instruction>(bndIns->getOperand(i))) continue;
    Instruction * binOpIns= dyn_cast<Instruction>(bndIns->getOperand(i));
    if(!DT->dominates(binOpIns, bndIns)){
      errs()<<" NOT DOMINATING.\n";
      if (isa<PHINode>(bndIns)) return true;

      if (!Rewriter.isInsertedInstruction(bndIns)) {
        errs()<<" not inserted by rewriter: "<<*binOpIns<<"\n";
        exit(0);
        return true;
      }
      domcount++;
      return false; 
    }
  } 
  return true;
}
*/

/// Insert checks for edge condition
void
FramerLoopOpt::insertEdgeBoundsCheck (Loop * L,
                                     CallInst * callInst,
                                     GEPOperator * origGEP,
                                     Instruction * ptIns,
                                     int type,
                                     ScalarEvolution * scevPass,
                                     //vector<CallInst*> & toBeRemoved,
                                     set<CallInst*> & toBeRemoved,
                                     Module & M,
                                     bool HookKind
                                     //DominatorTree * DT
                                     )
{
  enum {
    LOWER_BOUND,
    UPPER_BOUND
  };
   
  static const char * suffixes[] = {".lower", ".upper"};
  SCEVExpander Rewriter(*scevPass, callInst->getModule()->getDataLayout(), "scevname"); 
  
  Instruction *newGEP;
  if (isa<GetElementPtrInst>(origGEP)) {
    newGEP= cast<GetElementPtrInst>(origGEP)->clone();
  }
  else {
    newGEP= cast<GetElementPtrConstantExpr>(origGEP)->getAsInstruction();
    errs()<<"GEP constant: "<<*origGEP<<"\n";
    errs()<<" GEP op: "<<origGEP->getPointerOperand()<<"\n";
    if(isa<GlobalVariable>(origGEP->getPointerOperand()->stripPointerCasts())) {
        errs()<<" -->gep pointer op is GV!\n";   
    }
    exit(0);
  }

  newGEP->setName(origGEP->getName() + suffixes[type]);

  for(int i = 0, end = origGEP->getNumOperands(); i != end; ++i) {
    Value * op = origGEP->getOperand(i);
    if (L->isLoopInvariant(op)) continue;

    const SCEV * SH= scevPass->getSCEV(op);
    const SCEVAddRecExpr *AR= dyn_cast<SCEVAddRecExpr>(SH);
    const SCEV * startVal= AR->getStart();
    const SCEV * endVal= scevPass->getSCEVAtScope(op, L->getParentLoop());
    const SCEV * & val= type == LOWER_BOUND ? startVal : endVal; 
    
    Value * boundsVal= Rewriter.expandCodeFor(val, val->getType(), ptIns);

    newGEP->setOperand(i, boundsVal);
  }
  newGEP->insertBefore(ptIns);

///// re-structuring
// (1) check dominatortree. if dominating, do following. otherwise. skip. 
  Instruction * castedNewGEP= nullptr;
  Value * newSrcPtr= nullptr;

  if (newGEP->getType()==getVoidPtrType(callInst->getContext())) {
    castedNewGEP= newGEP;     
  }
  else {  
    castedNewGEP= CastInst::CreatePointerCast(
                    newGEP,
                    getVoidPtrType(callInst->getContext()), 
                    newGEP->getName() + ".casted",
                    ptIns);
  } 
  assert(castedNewGEP!=nullptr && "castedNewGEP is null\n");

  if (HookKind) { // if it's hook_gep
    if (origGEP->getPointerOperand()->getType()==getVoidPtrType(callInst->getContext())) {
      newSrcPtr= origGEP->getPointerOperand();
    }
    else {
      newSrcPtr= CastInst::CreatePointerCast(
                      origGEP->getPointerOperand(), //0th
                      //newGEP->getOperand(0),
                      getVoidPtrType(callInst->getContext()), 
                      origGEP->getName() + ".casted",
                      newGEP);

    }

    Instruction * checkInst= callInst->clone(); 
    checkInst->setOperand(0, castedNewGEP);
    checkInst->setOperand(1, newSrcPtr); 
    checkInst->insertBefore(ptIns);
      
    insertCheckMemAccess (origGEP, ptIns, castedNewGEP, toBeRemoved, L, callInst, M);
  }
  else { //hook_SL 
    loopoptcount++;
    Instruction * checkInst= callInst->clone(); 
    checkInst->setOperand(0, castedNewGEP);
    checkInst->insertBefore(ptIns);
    
    castAndreplaceUses(callInst, L, toBeRemoved, checkInst, M); 
  }
}

void static 
insertCastInstForArg (Instruction * insertBeforeMe, 
                     vector<Value*> & arglist)
{
    for(vector<Value*>::iterator it = arglist.begin(), ie = arglist.end(); it!=ie ; ++it){
        if (Instruction * mycast = dyn_cast<Instruction>(*it)){
            if (!mycast->getParent()) {
                mycast->insertBefore (insertBeforeMe);
            }
        }
    }
}


CallInst *
FramerLoopOpt::createUntagHook (CallInst * orig, 
                                Instruction * ptIns, //load/store inst
                                Module & M)
{
    Function *hook= M.getFunction("FRAMER_supplementary_untag_ptr"); 
    vector<Value *> arglist;
    CallInst * untag = nullptr; 
    
    if (orig->getOperand(0)->getType()==hook->getFunctionType()->getParamType(0)) { 
        arglist.push_back(orig->getOperand(0));
        untag = CallInst::Create (hook, arglist);
        untag->insertBefore(ptIns);
    }
    else {
        assert(orig->getOperand(0)->getType()->isPointerTy()
        &&  hook->getFunctionType()->getParamType(0)->isIntegerTy());
        
        pushtoarglist(ptIns, 
                     hook->getFunctionType()->getParamType(0),
                     orig->getOperand(0),
                     arglist, M);
        untag= CallInst::Create (hook, arglist, "");
        insertCastInstForArg (ptIns, arglist);
        untag->insertBefore (ptIns);

    }
    return untag;
}

//orig: call Framer_store/load (old_gep)
//user: load orig (or store val orig). TODO. now we get castinst user!
// *** hook_load is pushbacked into toBeRemoved here.  
void 
FramerLoopOpt::castAndreplaceUses(CallInst * orig, 
                                  Loop * L,
                                  set<CallInst*> & toBeRemoved,
                                  Instruction * newchk,
                                  Module & M)
{
//    assert(orig->getType()==newCI->getType() && "different type\n");
    bool changed=false;
    replacecount++;
     
// debug s
  if (orig->getNumUses()==0) {
    errs()<<" op:     "<<*orig->getOperand(0)<<"\n";
    errs()<<" casted: "<<*orig->getOperand(0)->stripPointerCasts()<<"\n";
  }
// debug e 
     
    Use * currentUse= &*orig->use_begin();
    Use * nextUse = currentUse;
    
    while (nextUse) {
        Instruction * user= dyn_cast<Instruction>(currentUse->getUser()); 
        nextUse = currentUse->getNext();
        //errs()<<"user: "<<*user<<"\n";
         
        assert(user!=nullptr && "user null\n");
        assert(user!=nullptr 
                && "orig (hook_store) not instruction\n"); 
        assert (user->getParent()!=L->getLoopPreheader()
                && "user is already in preheader?\n");
       
        //// when user is a castinst
        if (isa<CastInst>(user)){
          for(Value::user_iterator iit= user->user_begin();
                  iit!=user->user_end();++iit) {
            assert((isa<StoreInst>(*iit)||isa<LoadInst>(*iit))
                      && "not Store or Load 1\n");
          }
 /*       CastInst * cstins= cast<CastInst>(user);
        cstins->setOperand(0,newchk);
        toBeRemoved.insert(orig); */
         
          Instruction * CSTI= dyn_cast<Instruction>(user);
          assert(CSTI!= nullptr && "CSTI null\n");
          if (CSTI->getParent()==orig->getParent()
                  || !L->isLoopExiting(CSTI->getParent())){ 
              CallInst * untag= createUntagHook(orig, CSTI, M); // insert location? 
              CSTI->replaceUsesOfWith (orig, untag); //TODO. orig???
              toBeRemoved.insert(orig);
          }
          // SLI is in Loop, but not in preheader or in exit loop. 
          else {
              errs()<<"somewhere else 1\n";
              exit(0); 
          } 
        }
        else { //user: LI/SI hook_orig
            assert((isa<StoreInst>(user)||isa<LoadInst>(user))
                    && "not Store or Load 2\n");
            if (user->getParent()==orig->getParent()
                || !L->isLoopExiting(user->getParent())){ 
              
              CallInst * untag= createUntagHook(orig, user, M);  
              user->replaceUsesOfWith (orig, untag); 
              toBeRemoved.insert(orig);
            }
            // SLI is in Loop, but not in preheader or in exit loop. 
            else if (L->contains(user)) {
              errs()<<"just in the loop. user: "<<*user<<"\n";
              exit(0);
            }
            else {
              errs()<<"somewhere else 2\n";
              exit(0); 
            }
        }
    //TODO next: do something for memset? 
        currentUse = nextUse;
    }
    assert(orig->getNumUses()==0 && "orig's uses not 0\n");
}

void
FramerLoopOpt::insertCheckMemAccess(GEPOperator * origGEP,
                                    Instruction * ptIns,
                                    //CastInst * castedNewGEP,
                                    Instruction * castedNewGEP,
                                    //vector<CallInst*> & toBeRemoved,
                                    set<CallInst*> & toBeRemoved,
                                    Loop * L,
                                    const CallInst * origHook,
                                    Module & M)
{
    for(Value::user_iterator it= origGEP->user_begin(); 
            it!= origGEP->user_end(); ++it){
       
        if (*it==origHook)     continue; 
        if (!isa<CallInst>(*it)) continue;

        CallInst * CI= dyn_cast<CallInst>(*it); 
        Function * hook= CI->getCalledFunction();
        
        if (!CI || !hook) continue;
        
        // TODO: if CI's uses==0, 
        
        if (hook->getName().equals("FRAMER_forall_store")
                || hook->getName().equals("FRAMER_forall_load")){
              
            if (CI->getParent()!=origHook->getParent()) continue;
           
            /// clone hook.
            Instruction * checkInst = CI->clone(); //checkInst is call framer_gep
            // replace with castedNewGEP
            checkInst->setOperand(0, castedNewGEP);
            checkInst->insertBefore(ptIns);
             
            // replace all the uses of original hook 
            castAndreplaceUses(CI, L, toBeRemoved, checkInst, M); 
        }
        else if (hook->getName().equals("FRAMER_supplementary_untag_ptr")){
            errs()<<"UNTAG op\n";
            exit(0);
        }
        else {
            errs()<<"Skip: "<<**it<<"\n";
            exit(0);
        }
    }
}
/*
static Instruction * 
getNextInst (Instruction * Inst)
{
    BasicBlock::iterator I (Inst);
    I++;
    if (I == Inst->getParent()->end()) {
        return nullptr;
    }
    return &*I;
}*/

void 
FramerLoopOpt::removeLeftovers (Loop * L, LoopInfo &LI)
{
  //vector <Instruction*> toBeRemoved;
  set <Instruction*> toBeRemoved;
  for (Loop::block_iterator I=L->block_begin(),E=L->block_end();
          I!=E;++I) {
    BasicBlock *BB = *I;
    // Ignore blocks in subloops...
    if (LI.getLoopFor(BB) != L) continue; 

    for (BasicBlock::iterator it=BB->begin(),end=BB->end();it!=end;++it) {
      Instruction * inst= &*it;
      if (inst->getNumUses()==0 && isa<CastInst>(inst)) {
        toBeRemoved.insert(inst);   
      }
    }
  }
  //for(vector<Instruction*>::iterator it=toBeRemoved.begin(); 
  for(set<Instruction*>::iterator it=toBeRemoved.begin(); 
       it!= toBeRemoved.end(); ++it) {
     //  errs()<<"remove 2: "<<**it<<"\n";
    (*it)->eraseFromParent();
  }
}

static bool isHookedGEP (GEPOperator * gep)
{
  for(Value::user_iterator it=gep->user_begin();it!=gep->user_end();++it){
    if (isa<CastInst>(*it)) {
      CastInst * Cins= cast<CastInst>(*it); 
      for(Value::user_iterator iit=Cins->user_begin();iit!=Cins->user_end();++iit){
        if (!isa<CallInst>(Cins)) continue; 
          CallInst * ci= cast<CallInst>(Cins);
          Function * F= ci->getCalledFunction();
          if (!F) continue;
          if (F->getName().equals("FRAMER_forall_getelementptr")) 
            return true; 
      }
    }
    else if (isa<CallInst>(*it)){
      CallInst * ci= cast<CallInst>(*it);
      Function * F= ci->getCalledFunction();
        if (!F) continue;
        if (F->getName().equals("FRAMER_forall_getelementptr")) 
            return true; 

    }
  }
  return false;
}

static bool isLowbound (GEPOperator * gep)
{
  for(GEPOperator::op_iterator it= gep->idx_begin();
        it!=gep->idx_end();++it) {
    if (isa<ConstantInt>(*it)) {
      ConstantInt * idx= cast<ConstantInt>(*it);
      if (idx->getSExtValue()<0){
        return true; 
      }
    }
  }
  return false;           
}

static void 
replaceWithInlined (CallInst * ci, set<CallInst*> & toBeRemoved, Module & M)
{
    //get function
    Function * newf= nullptr;
    if (ci->getCalledFunction()->getName().startswith("FRAMER_forall_load")) {
        newf= M.getFunction("FRAMER_forall_load_inlining");
    }
    else if (ci->getCalledFunction()->getName().startswith("FRAMER_forall_store")) {
        newf= M.getFunction("FRAMER_forall_store_inlining"); 
    }
    assert(newf!=nullptr); 
    
    vector<Value*> arglist;
    for (int i=0;i<ci->getNumArgOperands();i++){    
        pushtoarglist (ci, 
                newf->getFunctionType()->getParamType(i), 
                ci->getArgOperand(i), arglist, M); 
    }
    CallInst * newci = CallInst::Create (newf, arglist, "");
    newci->insertBefore (ci);
    
    assert(ci->hasOneUse() && "multiple uses of hook?\n");
    ci->replaceAllUsesWith(newci);
    
    toBeRemoved.insert(ci);
}

bool
FramerLoopOpt::optimizeCheck(Loop *L, 
                             ScalarEvolution * scevPass,
                             //DominatorTree * DT,
                             LoopInfo &LI,
                             Module & M){
  
  // Determine whether the loop is eligible for optimization. 
  // If not, don't optimize it.
  if (!isEligibleForOptimization(L)) return false;

  // Remember the preheader block; we will move instructions to it.
  // TODO: hoisting frame check outside the loop, 
  // with base of 1st iteration, and last one,
  // and then see if they are in the same frame. (maybe new check?)
  // and then remove both in-frame checks and bounds check.  
  
  BasicBlock * Preheader= L->getLoopPreheader();
  bool changed = false;
  
  vector<PHINode *> loopVarList;
  getPossibleLoopVariable(L, loopVarList); //TODO. what is induction variable?
  PHINode * loopVar= NULL;

  for (vector<PHINode*>::iterator it=loopVarList.begin(),end=loopVarList.end();it!=end; ++it) {
    if (!isMonotonicLoop(L, *it, scevPass)) continue;


    loopVar = *it;
    
    // Loop over the body of this loop, looking for calls, invokes, and stores.
    // Because subloops have already been incorporated into AST, we skip blocks in
    // subloops.
    //
    set<CallInst*> toBeRemoved;
    for (Loop::block_iterator I = L->block_begin(), E = L->block_end();
         I != E; ++I) {
      BasicBlock *BB = *I;
      if (LI.getLoopFor(BB) != L) continue; // Ignore blocks in subloops...
        
      Instruction * successorInst = &*BB->begin();
     
      for (BasicBlock::iterator it=BB->begin(),end=BB->end();it!=end;++it) {
        
        if (&*it != &*successorInst) continue;
        successorInst = getNextInst(&*it);
        CallInst * callInst = dyn_cast<CallInst>(it);
        
        if (!callInst) continue;

        /// ** TODO: insert hook_gep for this case later. 
        /// it's optimized away from the previous passes, i guess. 
        if (callInst->getNumUses()==0) continue;
         
        Function * F = callInst->getCalledFunction();
        if (!F) continue;
        
        int boundtype=1; //default: upperbound
        if (F->getName().startswith("FRAMER_forall_getelementptr")) {
        
            GEPOperator * GEP = getGEPFromCheckCallInst(callInst);
            
            errs()<<"\nGEP HOOK: "<<*callInst<<"\n";
            errs()<<" GEP: "<<*GEP<<"\n";
            errs()<<" gep op: "<<GEP->getPointerOperand()<<"\n";
             
            if (!GEP) continue; 
            
            if (isHoistableGEPToHD(GEP, L, scevPass)) {
                errs()<<"   -->> hoistable!\n";
                hoistablecount++;
                 
                if (isLowbound(GEP)) boundtype=0; 
                 
                Instruction *ptIns= Preheader->getTerminator();
                insertEdgeBoundsCheck(L, callInst, GEP, ptIns, boundtype, 
                                      scevPass, toBeRemoved, M, isGEPHook);
            }
        }
        else if (F->getName().startswith("FRAMER_forall_load")
                ||F->getName().startswith("FRAMER_forall_store")) {
            
            if (callInst->getParent()==Preheader) continue; 
            
        /// bug bug!
            set<CallInst*>::iterator callit= 
                find(toBeRemoved.begin(), toBeRemoved.end(), callInst);
            if (callit!=toBeRemoved.end()) {
                errs()<<"oldHook in the loop body: "<<*callInst<<"\n";
                exit(0);
            }
        ///
            GEPOperator * GEP = getGEPFromCheckCallInst(callInst);
            
            //errs()<<"\nGEP HOOK: "<<*callInst<<"\n";
            //errs()<<" GEP: "<<*GEP<<"\n";
            //errs()<<" gep op: "<<*GEP->getPointerOperand()<<"\n";
            
            if (!GEP) continue; 
            
            if (isHookedGEP(GEP)) continue; //this hook will be handle at hook_gep 
            
            // GEP hook is optimised away. insert hook_gep currently? 
            if (isHoistableGEPToHD(GEP, L, scevPass)) {
                
                //errs()<<"   -->> hoistable!\n";
                
                hoistablecount++;
                if (isLowbound(GEP)) boundtype=0; 
                 
                int count1= toBeRemoved.size();
                Instruction *ptIns= Preheader->getTerminator();
                insertEdgeBoundsCheck(L, callInst, GEP, 
                                      ptIns, boundtype, 
                                      scevPass, toBeRemoved, 
                                      M, !isGEPHook);
            }
            else {
                //replace with inlined one
                replaceWithInlined (callInst, toBeRemoved, M); 
            }
            
        }
        changed = true;
      }
    }
    for (set<CallInst*>::iterator it=toBeRemoved.begin(),
            end=toBeRemoved.end(); it!= end; ++it) {
      //errs()<<"remove 1: "<<(**it)<<"\n";
      (*it)->eraseFromParent();
    }
  }

  return changed;
}
/*
void
FramerLoopOpt::skipALLChecks (Loop *L, 
                               LoopInfo &LI, 
                                Module & M) 
{ // test function to see how big overheads checks inside loop are causing
  set<CallInst*> toBeRemoved;

  for (Loop::block_iterator I = L->block_begin(), E = L->block_end();
       I != E; ++I) {
    BasicBlock *BB = *I;
    if (LI.getLoopFor(BB) != L) continue; // Ignore blocks in subloops...

    Instruction * successorInst = &*BB->begin();

    for (BasicBlock::iterator it=BB->begin(),end=BB->end();it!=end;++it) {
      if (&*it != &*successorInst) continue;
      successorInst = getNextInst(&*it);
      CallInst * callInst = dyn_cast<CallInst>(it);
       
      if (!callInst) continue;

      if (callInst->getNumUses()==0) continue;
         
      Function * F = callInst->getCalledFunction();
      if (!F) continue;
        
      if (F->getName().startswith("FRAMER_forall_load")
          || F->getName().startswith("FRAMER_forall_store")) {

          castAndreplaceUses(callInst, L, toBeRemoved, M); 
      }
      else if (F->getName().startswith("malloc")
          ||F->getName().startswith("free")) {
        elsecount++;
      }
    }
  }
  for (set<CallInst*>::iterator it=toBeRemoved.begin(),
          end=toBeRemoved.end(); it!= end; ++it) {
      (*it)->eraseFromParent();
  }
}
*/


void 
FramerLoopOpt::handleLoop (Loop *L, 
                           LoopInfo &LI, 
                           ScalarEvolution * scevPass,
                           Module & M) 
{
  for (Loop *SL : L->getSubLoops()) {
    handleLoop(SL, LI, scevPass, M/*, dt*/);
  }
  
  // Optimize the checks in the loop and record that we have done so.
  optimizedLoops.insert(L);
  bool changed= optimizeCheck(L, scevPass, LI, M);
  //skipALLChecks(L, LI, M);
  removeLeftovers(L, LI); 
}

bool 
FramerLoopOpt::runOnModule(Module & M) {
  errs()<<"---> starting Framer Loop Opt\n";
  framerloopoptpasscounter++;
 
  optimizedLoops.clear();

  for (Module::iterator IT= M.begin();IT!=M.end(); ++IT) {
    if ((*IT).isDeclaration()) 
        continue;
    if ((*IT).getName().startswith("FRAMER_")) 
        continue; 
     
    //errs()<<"\n>>>>Loop Opt F: "<<(&*IT)->getName()<<"\n";

    LoopInfo &LI= getAnalysis<LoopInfoWrapperPass>(*IT).getLoopInfo();
    ScalarEvolution * SE= &getAnalysis<ScalarEvolutionWrapperPass>(*IT).getSE();
    //DominatorTree *DT= &getAnalysis<DominatorTreeWrapperPass>(*IT).getDomTree();

    for (LoopInfo::iterator LIT=LI.begin(), LEND=LI.end(); LIT != LEND; ++LIT) {
      handleLoop (*LIT, LI, SE, M);
    }
    optimizedLoops.clear();
  // debugs
/*    if (ff->getName().startswith("DensityChannel")){
      errs()<<"DescribeChannel 2----\n";
      for (Function::iterator it= ff->begin();it!=ff->end();++it){
        for (BasicBlock::iterator iit= it->begin();iit!=it->end();++iit) {
          errs()<<" "<<*iit<<"\n";  
        }
      }
      errs()<<" ==== \n";
    }
*/
// debuge

  }

//  errs()<<"hoistable count: "<<hoistablecount<<"\n";
  errs()<<"replacecount: "<<replacecount<<"\n";
  errs()<<"elsecount: "<<elsecount<<"\n";
  errs()<<">>>>>>>>leaving looppass\n\n";
  
  return true;
}
