////////////////////////////////////////
///// Obfuscation.cpp ////////////////////
////////////////////////////////////////

#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/Interval.h"
#include "llvm/Transforms/Obfuscation/Obfuscation.h"

//#define MYDEBUG

#ifdef MYDEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

using namespace llvm;
using namespace std;

STATISTIC (obfuscationpasscounter, "Obfuscation");

static RegisterPass<Obfuscation> 
X ("obfuscation", "Obfuscation Pass", false, true);

char Obfuscation::ID = 0;

///////////////////////////////////////////////
//     LTO porting 
///////////////////////////////////////////////

//INITIALIZE_PASS(Obfuscation, "obfuscation", "Obfuscation Pass", false, false)

///////////////////////////////////////////////
//     LTO porting. upto here 
///////////////////////////////////////////////

//static RegisterAnalysisGroup<PostDominatorTreeWrapperPass> Y(X);


static void 
insertCastInstForArg (Instruction * inserBeforeMe, 
                      vector<Value*> & arglist )
{
  for(vector<Value*>::iterator it = arglist.begin(); 
                        it!= arglist.end();++it){

    if (Instruction * mycast = dyn_cast<Instruction>(*it)){
      if (!mycast->getParent()) {
        mycast->insertBefore (inserBeforeMe);
      }
    }

  }
}

static void 
pushtoarglist (BasicBlock* bb,  
               Type * paramTy,
               Value * arg, 
               vector<Value*> & arglist,
               Module & M) 
{
  Type * argty= arg->getType();
  
  if (paramTy == argty) {
      arglist.push_back(arg);
      return;  
  }
  
  /// now paramty != argty

  if (CastInst* temp= dyn_cast<CastInst>(arg)) {
      if (temp->getSrcTy() == paramTy) {
          arglist.push_back(temp->getOperand(0));
          return;
      }
  }
  if (paramTy->isPointerTy() && argty->isPointerTy()){

      arglist.push_back(new BitCastInst(arg, paramTy));
  }
  else if (paramTy->isIntegerTy() && argty->isVectorTy()) {

      VectorType * vty= cast<VectorType>(argty);
      unsigned argtysize= M.getDataLayout().getTypeSizeInBits(vty);
      if (paramTy->getIntegerBitWidth()!= argtysize) {

          BitCastInst * bci= 
              new BitCastInst(arg, Type::getIntNTy(M.getContext(),argtysize), "", bb);
          arglist.push_back(new ZExtInst(bci, paramTy));
      }
      else {
          arglist.push_back(new BitCastInst (arg, paramTy));
      }
  }
  else if (isa<PtrToIntInst>(arg)||
           isa<TruncInst>(arg)||
           isa<FPToSIInst>(arg)) {
      
      arglist.push_back(new ZExtInst (arg, paramTy));
  }
  else if (isa<SExtInst>(arg)) {
      arglist.push_back(new SExtInst (arg, paramTy));
  }
  else if (paramTy->isIntegerTy() && argty->isIntegerTy()) {
      assert(paramTy->getIntegerBitWidth() >= (argty)->getIntegerBitWidth()
              && "created arg for hook's int bitwdith is bigger than hook's original type width!\n");
      arglist.push_back(new SExtInst (arg, paramTy));
  }
  else if (paramTy->isIntegerTy()&& argty->isDoubleTy()) {
      arglist.push_back(new FPToUIInst (arg, paramTy));
  }
  else if (paramTy->isIntegerTy() && argty->isPointerTy()) {
      arglist.push_back(new PtrToIntInst (arg, paramTy)); 
  }
  else {
      errs()<<"ParamTy: "<<*paramTy<<", arg: "<<*argty<<"\n";
      errs()<<"!!!Unspecified type conversion!\n";
      exit(0);
  }
  return;
}

//pick BB to split


Instruction *
getOneOfRet(Function & fn)
{
    // get return ins
  Instruction * ret= nullptr;
  auto bbList = &(fn.getBasicBlockList()); 

  //errs()<<"bb reverse:\n"; 
  for(auto it = bbList->rbegin(); it != bbList->rend(); it++) {
     
      //errs()<<"  bb name: "<<(&*it)->getName()<<"\n";
       
      Instruction * ins= (&*it)->getTerminator();
        
      if (isa<ReturnInst>(ins)) {
        //errs()<<"  return inst: "<<*ins<<"\n";
        ret= ins;   
        break;
      } 
  }
  assert(ret);
  return ret; 
}

static Instruction *
getCandidate(Instruction * ins) 
{
  
  Instruction * userins= nullptr;

  if (isa<LoadInst>(ins)){
    
    Value * liop= cast<LoadInst>(ins)->getPointerOperand();
  
    // traverse user_list backwards and return any inst. 
    
    liop->reverseUseList ();
     
    for (auto it= liop->use_begin(); it!=liop->use_end(); ++it) {
        
      if (!isa<Instruction>(it->getUser())) continue;
      
      // now a user is an instruction
        
      Instruction * userins= cast<Instruction>(it->getUser());
      
        
      if (userins->isBinaryOp() || userins->isBitwiseLogicOp() 
            || userins-> isShift()) { 
        
        return userins; 
            // going deeper just one level..
      }
      else if (isa<StoreInst>(userins)) {
          
        StoreInst * si= cast<StoreInst>(userins);

        if (si->getPointerOperand()==liop) {
            
          Instruction * sival= 
              dyn_cast<Instruction>(si->getValueOperand());
          
          if (sival) {
          
            return sival;
          }
        }
        else {
             
          if (isa<Instruction>(si->getPointerOperand()))
            return cast<Instruction>(si->getValueOperand()); 
                //this ever happens?     
        }
      }
    }
  }
  else if (isa<PHINode>(ins)) {
    
    PHINode * phi= cast<PHINode>(ins);
    

    for (unsigned i=0; i< phi->getNumIncomingValues(); i++) {
      
      if (isa<Instruction>(phi->getIncomingValue(i))){ 
        
        return cast<Instruction>(phi->getIncomingValue(i));
      }
    }
  }
  else {
    
    ins->reverseUseList ();
    userins= dyn_cast<Instruction>(ins->user_back()); //initialise
    for (Value::use_iterator it= ins->use_begin(); it!=ins->use_end(); it++) {
     
      Instruction * temp= dyn_cast<Instruction>((&*it)->getUser());
      assert(temp);
       
      if (temp->mayWriteToMemory()) {
        userins= temp;
        break; 
      }
    }
  }
  return userins; 
}


static Instruction *
pickIns (Function & fn) 
{
  // if a func has only one BB, choose/return the middle ins.
  // we assume that there are at least 2 instructions. 
 
  if (fn.getBasicBlockList().size()==1) { 
    dbg(errs()<<"#bb==1\n";) 
    
    SymbolTableList<Instruction> & inslist= fn.front().getInstList(); 
    //assert(inslist.size()>1 && "we assume #ins in the 1st bb is bigger than 1..\n");
    BasicBlock::iterator it= inslist.begin(); 
   advance(it, inslist.size()/2);
    
    fn.front().splitBasicBlock(it, "");
    return &fn.front().front();
  }
  
  Instruction * picked= &*fn.begin()->begin(); //initialise it with the 1st inst. 

  // function has a return val.
  if (!fn.getReturnType()->isVoidTy()) {
         
    dbg(errs()<<"return ty!=void\n";) 
    
    Instruction * retins= getOneOfRet(fn);
  
 
    if (retins) { // found one of return instructions

      Instruction * retop= dyn_cast<Instruction>(retins->getOperand(0));
            
      if (retop) { // ret ins' operand is an inst.
      
        return getCandidate(retop);
     
      }                       
    }
    else { // couldn't find a ret (?)
        ;  
    }
  }
  if (fn.getFunctionType()->getNumParams() > 0) {
    // fn takes some arguments.
    
    dbg(errs()<<"has arg\n";) 
    
    Value * arg= &*fn.arg_begin(); // just picked the 1st argument..
    ///
    //arg->reverseUseList ();
    
     
    for (Value::use_iterator it= arg->use_begin(); it!=arg->use_end(); ++it) {
        
      if (!isa<Instruction>(it->getUser())) continue;
      
      Instruction * ins= cast<Instruction>(it->getUser());
      
      //if (ins->mayReadToMemory() || ins->isBinaryOp() 
      if (ins->mayWriteToMemory() || ins->isBinaryOp() 
          || ins->isBitwiseLogicOp() || ins-> isShift()) { // etc...
          
        return ins; 
      }

    } 
  }
 // if fn type is void(void), then pick any memory access 
  
  dbg(errs()<<"choose random\n";) 
  
  auto bbList = &(fn.getBasicBlockList()); 
   
  for(auto it = bbList->rbegin(); it != bbList->rend(); it++) {
     
      BasicBlock * bb= &*it;
      
      for (BasicBlock::iterator it= bb->begin(); it!=bb->end(); it++) {
       
        Instruction * ins= (&*it); 
         
        if (ins->mayWriteToMemory() || ins->isBinaryOp() ||
            ins->isShift() || ins->isBitwiseLogicOp()) {
            return ins; 
        }
      }
       
    }
  
  exit(0); 
  return picked; 

}

// set newbb's predecessors as oldbb's and make newbb oldbb's pred.
static void 
modifyPredecessor (BasicBlock * newbb, BasicBlock * oldbb, 
                   BasicBlock * newpred)
{
  // for  3 and 4 edge
  for (pred_iterator PI= pred_begin(oldbb), E = pred_end(oldbb); PI != E; ++PI) {
    
    BasicBlock *PredBlock = *PI;
    
    // (1) modify oldbb's phi nodes

    for (auto it= oldbb->begin(); it!=oldbb->end(); ++it) {
      
      if (!isa<PHINode>(&*it)) continue; 
      
      PHINode * phi= cast<PHINode>(&*it); // replace prev with trap
      
        for (unsigned i=0; i<phi->getNumIncomingValues(); i++) {
          
          BasicBlock * inbb= phi->getIncomingBlock (i); 
          
          if (inbb==PredBlock) {
            phi->setIncomingBlock (i, newpred); 
          }
        }
    }

    // (2) modify oldbb's preds' terminator    
    
    BranchInst *PBI = dyn_cast<BranchInst>(PredBlock->getTerminator()); 
    assert(PBI && "Terminator is something else. Do something\n");  
        // currently dealing with only branch ins.
      
    for (unsigned i=0; i< PBI->getNumSuccessors(); i++) {
        
      BasicBlock * suc= PBI->getSuccessor(i); 
      
      if (suc==oldbb) {
         PBI->setSuccessor(i, newbb); 
      }
    }
          
  }
}

static void
handlePredTrapBB (BasicBlock * predtrapbb,
                  BasicBlock * trapbb,
                  BasicBlock * pickedbb)
{
    // 1. fill predtrapBB -- set trapbb as a succbb (No other ins) 
    // 2. update pickedBB's preds. TODO 

    BranchInst::Create(trapbb, predtrapbb);
    modifyPredecessor(predtrapbb, pickedbb, trapbb); // here 
}

static void 
handleTrapBB (Function & F, Module & M, 
              BasicBlock * trapbb, 
              BasicBlock * gototrapbb, 
              BasicBlock * pickedbb){
    
    // 1. fill trapBB 
    Function * hook= M.getFunction("__HOOK_opaque");
    assert(hook); 
    assert(hook->getFunctionType()->getParamType(0)->isIntegerTy());
        // Currently we assume opaque function type (int opaque (int))
    
  
  /// create a call to opaque func.
    
    
    // initialise opaque func's arg. 
    Value * opaquearg= Constant::getNullValue(hook->getFunctionType()->getParamType(0));
     
    if (F.getFunctionType()->getNumParams() > 0) { // if F has arg(s) 

      Argument * F1starg= &*F.arg_begin(); //currently just chose the 1st arg.
      opaquearg= F1starg;
        // replace opaque's arg with F's arg. 
    }
 // test IRbuilder
    vector <Value*> arglist;
    pushtoarglist (trapbb, hook->getFunctionType()->getParamType(0),
                   opaquearg, arglist, M);
     
    CallInst* callopaque= 
        CallInst::Create (hook, arglist, "ci", trapbb);
    
    insertCastInstForArg(callopaque, arglist);       
     
    // insert compare inst
    Constant * cmpval= Constant::getNullValue(callopaque->getType()); // constant null(0) 
    ICmpInst * icmpins= new ICmpInst(*trapbb, ICmpInst::ICMP_NE, callopaque, cmpval, "tobool");
  
    // insert branch inst   
    BranchInst::Create(pickedbb, gototrapbb, icmpins, trapbb);
 
}


static void
handleGoToTrapBB(BasicBlock * trapbb, 
                 BasicBlock * gototrapbb) {

    BranchInst::Create(trapbb, gototrapbb);
      // setting gototrapbb's successors (single)
}

bool
Obfuscation::runOnFunction (Function &F, 
                            Module &M, 
                            CallGraph & CG)
{

    //DominatorTree &dt= getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    //AAResults & aaresult= getAnalysis<AAResultsWrapperPass>(F).getAAResults();

    
    Instruction * pickedins= pickIns(F);
        // This splits a basic block into two at pickedins.
    BasicBlock * pickedbb= pickedins->getParent();
  
    // if the picked ins is phi, advance the iterator. 
    // otherwise things get complicated..  
    BasicBlock::iterator SplitIt = pickedins->getIterator(); 
    while (isa<PHINode>(SplitIt) || SplitIt->isEHPad())
        ++SplitIt;
    pickedins= &*SplitIt;
    
    dbg(
      errs()<<"\nchosen ins: "<<*pickedins<<"\n";
      errs()<<"\nchosen BB: "<<*pickedbb<<"\n\n";
    )
    // create predtrapBB 1/4
     
    BasicBlock * predtrapbb= 
        BasicBlock::Create(F.getContext(), "predtrap", &F, pickedbb); 
    
    // create trapBB  2/4
    BasicBlock * trapbb= 
        BasicBlock::Create(F.getContext(), "trapBB", &F, pickedbb); 
    
    // split the pickedBB 3/4 (pickedBB is the BB that will be split into two)
    
    //Instruction * nextins= getNextInst(pickedins);
    //assert(nextins); //pickedins better not be a terminator ins
    //BasicBlock * succ= pickedbb->splitBasicBlock(nextins);   
  
  /// commented out above three and run the following para.
    BasicBlock * succ= pickedbb->splitBasicBlock(pickedins);   
       
    // create a pickedbb's successorBB. 4/4
    BasicBlock * gototrapbb= 
        BasicBlock::Create(F.getContext(), "gototrapBB", &F, succ); 
  
  //////////////////
  /// New BBs are created. Fill and bridge the BBs
  //////////////////

    handlePredTrapBB(predtrapbb, trapbb, pickedbb);
            // Handle created predtrapBB.
    
    handleTrapBB (F, M, trapbb, gototrapbb, pickedbb); 
            // Handle created trapBB
    
    //handlePickedBB(F,M, pickedbb, preditrap, );                 
    // Handle splitted pickedBB 
   
     
      
    handleGoToTrapBB (trapbb, gototrapbb);
            // Handle created gototrapbb 
    
    // Handle splitted half (succ) 
            // Just keep the branchIns as it is.
    
    return true;
}

static bool
isHookFunc(Function * fn)
{
  if (fn->getName().startswith("__HOOK_")) {
   return true; 
  }

  return false;
}

bool Obfuscation::runOnModule (Module &M) 
{
    obfuscationpasscounter++;

    CallGraph & CG= getAnalysis<CallGraphWrapperPass>().getCallGraph();
     
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
       
        dbg(errs()<<"### Function::  "<<mi->getName()<<"\n";) 
        
        Function * fn= &*mi;
          
        if (fn->isDeclaration()) {
            dbg(errs()<<"\t::decl.skipping..\n";) 
            continue; 
        }
        if (isHookFunc(fn)) { // skip hooks e.g. __HOOK_OPAQUE(n)
            continue;
        }
        runOnFunction(*fn, M, CG);
    }
    
    dbg(errs()<<">>>>>>>>>>> Leaving Obfuscation\n";) 
    return true;
}

