#include "llvm/Transforms/frame-pass/Framers.h"
#include "llvm/Transforms/frame-pass/FramerDelSafeAccess.h"

#define DEBUG_TYPE "framersafeaccess"

#define isGEPHook 1
using namespace llvm;
using namespace std;

STATISTIC (framerdelsafeaccesspasscounter, "FramerDelSafeAccess");


static RegisterPass<FramerDelSafeAccess> 
X ("framerdelsafeaccess", "FramerDelSafeAccess Pass", false, true);

char FramerDelSafeAccess::ID = 0;

///////////////////////////////////////////////
//     LTO porting 
INITIALIZE_PASS(FramerDelSafeAccess, "framerdelsafeaccess", "FramerDelSafeAccess Pass", false, false)
//     LTO porting. upto here 
///////////////////////////////////////////////


int safecount=0;
int dupload=0;
int dupstore=0;
int tempdupcount=0;

//op: load/store's ptr op. GEP

static void 
handleGEPHooks (GEPOperator * gep, 
                DominatorTree * DT, 
                Module & M,
                bool isMemAccess)
{   
    if (__isSafeAccess(gep, M, isMemAccess)){
        //0: not safe, 1: safe, 2: val= gep ptr 0 %x %y.. 
        
        //safecount++;
    }
}
static void
handleBitCastDuplicates(CallInst * ci, DominatorTree * DT)
{
  if (DT==nullptr) {
    return;
  }
  
  set<CallInst*> duplicates;
    
  Value * rawval=ci->getOperand(0)->stripPointerCasts(); //hook's uncasted  
    
  CallInst * fstchk= ci;  
     
  int count=0;

  assert(rawval->getNumUses()!=0);
  
    
 /* for (Value::user_iterator it= rawval->user_begin();it!=rawval->user_end();++it) {
    assert(*it!=nullptr);
  
    if (!isa<CastInst>(*it)) {
      continue;  
    }
   
    for (Value::user_iterator iit= (*it)->user_begin();iit!=(*it)->user_end();++iit) {

        CallInst * chk= dyn_cast<CallInst>(*iit); 
        if (chk==nullptr) {
          continue;
        }

        Function * hook= dyn_cast<Function>(chk->getCalledValue()); //problem
        if (hook==nullptr) {
          continue;
        }
        if (//!hook->getName().startswith("FRAMER_forall_load") && //for store-only checks
              !(hook->getName().startswith("FRAMER_forall_store"))
              ){
          continue;
        }
        
        if (fstchk==chk){
          continue;
        }
        //now we got a duplicate check for the same value.
          
        if (DT->dominates(fstchk, chk)) {  
            duplicates.insert(chk);
        }
        else if (DT->dominates(chk, fstchk)) {
            duplicates.insert(fstchk); 
            fstchk= chk; 
        }
        else {
          count++;
        }
    }
  }
 */ 
  
  // replace 
  for (set<CallInst*>::iterator it=duplicates.begin(),
          end=duplicates.end(); it!= end; ++it) {
    if ((*it)->getNumUses()==0) continue;
    
    if (CastInst * cins= dyn_cast<CastInst>(*((*it)->user_begin()))) {
        cins->setOperand(0, fstchk);
        dupstore++;  
    }
  }
 for (set<CallInst*>::iterator it=duplicates.begin(),
        end=duplicates.end(); it!= end; ++it) {
      (*it)->eraseFromParent(); 
  }

}

void 
FramerDelSafeAccess::handleDuplicates(CallInst * ci, 
                                     //set<CallInst*> & duplicates,
                                      DominatorTree * DT) //op: casted ptrop of S/L/
{
    // op is ptr op requiring cast passed from/to hook. 
    // HENCE(?), the ptr op's users should be in the same function,
    // so we can construct dominator tree and checking dominance relation. 

    
    if (DT==nullptr) {
        return; 
    }
    set<CallInst*> duplicates;
    
    Value * rawval=ci->getOperand(0)->stripPointerCasts(); //hook's uncasted  
    
    CallInst * fstchk= ci;  
     
    int count=0;

    if (rawval->getNumUses()==0) {
      errs()<<"rawval: "<<*rawval<<"  --> uses: 0\n";
      exit(0);
    }
    for (Value::user_iterator it= rawval->user_begin();it!=rawval->user_end();++it) {
      assert(*it!=nullptr);
      if (!isa<CastInst>(*it)) {
        continue;  
      }
      for (Value::user_iterator iit= (*it)->user_begin();iit!=(*it)->user_end();++iit) {

        CallInst * chk= dyn_cast<CallInst>(*iit); 
        if (chk==nullptr) {
          continue;
        }

        Function * hook= dyn_cast<Function>(chk->getCalledValue()); //problem
        if (hook==nullptr) {
          continue;
        }
        if (//!hook->getName().startswith("FRAMER_forall_load") && //for store-only checks
              !(hook->getName().startswith("FRAMER_forall_store"))
              ){
          continue;
        }
        
        if (fstchk==chk){
          continue;
        }
        //now we got a duplicate check for the same value.
          
        if (DT->dominates(fstchk, chk)) {  
            duplicates.insert(chk);
        }
        else if (DT->dominates(chk, fstchk)) {
            duplicates.insert(fstchk); 
            fstchk= chk; 
        }
        else {
          count++;
        }
      }
    }
  // replace 
  for (set<CallInst*>::iterator it=duplicates.begin(),
          end=duplicates.end(); it!= end; ++it) {
    if ((*it)->getNumUses()==0) continue;
    
    if (CastInst * cins= dyn_cast<CastInst>(*((*it)->user_begin()))) {
        cins->setOperand(0, fstchk);
        dupstore++;  
    }
  }
 for (set<CallInst*>::iterator it=duplicates.begin(),
        end=duplicates.end(); it!= end; ++it) {
      (*it)->eraseFromParent(); 
  }
}

void 
FramerDelSafeAccess::removeLeftovers (Function * F)
{
  //vector <Instruction*> toBeRemoved;
  set <Instruction*> toBeRemoved;
  for (Function::iterator IT=F->begin();IT!=F->end();++IT) {
    for (BasicBlock::iterator it=(*IT).begin();it!=(*IT).end();++it) {
      Instruction * inst= &*it;
      assert(inst!=nullptr);
      if (inst->getNumUses()==0 && isa<CastInst>(inst)) {
        toBeRemoved.insert(inst);   
      }
    }
  }
  for(set<Instruction*>::iterator it=toBeRemoved.begin(); 
       it!= toBeRemoved.end(); ++it) {
        (*it)->eraseFromParent();
  }

  /// find hotspot 
/*   if (!F->getName().equals("S_regmatch")) return;

   for (Function::iterator IT=F->begin();IT!=F->end();++IT) {
    for (BasicBlock::iterator it=(*IT).begin();it!=(*IT).end();++it) {
      Instruction * inst= &*it;
      if (LoadInst * li= dyn_cast<LoadInst>(inst)) {
              
      }
      if (StoreInst * si= dyn_cast<StoreInst>(inst)) {
          
      }


      }
    }
  }
 /////////
*/    
}
/*
bool 
FramerDelSafeAccess::alreadyHas (set<CallInst*> & dups, 
                                 CallInst* ci)
{
    if (dups.size()==0) return false;
    
    set<CallInst*>::iterator it= 
        find(dups.begin(), dups.end(), ci);
    if (it!=dups.end()) {
        return true;
    }
    return false;
}
*/

static void
addToEquivClass (CallInst * ci // op of hook_bitcast's op
                 , vector <vector<CallInst*>> & EC
                 , AAResults & AA
                 ) 
{
  Value * val= ci->getOperand(0);
  
  for (unsigned i=0;i<EC.size();i++) {
    for (unsigned j=0; j<EC.at(i).size(); j++) {
     
      if (AA.isMustAlias(EC.at(i).at(j), val)) {
        
        EC.at(i).push_back(ci);
        return; 
      }
    }
  }
  vector <CallInst*> oneclass;
  oneclass.push_back(ci);
  EC.push_back(oneclass);
}

static int
getAASetIdx (AliasSetTracker * AST, 
             AAResults & AA, 
             Instruction * op)
{
  int currentSet= 0; 

  for (AliasSetTracker::iterator I = AST->begin(); 
        I != AST->end(); ++I) {

    AliasSet &AS = *I;
     
    if (AS.aliasesUnknownInst(op, AA)) {
        return currentSet;     
    }
    /*for (AliasSet::iterator ASI = AS.begin(), 
            E = AS.end(); ASI != E; ++ASI) {

      Value * oneval= ASI->getValue();
       
      if (AA.isMustAlias(oneval, op)) {
        errs()<<*oneval<<"   --> alias!\n";
        idx= currentSet;
        return idx;
      }
    }*/

    currentSet++;   
  }
  return -1;
}

static void 
mergeBitCastHooks (vector<vector<CallInst*>> & myclass,
                   Function & F,
                   vector <vector<CallInst*>> & EC, 
                   DominatorTree * DT,
                   AAResults & AA,
                   AliasSetTracker * AST)
{
  for (AliasSetTracker::iterator I = AST->begin(); //E = AST->end();
         I != AST->end(); ++I) {
    
    vector <CallInst*> temp;
    myclass.push_back(temp); 
  }
  
  if (myclass.size()==0) return; //todo: myvector is empty
   
  //// end of initialise///
   
  for (Function::iterator fit= F.begin();fit!=F.end();++fit){   

    for (BasicBlock::iterator it=fit->begin();it!=fit->end();++it) {

      CallInst * ci = dyn_cast<CallInst>(it);

      if (!ci) continue;

      Function * F = ci->getCalledFunction();

      if (!F) continue;

      if (!F->getName().startswith("FRAMER_forall_bitcast")
          && !F->getName().startswith("FRAMER_forall_load")
          && !F->getName().startswith("FRAMER_forall_store")
          && !F->getName().startswith("FRAMER_forall_call_llvm_memset")
          &&  !F->getName().startswith("FRAMER_forall_call_llvm_memtransfer"))  continue; 
      
      Instruction * op= dyn_cast<Instruction>(ci->getOperand(0));

      if (!op) continue; 

      int AASetIdx= getAASetIdx(AST, AA, op);

      if (AASetIdx >= 0) { 
        myclass.at(AASetIdx).push_back(ci);
      } 
      
    }
  } 
}

static void
MemAccesshandleOneClass (vector<CallInst*> & oneclass,
                DominatorTree * DT,
                Module & M)
{
  set <CallInst*> DEL;
     
  for (unsigned i=0; i<oneclass.size(); i++) {
    for (unsigned j=0; j<oneclass.size(); j++) {

      if (i==j) continue;

      if (DT->dominates(oneclass.at(i), oneclass.at(j))) {

        DEL.insert(oneclass.at(j));
        tempdupcount++; 
      }                  
    }
  }

  assert(oneclass.size() > DEL.size() ); 
 
  Function * F = M.getFunction("FRAMER_untag_ptr");

  for (set<CallInst*>::iterator it= DEL.begin();
            it!=DEL.end();++it) {
    
     CallInst * ci= *it;
     // replace it with untag and then erase.
     vector<Value *> arglist;
     arglist.push_back(ci->getOperand(0));
     
     CallInst * rep = CallInst::Create (F, arglist, ""); // hook func callinst created.
     rep->insertBefore (ci); //then hook callinst inserted.
     ci->replaceAllUsesWith(rep); 
     ci->eraseFromParent();
  }
}

static void 
BitCasthandleOneClass (vector<CallInst*> & oneclass,
                       DominatorTree * DT)
{
  // (1) classify one class depending on dest tid.
  vector<vector<CallInst*>> classes; // categorise aliases by dest tid 
  vector <int64_t> tidlist;
  
     // (1.1) create tid list.
  for (unsigned i=0; i< oneclass.size(); i++) {
    CallInst * ci= oneclass.at(i);
    ConstantInt * temptid= dyn_cast<ConstantInt>(ci->getOperand(1));
    assert(temptid);
    int64_t tid= temptid->getSExtValue();
     
    if (getIdx(tidlist, tid) < 0) {
      tidlist.push_back(tid);
    }
  }

    // (1.2) create vectors of callinst whose elem num is tidlist.size() 
  for (unsigned i=0; i< tidlist.size(); i++) {
    vector<CallInst*> temp;
    classes.push_back(temp);
  }
    // (1.3) categorize callinsts by their tid.
  for (unsigned i=0; i<oneclass.size(); i++) {
   
    CallInst * ci= oneclass.at(i);
      
    ConstantInt * temptid= dyn_cast<ConstantInt>(ci->getOperand(1));
    assert(temptid);
    int64_t tid= temptid->getSExtValue();
    
    for (unsigned j=0; j<tidlist.size(); j++) {
      if (tidlist.at(j)==tid) {
        classes.at(j).push_back(ci);
        break;      
      }      
    }
  }
  
  // (2) now insert hook calls into DEL.
  set <CallInst*> DEL;
  
  for (unsigned K=0; K<classes.size(); K++) {
     
    for (unsigned i=0; i<classes.at(K).size(); i++) {
      for (unsigned j=0; j<classes.at(K).size(); j++) {

        if (i==j) continue;

        if (DT->dominates(classes.at(K).at(i), classes.at(K).at(j))) {

          DEL.insert(classes.at(K).at(j)); 
          tempdupcount++; 
        }                  
      }
    }
  }
  

  assert(oneclass.size() > DEL.size() ); 
  
  for (set<CallInst*>::iterator it= DEL.begin();
            it!=DEL.end();++it) {
    
     CallInst * ci= *it;
     ci->eraseFromParent();
  }
}

static void
removeRest (vector <vector<CallInst*>> & myclass,
            DominatorTree * DT,
            Module & M)
{
  //errs()<<"### now del ###\n";

  for (unsigned i=0; i<myclass.size();i++) {
    unsigned mysize= myclass.at(i).size();
   
    //errs()<<"  "<<i<<", size: "<<mysize<<"\n";
          
    if (mysize <= 1) continue; 
 
  #ifndef ENABLE_SPACEMIU
    MemAccesshandleOneClass(myclass.at(i), DT, M);
    
  #else
    
    BitCasthandleOneClass(myclass.at(i), DT);
  
  #endif
  }
}

static void
removeBitCastDups (Function & F,
                   vector <vector<CallInst*>> & EC, 
                   DominatorTree * DT,
                   AAResults & AA,
                   AliasSetTracker * AST,
                   Module & M)
{
  vector<vector<CallInst*>> myclass;

  mergeBitCastHooks (myclass, F, EC, DT, AA, AST);

  // initialise myclass 
  removeRest (myclass, DT, M);
  
  
  removeRest (EC, DT, M); 
  
}

/*
  SpaceMIU hooks bitcast inserted by Framer.
  DELETE THEM FIRST!
*/
/*static bool
isHookedForHooks (Value * op)
{
  if (isa<CallInst>(op)) { 
    
    errs()<<"\nop1: "<<*op<<"\n";  

    CallInst * ci= cast<CallInst>(op);
    Function * fn= ci->getCalledFunction();
      
    if (!fn) {
        errs()<<"not func call. return\n"; 
        return false;
    }
    
    if (!fn->getName().startswith("FRAMER_")) {
        errs()<<"not framer hook. return\n";   
        return false;
    }
     
    errs()<<"op itself: "<<*ci<<"\n";
   
    return true;  //case 4, 2
  }
  else if (isa<BitCastOperator>(op)) { 
      BitCastOperator * bcop= cast<BitCastOperator>(op);
      
      errs()<<"BC op: "<<*bcop<<"\n";
     
      if (isa<BitCastOperator>(bcop->getOperand(0))) {
        BitCastOperator * bc= 
            cast<BitCastOperator>(bcop->getOperand(0));  
        
        if (!bc->hasOneUse()) return false;
        
        User* usr= *(bc->user_begin()); 

        if (!isa<CallInst>(usr)) return false;;

        CallInst * ci= cast<CallInst>(usr);
        Function * fn= ci->getCalledFunction();

        if (!fn) return false; 

        if (!fn->getName().startswith("FRAMER_")) return false;

        errs()<<"bc's 1user: "<<*ci<<" (FRAMER?)\n";

      }
      else {
         ; 
      }
  } 

  for (Value::user_iterator it= op->user_begin();
            it!=op->user_end(); ++it) {

    errs()<<"op3: "<<*op<<"\n"; 
    User * usr= *it;

    /// bitcast arg for Hook alloca or global, etc)
    if (isa<BitCastOperator>(usr)) {
        
      BitCastOperator * bc= cast<BitCastOperator>(usr);
      
      errs()<<"BC usr: "<<*bc<<"\n";
      
      /// 
      for (Value::
      if (!bc->hasOneUse()) continue;
      
      User* usr2= *(bc->user_begin()); 
      
      if (!isa<CallInst>(usr2)) continue;
      
      CallInst * ci= cast<CallInst>(usr2);
      Function * fn= ci->getCalledFunction();
      
      if (!fn) continue; 
   
      if (!fn->getName().startswith("FRAMER_")) continue;
     
      errs()<<"bc's 1user: "<<*ci<<" (FRAMER?)\n";
      ///
    }
  }
  
  return false;
}
*/
/*
static void
removeHooksForHooks (Function & F)
{
  set <CallInst*> DEL;

  for (Function::iterator fi= F.begin(); fi!=F.end(); ++fi){
 
    for (BasicBlock::iterator it=(*fi).begin(); 
            it!=(*fi).end(); ++it) {
      
      CallInst * ci = dyn_cast<CallInst>(&*it);

      if (!ci) continue;

      Function * called = ci->getCalledFunction();
      if (!called) continue;

      if (!called->getName().startswith("FRAMER_forall_bitcast")) continue;  
      
      Value * op= ci->getOperand(0);  //strip cast or not?
      
      if (isHookedForHooks(op)) {
        DEL.insert(ci); 
      }
    }
  }
  
  /// delete the hooks.
  for (set<CallInst*>::iterator it= DEL.begin();
            it!= DEL.end(); ++it) {
    
    CallInst * ci= *it;
    errs()<<"delete: "<<*ci<<"\n";

    ci->eraseFromParent();
  }
  
  DEL.clear();
}
*/

bool
FramerDelSafeAccess::runOnBasicBlock (BasicBlock & BB,
                              vector <vector<CallInst*>> & EC, 
                              DominatorTree * DT,
                              AAResults & AA,
                              AliasSetTracker * AST,          
                              Module & M)
{
  Instruction * successorInst = &*BB.begin();
  
  for(BasicBlock::iterator it= BB.begin();it!=BB.end();++it){  
 
    if (&*it != &*successorInst) continue;

    successorInst = getNextInst(&*it);

    CallInst * callInst = dyn_cast<CallInst>(it);
 
    if (!callInst) continue;
  
 //   if (callInst->getNumUses()==0) continue;

    Function * F = callInst->getCalledFunction();
    if (!F) continue;
    
    assert(callInst->getOperand(0)!=nullptr); 

#ifndef ENABLE_SPACEMIU

    if (F->getName().startswith("FRAMER_forall_getelementptr")) {

      GEPOperator * GEP = getGEPFromCheckCallInst(callInst);
      if (!GEP) continue; 

      handleGEPHooks (GEP, DT, M, 0);

    }
    else if (//F->getName().startswith("FRAMER_forall_load") || //for store-only checks
         F->getName().startswith("FRAMER_forall_store") 
         || F->getName().startswith("FRAMER_forall_load") 
         || F->getName().startswith("FRAMER_forall_call_llvm_memset")
         || F->getName().startswith("FRAMER_forall_call_llvm_memtransfer")) {
    
      assert((callInst->getOperand(0)!=nullptr));
      // if the ptr has multiple uses, 
      if (isa<GlobalVariable>(callInst->getOperand(0))
          && callInst->getOperand(0)->getNumUses()>1) {
          errs()<<"Del Safe: do something\n";
          exit(0);
      }
      else if (isa<CastInst>(callInst->getOperand(0))){
          //  && callInst->getOperand(0)->stripPointerCasts()->getNumUses()>1) {
        
        //if (alreadyHas(duplicates, callInst)) continue;
        //handleDuplicates(callInst, duplicates, DT);  
        //handleDuplicates(callInst, DT);  
      
        Value * op= callInst->getOperand(0)->stripPointerCasts(); 
        
        if (isa<Instruction>(op)) {
        AST->add(cast<Instruction>(op));
        }
        else if (isa<VAArgInst>(op)) {
            AST->add(cast<VAArgInst>(op));
        }
        else {
            addToEquivClass(callInst, EC, AA);
        }
      }
    }

#else
   
    if (F->getName().startswith("FRAMER_forall_bitcast")) {


        Value * op= callInst->getOperand(0);

        //Value * op= callInst->getOperand(0)->stripPointerCasts();
        //errs()<<"\n###################\n";
        //errs()<<*callInst<<"\n";
        //errs()<<"raw op: "<<*callInst->getOperand(0)<<"\n"; 
        //errs()<<"stripped: "<<*op<<"  --> add. \n";

        if (isa<Instruction>(op)) {
            AST->add(cast<Instruction>(op));
        }
        else if (isa<VAArgInst>(op)) {
            AST->add(cast<VAArgInst>(op));
        }
        else {
            addToEquivClass(callInst, EC, AA);
        }

    }
    else {;}

#endif    

  }
}

bool 
FramerDelSafeAccess::runOnFunction (Function &F, 
                                    Module & M)
{
    DominatorTree * DT= &getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    AAResults & aaresult= getAnalysis<AAResultsWrapperPass>(F).getAAResults();
    
    AST = new AliasSetTracker(aaresult);
    
    vector <vector<CallInst*>> EC; //equivalent class
  
  // (1) delete bitcast hooks inserted for bitcast inserted by FRAMER. 
    //removeHooksForHooks (F); 
  
  // collect equiv class.   
    for (Function::iterator fit= F.begin();fit!=F.end();++fit){   
        runOnBasicBlock (*fit, EC, DT, aaresult, AST, M);
    }

/////    

    unsigned tempECcount= 0;
    for (unsigned i=0;i<EC.size();i++) {
        if (tempECcount < EC.at(i).size()) {
            tempECcount= EC.at(i).size();    
        }
    }

/////
    
    removeBitCastDups (F, EC, DT, aaresult, AST, M);
       
    AST->clear();
    EC.clear();
}


bool 
FramerDelSafeAccess::runOnModule(Module & M) {
  
  framerdelsafeaccesspasscounter++;
   
  for (Module::iterator IT= M.begin();IT!=M.end(); ++IT) {
    if ((*IT).isDeclaration()) continue;
    if ((*IT).getName().startswith("FRAMER_")) continue; 

    //LoopInfo &LI= getAnalysis<LoopInfoWrapperPass>(*IT).getLoopInfo();
    //ScalarEvolution * SE= &getAnalysis<ScalarEvolutionWrapperPass>(*IT).getSE();
    //DominatorTree & DT= getAnalysis<DominatorTreeWrapperPass>(*IT).getDomTree();
   
   /* 
   for (Function::iterator fit= (*IT).begin();fit!=(*IT).end();++fit){   
        handleBB (*fit, EC, DT, aaresult, M);
    }
   */
    runOnFunction(*IT, M);
    
    //removeDupBitCast (EC);

#ifndef ENABLE_SPACEMIU

  //  removeLeftovers(&*IT);

#endif
  }

   
  errs()<<"safecount : "<<safecount<<"\n";
  errs()<<"deleted dupcount : "<<tempdupcount<<"\n";
  errs()<<">>>>>>>>leaving del safe access pass\n\n";
  
  return true;
}
