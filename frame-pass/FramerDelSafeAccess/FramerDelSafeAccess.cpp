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

//op: load/store's ptr op. GEP

void 
FramerDelSafeAccess::handleHooks(GEPOperator * gep, 
                                 DominatorTree * DT, 
                                 Module & M,
                                 bool isMemAccess)
{   
    if (__isSafeAccess(gep, M, isMemAccess)){
        //0: not safe, 1: safe, 2: val= gep ptr 0 %x %y.. 
        
        safecount++;
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
bool FramerDelSafeAccess::alreadyHas(set<CallInst*> & dups, CallInst* ci)
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

void
FramerDelSafeAccess::handleBB(BasicBlock & BB, DominatorTree * DT, Module & M)
{
  Instruction * successorInst = &*BB.begin();
  //set<CallInst*> duplicates;
  for(BasicBlock::iterator it= BB.begin();it!=BB.end();++it){  
    if (&*it != &*successorInst) continue;
    successorInst = getNextInst(&*it);
    CallInst * callInst = dyn_cast<CallInst>(it);
    if (!callInst) continue;

    if (callInst->getNumUses()==0) continue;

    Function * F = callInst->getCalledFunction();
    if (!F) continue;
    
    assert(callInst->getOperand(0)!=nullptr); 
    if (F->getName().startswith("FRAMER_forall_getelementptr")) {
      GEPOperator * GEP = getGEPFromCheckCallInst(callInst);
      if (!GEP) continue; 
      handleHooks (GEP, DT, M, 0);
    }
    else if (//F->getName().startswith("FRAMER_forall_load") || //for store-only checks
         F->getName().startswith("FRAMER_forall_store")) {
    
      assert((callInst->getOperand(0)!=nullptr));
      // if the ptr has multiple uses, 
      if (isa<GlobalVariable>(callInst->getOperand(0))
          && callInst->getOperand(0)->getNumUses()>1) {
          errs()<<"Del Safe: do something\n";
          exit(0);
      }
      else if (isa<CastInst>(callInst->getOperand(0))
            && callInst->getOperand(0)->stripPointerCasts()->getNumUses()>1) {
        
        //if (alreadyHas(duplicates, callInst)) continue;
        
        //handleDuplicates(callInst, duplicates, DT);  
        handleDuplicates(callInst, DT);  
      }
    }
    else {;}
  }
  
  // delete hook_dup
 /* for (set<CallInst*>::iterator it=duplicates.begin(),
          end=duplicates.end(); it!= end; ++it) {
   /// debugging.s
    Function * myf= (*it)->getCalledFunction(); 
    assert(myf!=nullptr);
    if (myf->getName().equals("FRAMER_forall_load")) {
        dupload++; 
    }
    else if (myf->getName().equals("FRAMER_forall_store")) {
        dupstore++; 
    }
   /// debugging.e
      
      (*it)->eraseFromParent();
  }*/
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
    DominatorTree * DT= &getAnalysis<DominatorTreeWrapperPass>(*IT).getDomTree();

    for (Function::iterator fit= (*IT).begin();fit!=(*IT).end();++fit){   
        handleBB (*fit, DT, M);
    }
    removeLeftovers(&*IT);
  }
  
  errs()<<"safecount : "<<safecount<<"\n";
  errs()<<"dupstore : "<<dupstore<<"\n";
  errs()<<">>>>>>>>leaving del safe access pass\n\n";
  
  return true;
}
