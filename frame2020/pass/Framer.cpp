//==---- Framer.cpp ------==//

#include "llvm/Analysis/Passes.h"
#include "llvm/Analysis/TypeBasedAliasAnalysis.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Analysis/AliasAnalysis.h"

#include "llvm/Transforms/miu/Framers.h"
#include "llvm/Transforms/miu/Framer.h"
//#include "llvm/Transforms/miu/Framer.h"

#define DEBUG_TYPE "framer"

//#define MYDEBUG
#ifdef MYDEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

#define isOpaqueStructT -1
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

STATISTIC (framerpasscounter, "Framer");


///////////////////////////////////////////////
// register a pass and initialize ///////////// 


char Framer::ID= 0;

//static RegisterPass<Framer> 
//X ("framer", "Framer Pass", false, false);

INITIALIZE_PASS(Framer, "framer", "Framer Pass", false, false)

//void llvm::initializeFramerPass(PassRegistry &Registry);   

ModulePass* llvm::createFramerPass(){
    return new Framer();
}

void LLVMInitializeFramer (LLVMPassRegistryRef R) {
    llvm::initializeFramerPass (*unwrap(R));
} 

void LLVMAddFramerPass(LLVMPassManagerRef PM) {
    unwrap(PM)->add(createFramerPass()); 
}



// register a pass and initialize -- upto here
///////////////////////////////////////////////


enum CalledFuncEnum {
    MallocIsCalled,
    FreeIsCalled,
    LLVMMemTransferIsCalled, // containing both memcpy and memmove.
    LLVMMemSetIsCalled,
    ExternalFuncIsCall
    
};

unsigned tempGVcount=0;
unsigned temploadsafe=0;
unsigned tempstoresafe=0;
unsigned tempgepsafe=0;
unsigned tempload=0;
unsigned tempstore=0;
unsigned safeptr=0;
const DataLayout * dlayout;

const int CalledFuncEnum_count = ExternalFuncIsCall-MallocIsCalled+1;
Function *      Func_main = nullptr;
Instruction *   fstInstOfMainFunction= nullptr; 
BasicBlock *    fstBBOfMainFunction= nullptr;
BasicBlock *    initBBOfMain= nullptr;
BasicBlock *    GVsBBOfMain= nullptr;


bool HookDefinitionExists [100]={0};
bool HookDefForCalledFuncExists [CalledFuncEnum_count]={0};

vector <Type*> AllTypeList;

vector <StructType*> allStructTyList;
vector <vector<pair<short, vector<short>>>> tyoffsets; 

#ifdef ENABLE_SPACEMIU
  vector <vector <short>> flatrtoffsets;
  unsigned MaxOffset= 0;
  short max_upcasts;
#endif

vector <vector<short>> SafeCasts;
vector <vector<short>> DownCasts;

// * Union GV's*
vector <GlobalVariable*> GVUnions;

// * Heap unions
vector <Value*> HeapUnions;

// * the total number of all offsets for all types * 
unsigned totaloffsetcount= 0;

// * max tid count per offset.   
unsigned maxtysperoff= 0;

// * max offset count per ty
unsigned maxoffsperty= 0;

// * max offset value (not count, but value!) 
unsigned maxoffsetval= 0;

// * entry type size of an offset table *
unsigned tblentrysize= 0;



StructType*     HeaderTy=nullptr;
IntegerType*    OffByOneTy=nullptr;

/// GlobalVariable * basicTypeTable; 
GlobalVariable* StructTyTable=nullptr; /* StructTyTable in Arraytype */ 
GlobalVariable* startStructTypeTable=nullptr; 

// * GlobalVariable * SafeCastsTable*
GlobalVariable* SafecastTable=nullptr; /* SafeCastsTable in Arraytype */ 
GlobalVariable * rtOffsetTbl= nullptr;

////

ArrayType * SafeTidsTy= nullptr;
StructType * oneOffsetTy= nullptr;
ArrayType * entryT= nullptr;
ArrayType * tableT= nullptr;

const unsigned llvmbasicTyCount= 19;
const unsigned extrabasicTyCount= 8; //int8,16,32,64,128,and then i1, i48!!
const unsigned FramerBasicTyCount= llvmbasicTyCount+extrabasicTyCount; 
unsigned structTyCount=0;
uint64_t headerTySize=0;  
unsigned headerTyAlign=0;

const uintptr_t FRAMER_log_slotsize= 15;
const unsigned FRAMER_TyIDStart=100; //we use spare bits for big-framed allocation (flag=0) 
//bool PointersAreTagged = false;


unsigned maxcount100temp=0;
vector <Value*> paddedGVs;
set <Instruction*> FramerLoads;

//static RegisterAnalysisGroup<PostDominatorTreeWrapperPass> Y(X);

void 
Framer::insertCastInstForArg (Instruction * insertBeforeMe, 
                                      vector<Value*> & arglist )
{
    for(vector<Value*>::iterator it = arglist.begin(), ie = arglist.end(); it!=ie ; ++it){
        if (Instruction * mycast = dyn_cast<Instruction>(*it)){
            if (!mycast->getParent()) {
                mycast->insertBefore (insertBeforeMe);
            }
        }
    }
}

GlobalVariable* 
Framer::getNextGV (GlobalVariable * GV, 
                           Module &M)
{
    Module::global_iterator I (GV);
    I++;
    
    if (I == M.global_end()) {
        dbg(errs()<<"Next is the last GV!\n";)
        return nullptr;
    }
    return &*I;
}

Value * 
Framer::createConstantIntInstance (unsigned val, 
                                          Type * destTy)
{
    return ConstantInt::get(destTy, val); 
}

Value * 
Framer::constructValueFromFunc (unsigned val, 
                                        Function * F, 
                                        unsigned paramIdx)
{
    return ConstantInt::get(F->getFunctionType()->getParamType(paramIdx), 
                            val); 
}

Value * 
Framer::getArraySize (AllocaInst * AI, 
                              Type * funcParamTy) 
{
    if (AI->isArrayAllocation() 
        || AI->getArraySize() != ConstantInt::get(AI->getArraySize()->getType(), 1)) {
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

Type * 
Framer::getTypeOfElemOfArray (Type * allocatedType)
{
    if  (ArrayType *  MyArrayTy = dyn_cast<ArrayType>(allocatedType)) { 
        return MyArrayTy->getElementType();
    }
    else {
        return allocatedType;
    }
}

void 
Framer::insertCastToRestoreType (Instruction* insertAfterMe, 
                                         vector<Value*> & castinglist)
{
    for(vector<Value*>::iterator it= castinglist.begin(), 
            ie = castinglist.end(); it!=ie ; ++it){
        
        if (Instruction * mycastinst = dyn_cast<Instruction>(*it)){
            if (!mycastinst->getParent()) {
                mycastinst->insertAfter (insertAfterMe);
            }
        }
        else if (isa<Constant>(*it)) {
            //mycastconst->insertAfter (insertAfterMe);
        }
        else {
            errs()<<"Neither cast inst nor constant\n";
            exit(0);
        }
    }  
} 

unsigned 
Framer::getFramerTypeID (Type* ty)
{
  #ifdef ENABLE_SPACEMIU

    return getIdx (AllTypeList, ty); 
  
  #else 
    
    unsigned tID= 0;

    if ( StructType* st= dyn_cast<StructType>(ty)){
        
        int sid = getUserStructTypeID(st);  
        assert(sid!=-1 && "wtf is this?\n");
        tID = FramerBasicTyCount + sid;  
    }
    else if (IntegerType* intT= dyn_cast<IntegerType>(ty)) {
        int intid = getUserIntegerTypeID(intT); 
        if (intid==-1) {
            errs()<<"ERROR. ty: "<<*ty<<", int size: "<<intT->getBitWidth()<<"\n";
        }
        assert(intid!= -1 && 
                "cannot recognize the integer type. (check int type's bitwidth)\n");
        tID = llvmbasicTyCount + intid; 
    }
    else {
        tID= ty->getTypeID();
    }

    return tID;
  
  #endif
    
}


#ifdef ENABLE_TRACK_ARRAYS            

Instruction* 
Framer::doArrayAllocaInst (AllocaInst * AI, 
                          Instruction * successorInst, 
                          bool notDynamicArray,
                        #ifdef ENABLE_SPACEMIU  
                          vector <AllocaInst*> & LocalUnions, 
                        #endif
                          Module &M)
{
    //FRAMER_forall_alloca (void * locationOfAllocatedObject, uint64_t numElems, enum BASICType allocatedTypeID, unsigned numBytesPerElem )
    // TODO This is only for array of basictypes. Add struct type for elem... ALSO TODO merge this with doprimitivealocainst? duplicated code lines..


    Function * hook     = M.getFunction ("FRAMER_forall_alloca");
    Type * typeOfElem   = getTypeOfElemOfArray (AI->getAllocatedType());
    unsigned FramerTyID = getFramerTypeID (typeOfElem); 
    unsigned numBytes   =  Framer::getBitwidth(typeOfElem)/8;
    assert(numBytes!=0 && "numBytes is not zero\n");
    
    AllocaInst * paddedAI;
    GetElementPtrInst* origObj;

    if (!notDynamicArray) {
        return nullptr;
    }
    if (notDynamicArray){ 
        //--- to wrap an object
        dbg(errs()<<"doing alloca: "<<*AI<<"\n";)
        vector<Type*> paddedObjTyList= {HeaderTy, AI->getAllocatedType()};
        StructType* paddedTy= StructType::create(M.getContext(), 
                                paddedObjTyList,"paddedStruct", true);

        paddedAI= new AllocaInst (paddedTy, AI->getName(), AI);
        paddedAI->setAlignment(16); //for memset. sometimes memset presume alignment 16.
        
        vector<Value*> idx={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                            ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
        origObj= GetElementPtrInst::CreateInBounds (paddedTy,
                                               paddedAI,
                                               idx,
                                               "ptrToOrignalObj",
                                               AI);

    }
    else {
        errs()<<"AI: dynamic array.. it may cause bug errors (10) again..\n"; 
        exit(0);
        Instruction* addby2=nullptr;
         
        if ((uintptr_t)(Framer::getBitwidth(AI->getAllocatedType())) >= headerTySize) {
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
        
        dbg(errs()<<"paddedAI:\t"<<*paddedAI<<"\n";)
        vector<Value*> idx={
                            ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
        origObj= GetElementPtrInst::Create (AI->getAllocatedType(),
                                            paddedAI,
                                            idx,
                                            "ptrToOrignalObj",
                                            AI);
    }
    //--------- 

    Value * numElems       = getArraySize(AI, hook->getFunctionType()->getParamType(1));
    Value * typeIDOfElem   = constructValueFromFunc (FramerTyID, hook, 2);
    Value * numBytesPerElem= constructValueFromFunc (numBytes, hook, 3);

    vector<Value *> arglist;

    pushtoarglist (successorInst, 
                   hook->getFunctionType()->getParamType(0), 
                   origObj,//locationOfAllocatedObject, 
                   arglist,M);
    pushtoarglist (successorInst, 
                   hook->getFunctionType()->getParamType(1), 
                   numElems, 
                   arglist,M);
    pushtoarglist (successorInst, 
                   hook->getFunctionType()->getParamType(2), 
                   typeIDOfElem, 
                   arglist,M);
    pushtoarglist (successorInst, 
                   hook->getFunctionType()->getParamType(3), 
                   numBytesPerElem, 
                   arglist,M);

    CallInst * CI = CallInst::Create (hook, arglist, "");
    
    Instruction* typeRestoringPtrForReplacedUse= 
        castAndreplaceAllUsesWith (AI, CI);
    
    insertCastInstForArg (successorInst, arglist);
    CI->insertBefore (successorInst);
    
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter (CI); 
    }
  
  #ifndef ENABLE_SPACEMIU

  //  insertEpilogueOfFunc (CI, M);//, postDT);
  
  #endif

  #ifdef ENABLE_SPACEMIU  
    
    insertLocalUnionsList (paddedAI, LocalUnions);
  
  #endif
  
    dbg(errs()<<"exiting array alloca..\n";)
    return AI;
}

#endif

/* not used 
Value * Framer::getArrayEndAddress 
                (Value * baseAddr, unsigned numBitsOfElemTy, Value * numArrayElements, 
                 Type * typeToConvertTo, Instruction * insertBeforeMe, Module & M)
{
    IntegerType * my64IntTy = Type::getInt64Ty (M.getContext());
    
    ConstantInt * numByteOfElem = ConstantInt::get(my64IntTy, (numBitsOfElemTy/8));
    PtrToIntInst * baseAddrInInt = new PtrToIntInst (baseAddr, my64IntTy, "", insertBeforeMe);
    Instruction * totalNumBytes = 
                                BinaryOperator::Create (Instruction::Mul, numByteOfElem, numArrayElements, "", insertBeforeMe);
    
    Instruction * addTotalByteNumToBaseAddr = 
                               BinaryOperator::Create (Instruction::Add, baseAddrInInt, totalNumBytes, "", insertBeforeMe);
    IntToPtrInst * endAddress = new IntToPtrInst (addTotalByteNumToBaseAddr, typeToConvertTo, "", insertBeforeMe); 
     
    return endAddress;
}
*/
/*
unsigned Framer::getPrimTyBits (unsigned Typeid)
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
*/
/*
uint64_t Framer::getBitwidthOfStruct ( StructType * STy )
{
    if (!STy->isSized()) {
        errs()<<"structure "<<*STy<<"is not sized!! \n";
        exit(0);
    }
    const StructLayout * strtlayout = dlayout->getStructLayout (STy);
    return (unsigned)strtlayout->getSizeInBits();

}
*/

unsigned Framer::getBitwidth (Type * allocatedType)
{
    /// #Bits of element type. (e.g. int->32, struct->sum of member bits, 
    /// array->#bits of array element. 
    /// (outmost element, if the array is array of array...)
    unsigned allocatedTyID = allocatedType->getTypeID();
     
    if (( allocatedTyID > Type::VoidTyID && allocatedTyID < Type::PPC_FP128TyID) ){
        return getPrimTyBits (allocatedTyID); //TODO. maybe we can use llvm's func ?
    }
    else if (IntegerType * intTy = dyn_cast<IntegerType>(allocatedType)) {
        return intTy->getBitWidth();
    }
    else if (StructType * structTy = dyn_cast<StructType>(allocatedType)) {
        return (unsigned) getBitwidthOfStruct (structTy, dlayout);
    }
    else if (ArrayType * arrayTy = dyn_cast<ArrayType>(allocatedType)) {
        return (unsigned)(arrayTy->getNumElements())*Framer::getBitwidth(arrayTy->getElementType()); 
    }
    else if (VectorType * vecty= dyn_cast<VectorType>(allocatedType)) {
        //if (vecty->getBitWidth()!=0) {
        //    return vecty->getBitWidth();
        //}
        //else {
        return (unsigned)(vecty->getNumElements())*Framer::getBitwidth(vecty->getElementType()); 
            //}
    }
    //     else {
    //        errs()<<"1. what type is this??"<<*allocatedType<<"\n";
    //        exit(0);
    //    }
    //}
    else if (isa<PointerType>(allocatedType)) {
        assert(dlayout->getPointerSizeInBits()==64 && "not 64?\n");
        return dlayout->getPointerSizeInBits();
    }
    else {
        assert (isa<FunctionType>(allocatedType));
        errs()<<"cast: function type in getBitwidth\n";
        return 0;
        //exit(0);
    }
}


bool Framer::isItsUser (Value * useuser, User * useruser)
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
Instruction* Framer::castAndreplaceAllUsesWith(Value * originalPtr, 
                                               Value* modifiedPtr)
{
    dbg(errs()<<"INSIDE castAndreplaceAllUsesWith\n";)
    /// restoring tagged_pointer back to original ptr is inserted 
    /// right before the first use.
    /// there are other cases of replacing origPtr. 
    /// such as malloc, calloc, etc, and GEP is not replaced?
    
    Instruction* bitcastFromModifiedToOrig = nullptr;
  
    if (originalPtr->getType()==modifiedPtr->getType() 
        && !isa<Constant>(originalPtr)) { 
        /*replace all occurrences of original ptrs with the modified AI/GV. 
        Note that use of original_ptr in the hook func call is also replaced! */
        // restore a ptr in the hook function, which is modifiedAI/modifiedGV. 
      
        originalPtr->replaceAllUsesWith (modifiedPtr);
    }
    else if (originalPtr->getType() != modifiedPtr->getType()){
        bitcastFromModifiedToOrig= 
            new BitCastInst (modifiedPtr, originalPtr->getType(), "");
        
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
                    (&*currentUse)->set(bitcastFromModifiedToOrig);
                }
                else {
                    ;
                }
            } 
            //else if (ConstantExpr* constUser= dyn_cast<ConstantExpr>(user)) {
            else if (isa<ConstantExpr>(user)) {
                assert(isa<Constant>(modifiedPtr) && "modifiedPtr must be constant\n");
                //Constant* bitcastConstant=
                //    ConstantExpr::getPointerBitCastOrAddrSpaceCast(cast<Constant>(modifiedPtr), 
                //                                                    (*currentUse)->getType());
                //constUser->handleOperandChange (*currentUse, bitcastConstant); 
                (&*currentUse)->set(bitcastFromModifiedToOrig);
                errs()<<"should replace use, not change uses (can be plural) of the user??\n"; 
                exit(0);
            }
            else {
                errs()<<"what is this?? Exiting..\n";
                exit(0);          
            }
            currentUse = nextUse;
        }
    }
      
    //PointersAreTagged = true;
    dbg(errs()<<"exiting castAndreplaceAllUsesWith... \n";)
    return bitcastFromModifiedToOrig; 
}
/*
static unsigned 
getopidx (User *user, Use * op)
{
    User::op_iterator it (op);
    assert(it!=user->op_end() && "value not found in op_list\n");
    return it - user->op_begin();
}
*/

/*
static ConstantAggregate* 
getNewConstAggr (int opnum, Constant * CA, Constant * newGV) 
{
    assert(isa<ConstantAggregate>(CA) && "CA not ConstantAggregate\n");
   
    /// create array with GV replaced with newGV. 
    vector <Constant*> elems;
    for (User::op_iterator it=CA->op_begin(),ie=CA->op_end();it!=ie;++it){
        elems.push_back(cast<Constant>(&*it->get())); 
    } // fill elems from CA. and then replace opnum's elem.
    elems.at(opnum)= newGV;
    
    Constant * replica=nullptr;
    
    if (ConstantStruct * CStrt=dyn_cast<ConstantStruct>(CA)) {
       replica= ConstantStruct::get(CStrt->getType(),elems); 
    }
    else if(ConstantArray * CArr=dyn_cast<ConstantArray>(CA)){
        replica= ConstantArray::get(CArr->getType(), elems); 
    }
    else if (isa<ConstantVector>(CA)){
        replica=ConstantVector::get(elems);
    }
    else {
        errs()<<"FRAMER:: What case is this? getNewConstAggr\n";
        exit(0); 
    }
    return cast<ConstantAggregate>(replica);
}
*/

/// CU == constant_expr or aggr (orig_gv) form.
/*static Constant* 
getNewConstExpr (Use * use, Constant* newGV, 
            GlobalVariable* origGV, vector <Constant*>& oplist)
{      // use: bitcast (oldgv to ty) 
    if (oplist.empty()) {
        return (cast<Constant>(&*use)); 
    }
    Constant* CU= cast<Constant>(&*use); 
    Constant* replica= CU; 
    int opnum=0;
    
    for (User::op_iterator it= CU->op_begin(), ie=CU->op_end(); it!=ie; ++it) { 
        //iterating numOperands of the operator
         
        if ((&*it)->get()==origGV) {
            if (isa<ConstantExpr>(CU)) {
                replica= cast<ConstantExpr>(replica)->getWithOperandReplaced(opnum, newGV); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                replica= getNewConstAggr(opnum, replica, newGV); 
            }
        }
        else if (isa<ConstantExpr>(&*it)||isa<ConstantAggregate>(&*it)) { 
            Constant * itex= cast<Constant>(&*it);
            oplist.push_back(itex);
            
            Constant * temp= getNewConstExpr(it,newGV,origGV,oplist);

            if (temp == itex) {
                opnum++;
                continue;
            }
            if (isa<ConstantExpr>(CU)) {
                replica= (cast<ConstantExpr>(replica))->getWithOperandReplaced(opnum,temp); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                replica= getNewConstAggr(opnum, replica, temp);
            }
        }
        else if (User * UU=dyn_cast<User>(&*it)) { // having leaves  
            if (UU->getNumOperands()>=2) {
            errs()<<">> what case is this? CU:: "<<*CU<<"\n";
                exit(0);
            }
        }
        opnum++;
    }
    assert(opnum==CU->getNumOperands() && "CU!=getnumops!!\n"); 
    oplist.pop_back();   
    return replica; 
}
*/

/*
static Constant * 
getReplacement (Use* use, Constant* newGV, 
                GlobalVariable * origGV)
{ //use's form constexpr(orig_gv) or orig_gv. definitely having origGV inside.

    if (&*use->get()==origGV) {
        assert(isa<GlobalVariable>(&*use) && "Use is not GV!\n");
        return newGV; 
    }
    
    assert(!isa<GlobalVariable>(&*use) 
    && "FRAMER ERROR.for this case, it should have been returned.\n");
    
    if (isa<ConstantExpr>(&*use)||isa<ConstantAggregate>(&*use)) {
        vector <Constant*> oplist;
        oplist.push_back(cast<Constant>(&*use)); 
        return getNewConstExpr(&*use, newGV, origGV, oplist); 
    }
    else { 
        errs()<<"Use is Neither GV nor CE. USE: "<<**use<<"\n"; 
        exit(0);    
    }
}
*/

/// CU == constant_expr form CURRENTLY.
/*static Value* 
getNewInsForGV (Use * use, Constant* newGV, 
                GlobalVariable* origGV, vector <Constant*>& oplist,
                Instruction * init, 
                vector<Instruction*> & insToBeInserted)
{      // use: bitcast (oldgv to ty) 
    if (oplist.empty()) {
        return (cast<Constant>(&*use)); 
    }
    //Constant* CU= cast<Constant>(&*use); 
    //Constant* replica= CU; 
    
    ConstantExpr* CU= dyn_cast<ConstantExpr>(&*use); 
    assert(CU!=nullptr);

    Instruction* replicaIns= CU->getAsInstruction(); 
    
    int opnum=0;
    for (User::op_iterator it= CU->op_begin(), ie=CU->op_end(); it!=ie; ++it) { 
        //iterating numOperands of the operator
         
        if ((&*it)->get()==origGV) {
            if (isa<ConstantExpr>(CU)) {
               // TODO: if it's gep and safe access, replace with orig GV. 
               // replica= cast<ConstantExpr>(replica)->getWithOperandReplaced(opnum, newGV); 
                replicaIns->setOperand(opnum, init); //do check
                 
            }
            else if (isa<ConstantAggregate>(CU)) {
                //replica= getNewConstAggr(opnum, replica, newGV); 
                //replica->setOperand(opnum, getNewConstAggr(opnum, replica, newGV));
                replicaIns->setOperand(opnum, getNewConstAggr(opnum, CU, newGV)); 
                errs()<<"what case is this? \n";
                errs()<<"Const user is CAgg: "<<*CU<<"\n";
                errs()<<"replica: "<<*replicaIns<<"\n";
              //  exit(0);
            }
        }
        else if (isa<ConstantExpr>(&*it)||isa<ConstantAggregate>(&*it)) { 
            Constant * itex= cast<Constant>(&*it);
            oplist.push_back(itex);
            //Constant * temp= getNewInsForGV(it,newGV,origGV,
            Value * temp= getNewInsForGV(it,newGV,origGV,
                            oplist, init, insToBeInserted);

            if (temp == itex) {
                opnum++;
                continue;
            }
            if (isa<ConstantExpr>(CU)) {
                //replica= (cast<ConstantExpr>(replica))->getWithOperandReplaced(opnum,temp); 
                replicaIns->setOperand(opnum,temp); 
            }
            else if (isa<ConstantAggregate>(CU)) {
                //replica= getNewConstAggr(opnum, replica, temp);
                if (isa<Constant>(temp)) {
                    replicaIns->setOperand(opnum, getNewConstAggr(opnum, CU, cast<Constant>(temp)));
                }
                else {
                    errs()<<"do something. grr\n";
                    //exit(0);  
                }
            }
        }
        else if (User * UU=dyn_cast<User>(&*it)) { // having leaves  
            if (UU->getNumOperands()>=2) {
            errs()<<">> what case is this? CU:: "<<*CU<<"\n";
                exit(0);
            }
        }
        opnum++;
    }
    assert(opnum==CU->getNumOperands() && "CU!=getnumops!!\n"); 
    oplist.pop_back();
    insToBeInserted.push_back(replicaIns);   
    FramerLoads.insert(replicaIns);
    return replicaIns; 
}
*/

/*
static Value * 
getInstReplacement(Use* use, Constant* newGV, 
                   GlobalVariable * origGV, 
                   Instruction * init,
                   vector<Instruction*> & insToBeInserted)
{
    if (&*use->get()==origGV) {
        assert(isa<GlobalVariable>(&*use) && "Use is not GV!\n");
        exit(0);
        return newGV; //DO SOMETHING. 
    }
    
    assert(!isa<GlobalVariable>(&*use) 
    && "FRAMER ERROR.for this case, it should have been returned.\n");
    
    if (isa<ConstantExpr>(&*use)||isa<ConstantAggregate>(&*use)) {
         
//debug.s
if (isa<ConstantAggregate>(&*use)) {
    errs()<<"user is constAgg!: "<<*origGV<<"\n";
}
//debug.e

        vector <Constant*> oplist;
        oplist.push_back(cast<Constant>(&*use)); 
        return getNewInsForGV(&*use, newGV, origGV, 
                        oplist, init, insToBeInserted); 
      // use: bitcast (oldgv to ty) 
    }
    else { 
        errs()<<"Use is Neither GV nor CE. USE: "<<**use<<"\n"; 
        exit(0);    
    }

}
*/

/*
static void 
insertNewIns (vector<Instruction*> & insVec,
              Instruction * iuser)
{
    //push_back, and insert before iuser
    for(Instruction * ins : insVec) {
        ins->insertBefore(iuser);
    }
}*/

/*
static void 
handleUsesOfGV (Use* use, Constant* tagged, 
            Constant* untagged, GlobalVariable * origGV,
            GlobalVariable * gvTag)
{
    User * user= use->getUser();

    if(GlobalVariable * GVU= dyn_cast<GlobalVariable>(user)) {  
      
        Constant* replica= getReplacement(use, untagged, origGV);
        // ** replacing with untagged, since some forms of our tagged pointer 
        // not allowed as an GV initializer.
 
        GVU->setInitializer(replica);
    }
    else if(Instruction * IU= dyn_cast<Instruction>(user)) { 
    //TODO:RESTORE  assert(!isHookFamilyFunction(IU->getParent()->getParent()) && IU->getParent()); 
        
        if (isa<ConstantAggregate>(use->get())) {
            errs()<<"Constant agg: "<<*(use->get()); 
            errs()<<"Constant agg's IU: "<<*IU<<"\n";
        }
       
        // TODO: if (IU is GEP and safeAccess. replace it origGV) 
         
        LoadInst * li= new LoadInst(gvTag, "loadGVTag", IU);  
        FramerLoads.insert(li);
        
        vector<Instruction*> insToBeInserted;
        Value* replica= getInstReplacement(use,tagged, origGV, li, insToBeInserted);

        //TODO: insert ins in insToBeInserted before  
        insertNewIns (insToBeInserted, IU);
        insToBeInserted.clear();
        Value * castedReplica= replica; 
        unsigned myidx= getopidx(IU, use);
        if (IU->getOperand(myidx)->getType()!=replica->getType()) {
            BitCastInst * mybitcastinst= 
                new BitCastInst (replica, IU->getOperand(myidx)->getType(),"");
            mybitcastinst->insertBefore(IU);
            replica= mybitcastinst;
        }
        IU->setOperand(myidx, replica); //do something.
         
    }
    else if (isa<ConstantExpr>(user) || isa<ConstantAggregate>(user)) { 
        Constant * CU= cast<Constant>(user); 
        if (CU->use_empty()) {
            return;
        }
        int OrigNumUses= CU->getNumUses();
        int usenum=0;
        
        Use * currentUse= &*CU->use_begin();
        Use * nextUse= currentUse;
        
        while ( nextUse ) {
            nextUse = currentUse->getNext();

            handleUsesOfGV(currentUse,tagged,
                           untagged,origGV, gvTag); //TODO: check if it's user or cit 
            usenum++;
        
            currentUse = nextUse;
        }
        assert(usenum==OrigNumUses && "Not all uses traversed!\n");
    }
    else {
        errs()<<"GV replacement- something else. TODO\n";
        if (isa<Operator>(user)) errs()<<"--> Operator. do something\n";
        if (Constant* cuser= dyn_cast<Constant>(user)) {
            if (isa<ConstantAggregate>(cuser)) errs()<<"--> ConstantAggregate\n";
            else if (isa<ConstantData>(cuser)) errs()<<"--> ConstantAggregate\n";
            else if (isa<GlobalValue>(cuser)) errs()<<"--> GlobalValue\n";
            else errs()<<"Something else.\n";
        }
        exit(0); // do something
    }

}
*/


/*
static void 
castAndreplaceAllUsesWithForGV (GlobalVariable * originalGV, 
                Constant * taggedGV, Constant * untaggedGV,
                GlobalVariable * gvTG)
{
    Use * currentUse =  &*originalGV->use_begin();
    Use * nextUse = currentUse;
    
    errs()<<"\nGV orig: "<<*originalGV<<"\n"; 
    while ( nextUse ) {
               
        nextUse = currentUse->getNext();

        handleUsesOfGV (currentUse, taggedGV, untaggedGV, 
                        originalGV, gvTG); 
        
        currentUse = nextUse;
    }
}
*/

int Framer::insertLiteralToStructList (StructType* ty)
{
    allStructTyList.push_back(ty);
    return (int)(allStructTyList.size()-1);
}

int Framer::getUserStructTypeID (StructType* ty)
{
    int structtyid= -1; 
    vector<StructType*>::iterator it= find( allStructTyList.begin(),
                                            allStructTyList.end(), 
                                            ty);
    /// if it's identified struct ty. /// 
    if (it != allStructTyList.end()) {
        dbg(errs()<<"This exists in the list:: "<<*ty<<"\n";)
        structtyid= it - allStructTyList.begin();
    }
    /// not in the list, but sized struct. ///
    else if (ty->isSized()) { 
        assert(!ty->isOpaque() && "type is sized and opaque? \n");
        errs()<<"\ninserting new struct type--\n";
        errs()<<*ty<<"\n";
        structtyid= insertLiteralToStructList(ty);
    }
    else {
        errs()<<*ty<<":: not in the list, not sized. \n"; 
    }
    return structtyid;
}

int Framer::getUserIntegerTypeID (IntegerType* ty)
{
    unsigned intID= -1;
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
        case 1:  /// Jesus. i1 exists!!
            intID= 5; 
            break;
        case 48:
            intID= 6;
            break;
        case 24:
            intID= 7;
            break;
        default:
            errs()<<"Error, integer bitwidth is strange: " <<numBits<<"\n";
            break;
    }
    return intID;
}

Constant* Framer::constructAddressValue (Module &M, GlobalVariable* tab, unsigned subindex)
{
    Type* ty= tab->getType(); 
    
    Constant* idconst= ConstantInt::get(Type::getInt64Ty(M.getContext()), subindex); 
    Constant* entryAddr = 
        ConstantExpr::getInBoundsGetElementPtr(ty, tab, idconst); 
    errs()<<"wtf is this?\n";
    exit(0); 
    return entryAddr;
}

bool Framer::isFramerIntID (unsigned id)
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

static void
insertCompareSizeHook (vector<Value*> & arglist, 
                       Value * ptrop, // S/L's ptrop. possibly casted 
                       Instruction * ins,
                       Function * hook,
                       Module & M)
{
    GEPOperator * gep=dyn_cast<GEPOperator>(ptrop->stripPointerCasts());
    assert(gep!=nullptr);
    assert(gep->getNumIndices()==1);  
    
    CallInst * malloccall= dyn_cast<CallInst>(gep->getOperand(0)->stripPointerCasts());     
    if (malloccall==nullptr) {
        errs()<<"malloccall is null. gep op: "<<*gep->getOperand(0)<<"\n";
        errs()<<"  stripped: "<<*gep->getOperand(0)->stripPointerCasts()<<"\n";

    }
    assert(malloccall!=nullptr);
     
    Value * objsize= malloccall->getOperand(0);  
    Value * idx= gep->getOperand(1);
    unsigned tysizenum= 
        FramerGetBitwidth(cast<PointerType>(ptrop->getType())->getElementType(), dlayout)/8;
    Constant * tysize= 
        ConstantInt::get(hook->getFunctionType()->getParamType(2),
                        tysizenum, true);   
    unsigned elemsizenum=
        FramerGetBitwidth(cast<PointerType>(gep->getType())->getElementType(), dlayout)/8;
    Constant * elemsize= 
        ConstantInt::get(hook->getFunctionType()->getParamType(3),
                        elemsizenum, true);   
     
    //malloc size
    // idx * gep_typesize

    /*errs()<<"  objsize: "<<*objsize<<"\n";
    errs()<<"  idx: "<<*idx<<"\n";
    errs()<<"  tysize: "<<*tysize<<"\n";
    errs()<<"  elemsize: "<<*elemsize<<"\n";
    errs()<<"  ptrop: "<<*ptrop<<"\n";*/
    pushtoarglist(ins,hook->getFunctionType()->getParamType(0),
                    objsize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(1),
                    idx,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(2),
                    tysize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(3),
                    elemsize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(4),
                    ptrop, arglist,M); 
}

static void
insertCompareTypeHook (vector<Value*> & arglist, 
                       Value * ptrop, // S/L's ptrop. possibly casted 
                       Instruction * ins,
                       Function * hook,
                       Module & M)
{
    assert(isa<CallInst>(ptrop->stripPointerCasts())
            && "do something for COMPTYPEATRUNTIME\n"); 
    
    CallInst * malloccall= cast<CallInst>(ptrop->stripPointerCasts());     

    Value * objsize= malloccall->getOperand(0);  
    unsigned tysizenum= 
        FramerGetBitwidth(cast<PointerType>(ptrop->getType())->getElementType(), dlayout)/8;

//    errs()<<"\nS/L: "<<*ins<<"\n";
    //errs()<<"ptrop: "<<*ptrop<<"\n";
    //errs()<<"ptrop_: "<<*ptrop->stripPointerCasts()<<"\n";
    //errs()<<"objsize: "<<*objsize<<"\n";
    //errs()<<"ty: "<<*(cast<PointerType>(ptrop->getType())->getElementType())<<", tysize : "<<tysizenum<<"\n";

    Constant * tysize= 
        ConstantInt::get(hook->getFunctionType()->getParamType(1),
                        tysizenum, true);   

    pushtoarglist(ins,hook->getFunctionType()->getParamType(0),
                    objsize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(1),
                    tysize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(2),
                    ptrop, arglist,M); 
 
}

static void 
insertCompareHookArgs(vector<Value*> & arglist, 
                  Value * ptr, 
                  Instruction * ins,
                  Function * hook,
                  Module & M)
{
    GEPOperator * gep= dyn_cast<GEPOperator>(ptr->stripPointerCasts());
    assert(gep!=nullptr); 
    
    Type * pt= 
        cast<PointerType>(gep->getPointerOperand()->getType())->getElementType();
        //cast<PointerType>(gep->getPointerOperand()->stripPointerCasts()->getType())->getElementType(); 
        //TODO. apply this later! get the size of array from hook_alloca, hook_gv
        
    unsigned elemNum=0;

    if (isa<StructType>(pt)) {
        elemNum=cast<StructType>(pt)->getNumElements(); 
    }
    else if (isa<ArrayType>(pt)) {
        elemNum=(unsigned)cast<ArrayType>(pt)->getNumElements();  
    }
    else if (isa<VectorType>(pt)) {
        elemNum=(unsigned)cast<VectorType>(pt)->getNumElements();  
    }
    else {
        errs()<<"other type: "<<*pt<<"\n";
        errs()<<"gep: "<<*gep<<"\n";
        errs()<<"op (strip): "<<*gep->getPointerOperand()->stripPointerCasts()<<"\n";
        exit(0);
    }
    // ** This is perlbench having an array ptr bitcasted to [0*type] from [elem*type]
    if (elemNum==0) {
        pt= cast<PointerType>(gep->getPointerOperand()->stripPointerCasts()->getType())->getElementType();

        if (isa<StructType>(pt)) {
            elemNum=cast<StructType>(pt)->getNumElements(); 
        }
        else if (isa<ArrayType>(pt)) {
            elemNum=(unsigned)cast<ArrayType>(pt)->getNumElements();  
        }
        else if (isa<VectorType>(pt)) {
            elemNum=(unsigned)cast<VectorType>(pt)->getNumElements();  
        }
    }

    assert(elemNum!=0);
        
    Constant * esize= 
        ConstantInt::get(hook->getFunctionType()->getParamType(0), 
                    elemNum, true); 

    pushtoarglist(ins,hook->getFunctionType()->getParamType(0),
                    esize,arglist,M); 
    pushtoarglist(ins,hook->getFunctionType()->getParamType(1),
                    gep->getOperand(2),arglist,M); //2nd index.
    pushtoarglist(ins,hook->getFunctionType()->getParamType(2),
                    ptr,arglist,M); 
}

/*
bool Framer::isFramerStructID (unsigned id)
{
    bool isStruct;
    if (FramerBasicTyCount<=id && id < (FramerBasicTyCount+structTyCount)) {
        isStruct=true;
    }
    else{
        isStruct=false;
    }
    return isStruct;
}*/

/*
Constant* Framer::getFramerTyEntryAddress (Module &M, unsigned ftid)
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
}*/

Instruction* 
Framer::doPrimitiveAllocaInst(AllocaInst * AI, 
                              Instruction * successorInst, 
                            #ifdef ENABLE_SPACEMIU
                              vector <AllocaInst*> & LocalUnions, 
                            #endif
                              Module &M)
{

    //for struct alloca, get type of alloca. -> create struct-> replace all alloca uses. then replace itself.

    //perlbench
    if (StructType* st= dyn_cast<StructType>(AI->getAllocatedType())) {
        if (st->isOpaque()) {
            errs()<<"OPAQUE struct type. do not pad me. skip me later instead of exiting\n";
            errs()<<*st<<"\n";
            exit(0);
        }
        if (!st->isLiteral()) {
            if (st->getName().equals("struct.tm")) {
                errs()<<"struct.tm type: "<<*st<<"\n";
                errs()<<"  obj1: "<<*AI<<"\n";
                return nullptr;
            }
        }
    }
    if (PointerType *pt= dyn_cast<PointerType>(AI->getAllocatedType())) {
        if(StructType *myst= dyn_cast<StructType>(pt->getElementType())) {
            if (!myst->isLiteral()) {
                if (myst->getName().equals("struct.tm")) {
                    errs()<<"struct.tm pointer: "<<*pt<<"\n";
                    errs()<<"  obj2: "<<*AI<<"\n";
                    return nullptr;
                }
            }
        }

    }
    //perlbench

    Function * hook    = M.getFunction ("FRAMER_forall_alloca");
    unsigned FramerTyID= getFramerTypeID(AI->getAllocatedType()); 
    
    unsigned numBytes  = (Framer::getBitwidth(AI->getAllocatedType()))/8;
    assert(numBytes!=0 && "numBytes is zero\n");

//--- wrap the object in a struct  ------------ 
    //vector<Type*> paddedObjTyList= {HeaderTy, AI->getAllocatedType(), OffByOneTy};
    vector<Type*> paddedObjTyList= {HeaderTy, AI->getAllocatedType()}; //** deleted offbyone
    StructType* paddedTy= StructType::create(M.getContext(), paddedObjTyList, "paddedStruct", true);
    
    //Constant* nullHeader = Constant::getNullValue(HeaderTy);
    //Constant* nullPad = Constant::getNullValue(OffByOneTy);

    AllocaInst* paddedAI= 
        new AllocaInst (paddedTy, 
                        M.getDataLayout().getAllocaAddrSpace(), 
                        AI->getName(), AI);
    paddedAI->setAlignment(Align(16));
     
    dbg(errs()<<"PaddedAI: "<<*paddedAI<<"\n";)
    
    vector<Value*> idx={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
    GetElementPtrInst* origObj=  
        GetElementPtrInst::CreateInBounds(paddedTy,
                                        paddedAI,
                                        idx,
                                        "ptrToOrignalObj",
                                        AI);
    dbg(errs()<<"new GEP: "<<*origObj<<"\n";
        errs()<<"origObj type:: "<<*origObj->getType()<<"\n";)
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
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1),
                    numArrayElem, 
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2) , 
                    typeIDOfAllocatedObj, 
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3) , 
                    numBytesOfElemTy, 
                    arglist,M);

 #ifdef ENABLE_SPACEMIU  
   
    bool is_union= isUnionTy(AI->getAllocatedType());
    Value * constisUnionTy= 
            constructValueFromFunc(is_union, hook, 4); 
 
    pushtoarglist ( successorInst, 
                    hook->getFunctionType()->getParamType(4) , 
                    constisUnionTy, 
                    arglist,M);

  #endif

    CallInst * modifiedAI = CallInst::Create(hook, arglist, "");
    //vector<Value*> castinglist;
    Instruction* restoredPtr= 
        castAndreplaceAllUsesWith (AI, modifiedAI);
    
    insertCastInstForArg (successorInst, arglist);
    modifiedAI->insertBefore(successorInst);
    if (restoredPtr != nullptr) {
        restoredPtr->insertAfter(modifiedAI); //
    }
    
  //  insertEpilogueOfFunc (modifiedAI, M);

  #ifdef ENABLE_SPACEMIU  
    
    insertLocalUnionsList (paddedAI, LocalUnions);
  
  #endif

    return AI;
}

Instruction* 
Framer::doAllocaInst (AllocaInst* AI, 
                              Instruction* successorInst,
                            #ifdef ENABLE_SPACEMIU
                              vector <AllocaInst*> & LocalUnions, 
                            #endif
                              Module & M) 
{
    bool notDynamicArray= false;

    if (AI->use_empty()) {
        dbg(errs()<<"\tuse list empty. skipping..\n";)
        return nullptr;
    }
    //errs()<<"AI: "<<*AI<<"\n";
       
    Type * Ty = AI->getAllocatedType();
    Instruction* ToBeRemoved= nullptr;

    if (AI->isArrayAllocation() 
        || AI->getArraySize() != ConstantInt::get(AI->getArraySize()->getType(), 1)) 
       {
  #ifdef ENABLE_TRACK_ARRAYS
        notDynamicArray= false;
        
        if (AI->getArraySize() != ConstantInt::get(AI->getArraySize()->getType(), 1)) {
            errs()<<"This form may be -- a=alloca ty, elemNum. and Framer/SpaceMiu may be produce wrong hook args and new alloca. DO CHECK\n";
            exit(0);
        }
        
        ToBeRemoved= doArrayAllocaInst (AI, 
                                        successorInst, 
                                        notDynamicArray, 
                                      #ifdef ENABLE_SPACEMIU
                                        LocalUnions, 
                                      #endif
                                        M);
  #endif 
        return ToBeRemoved;
    }

    if (Ty->isFirstClassType()) { 
        
        if (Ty->isSingleValueType() ) {
            
            if (Ty->isVectorTy()) {
                errs()<<"ERROR: Alloca - single valued, vector type. do something \n"; 
                exit(0);
            }
            else if (!(Ty->isPointerTy())) {
                dbg(errs()<<"\tSKIP: non-pointer type.\n";)
                return ToBeRemoved; 
            }

            else {
                ;//doPrimitiveAllocaInst (AI, successorInst, M); 
                // doing nothing right now for non-array allocation. 
            }
        }
        else if (Ty->isAggregateType() ) {

            if (Ty->isArrayTy()) {

              #ifdef ENABLE_TRACK_ARRAYS            
                notDynamicArray= true;
                ToBeRemoved= 
                    doArrayAllocaInst(AI, 
                                      successorInst, 
                                      notDynamicArray, 
                                    #ifdef ENABLE_SPACEMIU
                                      LocalUnions,
                                    #endif
                                      M);//, postDT);
                return ToBeRemoved;
             
              #endif
            }

        #ifdef TRACK_STRUCT_ALSO 
        
            else if (Ty->isStructTy()) {
                ToBeRemoved= doPrimitiveAllocaInst (AI, 
                                                    successorInst, 
                                                    LocalUnions, 
                                                    M);
                return ToBeRemoved; 
            }
            else {
                errs()<<"Aggregated type allocated, but neither array nor struct. It is "<<*Ty<<"\nDo something here. \n";
                exit(0);
            }
       #endif
        }
    }
    else {
        errs()<<"Not a first class type! Exiting... do something for this. \n\n";
        exit(0);
    }
    return ToBeRemoved;
}

//ptr expects an operand (0) of load inst.
Value *  Framer::getOriginalAlloca (Value * ptr) 
{
    StringRef hookName = "";
    
    if (CallInst * callHook = dyn_cast<CallInst>(ptr)) { // The case of AI ty == modified AI Ty
        hookName = callHook->getCalledFunction()->getName();

        if (hookName.startswith(StringRef("FRAMER_forall_alloca")) || 
            hookName.startswith(StringRef("FRAMER_forall_global_variable"))) {

            dbg(errs()<<"\tis Modified one 1.\n";
                errs()<<"\treturining orig: "<<*callHook->getArgOperand(0)<<"\n";)
            
            return callHook->getArgOperand(0);
       
        }
        else {
            errs()<<"Loaded from CallInst? .\n";
            exit(0);
        }
    }
    else if (CallInst * callHook = dyn_cast<CallInst>(cast<User>(ptr)->getOperand(0))) { // AI Ty != modified AI Ty
        hookName = callHook->getCalledFunction()->getName();

        if (hookName.startswith(StringRef("FRAMER_forall_alloca")) || 
            hookName.startswith(StringRef("FRAMER_forall_global_variable"))) {

            dbg(errs()<<"\tis Modified one 2.\n";
                errs()<<"\tCallInst Hook: "<<*callHook<<"\n";
                errs()<<"\tCallInst's arg: "<<*callHook->getArgOperand(0)<<"\n";
                errs()<<"\tCallinst's arg(bitcast)'s op(0): "<<*cast<BitCastInst>(callHook->getArgOperand(0))->getOperand(0)<<"\n";)

            Value * OriginalPtr = cast<BitCastInst>(callHook->getArgOperand(0))->getOperand(0);
            return OriginalPtr;
        }
        else {
            errs()<<"Loaded from CallInst? seems wrong..\n";
            exit(0);
        }
    }
    else {
        dbg(errs()<<"Not a modified Alloca family. so Skip...\n";)
        return nullptr;
    }
     
    
}

/* not used
void Framer::restoreModifiedPtr (LoadInst * LI) 
{
    Value * MaybeModifiedPtr = LI->getOperand(0);

    // *** from here, implementation of restoring an original alloca in load inst. ****
    Value * originalPtr = getOriginalAlloca (MaybeModifiedPtr);
    if (originalPtr != nullptr ){
        LI->replaceUsesOfWith (MaybeModifiedPtr, originalPtr); 
    }

}*/

void Framer::castAndreplaceUsesOfWithBeforeInst(Instruction* user, 
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
        //unlike alloca, FRAMER_load and bitcast should be inserted BEFORE load inst.
        //replace 'from' with mybitcastinst which casts toThis (modifiedptr) to 'from's type.
        user->replaceUsesOfWith (from, mybitcastinst);

    }
}

/*
static Value * 
ismalloc (Value * p) 
{
// p, possibly casted
// returns sizeOfObj of malloc or nullptr 
    if (isa<CallInst>(p->stripPointerCasts())) {
        CallInst * ci= cast<CallInst>(p->stripPointerCasts());
        Function * F= ci->getCalledFunction();
        if (F==nullptr) return nullptr; 
         
        if (F->getName().equals("malloc")) {
            return ci->getOperand(0); 
        }
    }
    return nullptr;            
}
*/

/*
static Value* isHookedAllocaOrGV(Value * p) 
{
    //alloca
    if (isa<CallInst>(p->stripPointerCasts())) { 
        CallInst * CI= cast<CallInst>(p->stripPointerCasts());
        Value * CV= CI->getCaller();
        if (isa<Function>(CV)) {
            Function * F= cast<Function>(CV);
            if (F->getName().startswith("FRAMER_forall_alloca")) { //for alloca
                Value * myalloc= dyn_cast<GEPOperator>(CI->getOperand(0)->stripPointerCasts()); 
                assert(myalloc!=nullptr && "alloca op 0 is null\n");  
                return myalloc; 
            }
            else {;}
        }
    }
    // GV
    else if (UnaryConstantExpr * itp= dyn_cast<UnaryConstantExpr>(p)){
       //  paddedGV's elems are intptr's operand(0), 
       //     becuz as of cast inttoptr, the cast instructions are merged. 
        
        vector<Value*>::iterator it; //TODO: add paddedGV in doGV. (check bitcast. strip or not) 
        it= find (paddedGVs.begin(), paddedGVs.end(), itp->getOperand(0)); //p or ptr?
        if(it != paddedGVs.end()) {
            //Value * myalloc= dyn_cast<GEPOperator>(itp->getOperand(0)->stripPointerCasts()); 
            //assert(myalloc!=nullptr && "gv op 0 is null\n");  
            return itp;
        }
    }
    return nullptr;
}
*/

/*
static unsigned getStaticOffset (GEPOperator * gep, Value * obj)
{
    // obj is thin base of allocation // 
    
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
            assert (SEQT->getNumElements()>idx && "out of bound\n"); // check overflow 
            uint64_t elemsize= dlayout->getTypeSizeInBits(SEQT)/8;
            offset=offset+ (idx*elemsize);
            upT= SEQT->getElementType(); 
        }
        else if (StructType * SUBCT= dyn_cast<StructType>(upT)){
            const StructLayout * SL= dlayout->getStructLayout(SUBCT);
            offset=offset+SL->getElementOffset(idx); //update offset
            assert (SUBCT->getNumElements()>idx && "out of bound\n"); // check overflow 
            upT= SUBCT->getElementType(idx);
        }
        else {;}
    }
    return (unsigned)offset; //delete later

}*/

Value* 
Framer::getAssignment(LoadInst * LI, DominatorTree & dt)
{
    Value * ptr=LI->getPointerOperand(); 
    StoreInst * mydominator=nullptr; 
    for (Value::user_iterator it=ptr->user_begin();it!=ptr->user_end();++it){
        if (StoreInst * SI=dyn_cast<StoreInst>(*it)) {
            Value * val= SI->getPointerOperand();
            if (val!=ptr || LI->getFunction()!=SI->getFunction()) {
                continue;  
            }
            // (1) check if it's an immediate assignment.
            if (dt.dominates(SI,LI)) { 
                if (mydominator==nullptr || dt.dominates(mydominator, SI)) {
                    mydominator=SI;
                }
            }
        }
    }
    if (mydominator!=nullptr) {
        return mydominator->getValueOperand();
    }
    return nullptr;

}
bool 
Framer::checkSafeWithDomTree (Value * op, DominatorTree & dt) 
{
    // op is cast-stripped ptr op of SI/LI

    if (LoadInst * li= dyn_cast<LoadInst>(op)) { //li == %1 == op
        Value* itsval= getAssignment(li, dt);
        if (itsval==nullptr) {
            return false;
        }
        if (isSafePtr(itsval)) {
            return true;      
        }
        else {
            // if (double pointers or triple pointers? anyway) 
            // then return true? since we tag typeID only for alloca or global referencing  
            errs()<<"check..\n";
            
            exit(0);
        }   
        //  }
    }
    /*else if (PHINode * pn=dyn_cast<PHINode>(op)){
        for (int i=0;i<pn->getNumIncomingValues();i++) {
            ; 
        }
    } */
    else {
    }
    return false;
}
/*bool Framer::isStaticInBound (unsigned offset, unsigned sizeToAccess, unsigned totalsize)
{
    if (offset+sizeToAccess>totalsize){
        return false;    
    }
    return true;
}
*/

//unsigned Framer::getTotalSize(GEPOperator * gep)
/*
static unsigned 
getTotalSize(GEPOperator * gep, const DataLayout * dlayout)
{
    Type * upT= cast<CompositeType>((cast<PointerType>(gep->getPointerOperandType()))->getElementType());; 
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
    else {
        errs()<<"totalsize. "<<*upT<<"\n"; exit(0);
    }
}
*/
bool Framer::isuntaggedPtr(Value * ptrop)
{
    if (isa<GEPOperator>(ptrop)) return false;
    
    if (isa<LoadInst>(ptrop)) {
        LoadInst * li= cast<LoadInst>(ptrop);
        if (isa<LoadInst>(li->getPointerOperand())) {
            Value * val= cast<LoadInst>(ptrop)->getPointerOperand();
            if (isa<GlobalVariable>(val->stripPointerCasts()) 
                || isa<AllocaInst>(val->stripPointerCasts())) {
                errs()<<"do something 2.\n";
                exit(0);
            }
        }
        else {
            if(isa<AllocaInst>(li->getPointerOperand())
                    ||isa<GlobalVariable>(li->getPointerOperand())){
                PointerType * pty= dyn_cast<PointerType>(li->getType()); 
                    // should be pointer.
                assert(pty!=nullptr);
                Type * ty= pty->getElementType();
                //if (!isa<CompositeType>(ty)) {
                if (isa<IntegerType>(ty)) {
                    errs()<<"SL op_li: "<<*li<<"\n";
                    errs()<<"untag2: "<<*li->stripPointerCasts()<<"\n";
                    return true; 
                }
            }
        }
    }
    else {
        errs()<<"val3: "<<*ptrop<<"\n";
    }
    return false;
}
/*
// toUntag (-1), do nothing (0), tobechecked (1) 
// op_'s type is always pointer type.
static unsigned 
isSafeAccess (Value * op_, Module & M, bool isMemAccess,
              vector <Value*> & paddedGVs) //op: load/store's ptr op
{
    Value * op=op_->stripPointerCasts();
    
    if (isHookedAllocaOrGV(op, paddedGVs)) {
        return SAFESTATICALLY;
    }
    Value * mallocop= ismalloc(op_);
    if (mallocop!=nullptr) {
        
        return SAFESTATICALLY;
    }
    if (GEPOperator * gep=dyn_cast<GEPOperator>(op)) {  
        dbg("skip. safe gep\n";);
        return __isSafeAccess(gep, M, isMemAccess); 
    }
    else {

/// commented since I am doubtful if this will /////////
/// make a big difference for performance.      /////////
/// can try later                               /////////
//        if (checkSafeWithDomTree(op, dt)) { 
//            errs()<<"Read todo\n"; //TODO. bring case splitting (if load stuff) to here.
//            return true;
//        }
    } 
    return 0;
}
*/

static void insertExitCall (Instruction * ins, Module & M)
{
//debug.s
    if (isa<LoadInst>(ins)) {
        LoadInst * li= cast<LoadInst>(ins);
        errs()<<"\top raw: "<<*li->getPointerOperand()<<"\n"; 
        errs()<<"\top unt: "<<*li->getPointerOperand()->stripPointerCasts()<<"\n";
    }
    if (isa<StoreInst>(ins)) {
        StoreInst * si= cast<StoreInst>(ins);
        errs()<<"\top raw: "<<*si->getPointerOperand()<<"\n"; 
        errs()<<"\top unt: "<<*si->getPointerOperand()->stripPointerCasts()<<"\n";
    }
//debug.e
    Function * hook= M.getFunction("FRAMER_supplementary_exit"); 
    vector<Value*> arglist;
    CallInst * ci= CallInst::Create(hook, arglist, "");
    //insertCastInstForArg (ins, arglist); 
    ci->insertBefore(ins);
} 


void
Framer::doLoadInstForSpaceMiu (LoadInst * LI, 
                            Instruction * sucIns, 
                            DominatorTree & dt, 
                            AAResults & AA,
                            vector <AllocaInst*> & ais,
                            Module &M)
{
  
  Function * hook= nullptr;
  vector<Value *> arglist;

  bool justUntag= justToBeUntagged (LI->getPointerOperand(),
                                    AA, ais, GVUnions, HeapUnions, 
                                    AllTypeList, SafeCasts, M); 
   
  if (justUntag) {
      hook= M.getFunction ("FRAMER_untag_ptr_2");

      pushtoarglist(LI, 
              hook->getFunctionType()->getParamType(0), 
              LI->getPointerOperand(),     
              arglist,M);
  }
  else {
//      errs()<<"## LOAD has alias:: "<<*LI<<"\n";
//      errs()<<"   --> do type check\n";
        
      //hook= M.getFunction ("FRAMER_type_update_at_memREAD");
   errs()<<" FRAMER_type_check_at_memREAD!!! exiting. \n";
   exit(0);

      hook= M.getFunction ("FRAMER_type_check_at_memREAD");
      
      Type * ty= LI->getPointerOperand()->getType(); 
        
      short tid= getIdx(AllTypeList, ty);
        
      assert(tid >=0); 

      pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(0), 
                LI->getPointerOperand(), arglist,M);

      Value * desttid= 
          constructValueFromFunc (tid, hook, 1);
      pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(1), 
                desttid, arglist,M);
      
      pushtoarglist (sucIns, 
              hook->getFunctionType()->getParamType(2), 
              constructValueFromFunc(MaxOffset, hook, 2), 
              arglist,M);
  } 

  CallInst * modifiedPtr = CallInst::Create(hook, arglist, "");

  insertCastInstForArg (LI, arglist); 
  modifiedPtr->insertBefore(LI);
  castAndreplaceUsesOfWithBeforeInst (LI, 
          LI->getPointerOperand(), 
          modifiedPtr);

}


/*  doLoadInstForSpaceMiu : enabled when SPACE Miu is on */
/*
void
Framer::doLoadInstForSpaceMiu (LoadInst * LI, 
                            Instruction * sucIns, 
                            DominatorTree & dt, 
                            AAResults & AA,
                            vector <AllocaInst*> & ais,
                            Module &M)
{
    Function * hook= nullptr;
    vector<Value *> arglist;
   
    BitCastOperator * bitcastop= dyn_cast<BitCastOperator>(LI->getPointerOperand()); 
    PointerType * ptrTy= nullptr;
   
    if (bitcastop) {
        ptrTy= dyn_cast<PointerType>(bitcastop->getSrcTy());
        assert(ptrTy!=nullptr);
    }
 
  //  PointerType * ptrTy= dyn_cast<PointerType>(LI->getOperand(0)->getType());
  //  assert(ptrTy!=nullptr);
     
    if( !bitcastop
        || !isUnionTy(ptrTy->getElementType())  
        || !isAliasWithUnionObj(LI->getOperand(0), AA, ais, GVUnions, M)) {

        hook= M.getFunction ("FRAMER_untag_ptr");

        pushtoarglist(LI, 
                hook->getFunctionType()->getParamType(0), 
                LI->getOperand(0),     
                arglist,M);
    }
    else {
        errs()<<"## LOAD has alias:: "<<*LI<<"\n";
        errs()<<"  -> hook type check\n";
         
        hook= M.getFunction ("FRAMER_type_check_at_memREAD");

        PointerType * desti= 
            dyn_cast<PointerType>((LI->getOperand(0))->getType());
        
        assert(desti);
           
        short desttid= getIdx(AllTypeList, desti->getElementType());
        
        unsigned destTsize= 
            Framer::getBitwidth(desti->getElementType())/8; 

        assert(desttid >=0); 

        // *****  

        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(0), 
                LI->getOperand(0), arglist,M);

        Value * dest= 
            constructValueFromFunc (desttid, hook, 1);
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(1), 
                dest, arglist,M);

        Value * constmaxtysperoff= 
            constructValueFromFunc(maxtysperoff, hook, 2);
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(2), 
                constmaxtysperoff, arglist,M);

        Value * constmaxoffsperty= 
            constructValueFromFunc(maxoffsperty, hook, 3); 
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(3), 
                constmaxoffsperty, arglist,M);

        Value * consttblentrysize= 
            constructValueFromFunc(tblentrysize, hook, 4); 
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(4), 
                consttblentrysize, arglist,M);

        Value * constdestTsize= 
            constructValueFromFunc(destTsize, hook, 5); 
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(5), 
                constdestTsize, arglist,M);
      
        pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(6), 
                constructValueFromFunc(MaxOffset, hook, 6), 
                arglist,M);
     
        // add more args.
    } 

    CallInst * modifiedPtr = CallInst::Create(hook, arglist, "");

    insertCastInstForArg (LI, arglist); 
    modifiedPtr->insertBefore(LI);
    castAndreplaceUsesOfWithBeforeInst (LI, 
            LI->getOperand(0), 
            modifiedPtr);
}
*/

void 
Framer::doLoadInst (LoadInst * LI, 
                            Instruction * successorInst, 
                            DominatorTree & dt, 
                            AAResults & AA,
                            Module &M)
{
    tempload++; 
    Function * hook= nullptr; 
    vector<Value *> arglist;

#ifdef STORE_ONLY_CHECK
    hook= M.getFunction ("FRAMER_untag_ptr_2");
    pushtoarglist(LI, 
            hook->getFunctionType()->getParamType(0), 
            LI->getOperand(0),     
            arglist,M);
#else
    // SAFE access. skipping mem_check. instead insert ** untag_ptr **
    dbg(errs()<<" hooking... ptrop: "<<*LI->getPointerOperand()<<"\n";)
   
    //errs()<<" hooking! load!??\n"; 
    unsigned issafeaccess= isSafeAccess(LI->getPointerOperand(), M, 1, paddedGVs); 
    if (issafeaccess==SAFESTATICALLY) { 
        dbg(errs()<<" 1\n";)
        temploadsafe++;
        hook= M.getFunction ("FRAMER_untag_ptr_2");
        pushtoarglist(LI, 
                      hook->getFunctionType()->getParamType(0), 
                      LI->getOperand(0),     
                      arglist,M);
    }
  #ifndef DISABLE_CHEAP_CHECKS 
    else if (issafeaccess==COMPAREIDXATRUNTIME) {
        dbg(errs()<<" 2\n";)
      // compare size and idx.  
        temploadsafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_idx");
        assert(hook!=nullptr);
        insertCompareHookArgs(arglist, LI->getOperand(0), LI, hook, M); 
    }
    else if (issafeaccess==COMPTYPEATRUNTIME) {
        dbg(errs()<<" 3\n";)
      // compare memaccess type size and heap objsize.  
        temploadsafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_type");
        assert(hook!=nullptr);
        insertCompareTypeHook(arglist, LI->getPointerOperand(), LI, hook, M); 
    }
  #endif
    else if (issafeaccess==COMPSIZEATRUNTIME) {
        dbg(errs()<<" 4\n";)
      // compare memaccess size and heap objsize.  
        temploadsafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_size");
        assert(hook!=nullptr);
        insertCompareSizeHook(arglist, LI->getPointerOperand(), LI, hook, M); 
    }
    else if (issafeaccess==OUTOFBOUNDATRUNTIME) {
        dbg(errs()<<" 5\n";)
        insertExitCall(LI,M);
        return; 
    } 
    else { 
        dbg(errs()<<" 6\n";)
        hook= M.getFunction ("FRAMER_forall_load");
        
        unsigned typeSizeOfLoadedContent= 
            Framer::getBitwidth(LI->getType())/8;
        
        assert (typeSizeOfLoadedContent!=0 
                && "typeSizeOfLoadedContent is zero\n"); 
        
        Value * numBytesOfLoadedContent= 
            constructValueFromFunc (typeSizeOfLoadedContent, 
                                    hook, 
                                    1);

        // here 'insertBeforeMe' is LoadInst itself, 
        // since hook call and bitcast should be inserted BEFORE LI for a relacement.
        pushtoarglist (LI, 
                hook->getFunctionType()->getParamType(0), 
                LI->getOperand(0),     
                arglist,M);
        pushtoarglist (LI, 
                hook->getFunctionType()->getParamType(1), 
                numBytesOfLoadedContent, 
                arglist,M);

    }
#endif
    
    /// modifiedPtr == return val of hook == tag-stripped pointer.
    CallInst * modifiedPtr = CallInst::Create(hook, arglist, "");
    insertCastInstForArg (LI, arglist); 
    modifiedPtr->insertBefore(LI);
    
    /* replace operand of LI with modifiedPtr, 
    since operand of LI is tagged pointer. 
    If an in-bound pointer, load with tag-stripped pointer, 
    if else out-of-bound, error msgs and exit. */
    castAndreplaceUsesOfWithBeforeInst (LI, 
                                        LI->getOperand(0), 
                                        modifiedPtr);
}

Value* Framer::tagFramerTyID (Value * val, //val: alloca or gv
                              unsigned id, 
                              Module &M,
                              Instruction * valsUser) 
{
    uintptr_t tagvec = ((uintptr_t)(id+FRAMER_TyIDStart))<<48; 
    
    ConstantInt* idconst= // framerTyID_tag 
        ConstantInt::getSigned(Type::getInt64Ty(M.getContext()), tagvec); 
         
    Value* result= nullptr;
    if (Constant* constval= dyn_cast<Constant>(val)){
        Constant* or_tag= ConstantExpr::getOr(idconst, 
            ConstantExpr::getPtrToInt(constval, idconst->getType())); 
        Constant * taggedval= ConstantExpr::getIntToPtr(or_tag, val->getType()); //fix

        result= taggedval;
    }
    else {
        /// (1) convert val to type i64 (val is alloca/gv itself) 
        PtrToIntInst * valin64int = 
            new PtrToIntInst (val, idconst->getType(),"",valsUser);
        
        /// (2) OR (framerTyID_tag, ptrtoint)
        BinaryOperator* or_tag = 
            BinaryOperator::Create(Instruction::Or, 
                                   idconst, valin64int, 
                                   "referencedVar",
                                   valsUser);

        // (3) convert taggedptr back to ptr type. 
        IntToPtrInst * taggedval= 
            new IntToPtrInst (or_tag, val->getType(), "", valsUser);
        
        result= taggedval; 
    }
     
    return result;
}
/*bool Framer::isTaggedPointer (Value* ptrop)
{
    bool istagged=false;
    Value * p= ptrop->stripPointerCasts(); 
    if (CallInst* ci= dyn_cast<CallInst>(p)) {
        if (!isa<Function>(ci->getCaller())) {
            return false; 
        }
        Function * f= cast<Function>(ci->getCaller());
        if (f->getName().startswith("FRAMER_untag_ptr")) {
            exit(0); 
        }
        else if (isHookFamilyFunction(f)) {
            istagged=true; 
        }
        else if () {
            //do something for GV
        } 
        else {; errs()<<"\t- skip\n"; }
    }
    else {
    }
    return istagged;
}*/

void
Framer::doStoreInstForSpaceMiu (StoreInst * SI, 
                            Instruction * sucIns, 
                            DominatorTree & dt, 
                            AAResults & AA,
                            vector <AllocaInst*> & ais,
                            Module &M)
{
//  errs()<<"\n##  STORE  ##############\n";
  
  Function * hook= nullptr;
  vector<Value *> arglist;
  Value * op= SI->getPointerOperand();
  
  StructType * unionty= 
        isAliasWithUnionObj(op, 
                            AA, ais, GVUnions, HeapUnions, M); 

  // pointer operand is union-typed. 
  
  if (!unionty) {
 //     errs()<<"\t----> not union type. \n"; 
   //   assert(isSafelyCastedTo (unionty, 
   //                 cast<PointerType>(op->getType())->getElementType(), 
   //                 AllTypeList, SafeCasts)); 
      hook= M.getFunction ("FRAMER_untag_ptr_2");

      pushtoarglist(SI, 
              hook->getFunctionType()->getParamType(0), 
              SI->getPointerOperand(),     
              arglist,M);
  }
  else {
//      errs()<<"\t---> alias:: "<<*SI<<"\n";
//      errs()<<"\t---> update metadata.\n";
        
      hook= M.getFunction ("FRAMER_type_update_at_memWRITE");

      Type * ty= SI->getValueOperand()->getType(); 
         
      short tid= getIdx(AllTypeList, ty);
        
      assert(tid >=0); 

      Value * desttid= 
          constructValueFromFunc (tid, hook, 1);
        
      pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(0), 
                SI->getPointerOperand(), arglist,M);

      pushtoarglist (sucIns, 
                hook->getFunctionType()->getParamType(1), 
                desttid, arglist,M);
  } 

  CallInst * modifiedPtr = CallInst::Create(hook, arglist, "");

  insertCastInstForArg (SI, arglist); 
  modifiedPtr->insertBefore(SI);
  castAndreplaceUsesOfWithBeforeInst (SI, 
          SI->getPointerOperand(), 
          modifiedPtr);

}

void Framer::doStoreInst (StoreInst * SI, 
                          Instruction * successorInst, 
                          DominatorTree & dt, 
                          Module &M)
{
    tempstore++;
    Function * hook=nullptr;
    vector<Value *> arglist;
    
    Value* val = SI->getOperand(0);  
    Type * srcType = val->getType(); 
    unsigned srcFramerTyID= getFramerTypeID(srcType); 
    unsigned srcFramerTySize= Framer::getBitwidth(srcType)/8;
    assert (srcFramerTySize!=0 
            && "doStore. srcFramerTySize is zero\n");

#ifdef TYPECHECK    
    // Tagging referencing 
    if (isa<AllocaInst>(val) || isa<GlobalVariable>(val)) {
        assert(!(val->getType()->isArrayTy() 
            || val->getType()->isStructTy()) 
            && "Error! array/struct typed object should have been "
            "padded (so should be in constantexpr for gv," 
            "or in hook for alloca)!! check\n");
        
        Value* IDtagged= tagFramerTyID(val, srcFramerTyID, M, SI);  
        SI->setOperand(0, IDtagged); /// replace val with FramerTyID-tagged one.
    }
#endif

    /// if safe ptr operand (not involved in arith or cast), skip hooking. 
    if (isSafePtr(SI->getPointerOperand())) {
        dbg(errs()<<"skip. safe ptr. ptrop: "<<*SI->getPointerOperand()<<"\n";)
        safeptr++;
        return; 
    }

    unsigned issafeaccess= isSafeAccess(SI->getPointerOperand(), M, 1, paddedGVs);
    if (issafeaccess==SAFESTATICALLY) {
        tempstoresafe++;
        hook= M.getFunction ("FRAMER_untag_ptr_2");

        pushtoarglist(SI, 
                hook->getFunctionType()->getParamType(0), 
                SI->getPointerOperand(),     
                arglist,M);

    }
#ifndef DISABLE_CHEAP_CHECKS 
    else if(issafeaccess==COMPAREIDXATRUNTIME) {
        tempstoresafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_idx");
        assert(hook!=nullptr);
        insertCompareHookArgs(arglist, SI->getPointerOperand(), SI, hook, M);
    }
    else if (issafeaccess==COMPTYPEATRUNTIME) {
        tempstoresafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_type");
        assert(hook!=nullptr);
        insertCompareTypeHook(arglist, SI->getPointerOperand(), SI, hook, M); 
    }
#endif
    else if (issafeaccess==COMPSIZEATRUNTIME) {
        tempstoresafe++;
        hook= M.getFunction("FRAMER_supplementary_compare_size");
        assert(hook!=nullptr);
        insertCompareSizeHook(arglist, SI->getPointerOperand(), SI, hook, M); 
    }
    else if (issafeaccess==OUTOFBOUNDATRUNTIME) {
        insertExitCall(SI,M);
        return;
    } 
    else { 
        //errs()<<"store hooked!\n";
        hook= M.getFunction ("FRAMER_forall_store");

        Value * numBytesOfSrcTy = 
            constructValueFromFunc (srcFramerTySize, 
                    hook, 
                    1);

        assert (srcType == (cast<PointerType>(SI->getPointerOperand()->getType())->getElementType()) 
                && "Type mismatch between src and dest in store."); 


        pushtoarglist (SI, 
                hook->getFunctionType()->getParamType(0), 
                SI->getPointerOperand(),    
                arglist,M);
        pushtoarglist (SI, 
                hook->getFunctionType()->getParamType(1), 
                numBytesOfSrcTy, 
                arglist,M);

    //perlbench
/*    unsigned tempval=0;
    if (SI->getFunction()->getName().equals("S_study_chunk")) {
        tempval=1;  
    }
    Value *tempVAL=constructValueFromFunc(tempval, //GEPElemType->getTypeID(),   
                           hook, 
                           3);
    pushtoarglist (SI, 
                    hook->getFunctionType()->getParamType(3), 
                    tempVAL, 
                    arglist,M);
*/
   //perlbench
    }
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (SI, arglist);
    modifiedPtr->insertBefore (SI);
    castAndreplaceUsesOfWithBeforeInst(SI, 
        SI->getPointerOperand(), modifiedPtr);
}


void Framer::doGetElementPtrInst (GetElementPtrInst * GEP, 
                                        Instruction * successorInst, 
                                        Module &M)
{
    Function* hook= M.getFunction ("FRAMER_forall_getelementptr");

#ifdef TYPECHECK    
    unsigned srcFramerTyID= 
        getFramerTypeID(GEP->getSourceElementType()); 
    unsigned resultFramerTyID= 
        getFramerTypeID(GEP->getResultElementType()); 
    
    Value* srcFramerTyIDval= constructValueFromFunc(
                                    srcFramerTyID,   
                                    hook, 
                                    2);
    Value* resultFramerTyIDval= constructValueFromFunc(
                                    resultFramerTyID,   
                                    hook, 
                                    3);
#endif

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    GEP, 
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    GEP->getPointerOperand(), 
                    arglist,M);
#ifdef TYPECHECK
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(2), 
                    srcFramerTyIDval, 
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(3), 
                    resultFramerTyIDval, 
                    arglist,M);
#endif     
    
    CallInst * modifiedGEP = CallInst::Create(hook, arglist, "");
    insertCastInstForArg (successorInst, arglist);
    modifiedGEP->insertBefore(successorInst);
}


void Framer::doFPToSIInst (FPToSIInst * FTS, 
                                Instruction * successorInst, 
                                Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_fptosi");
    
    Type * SrcTy    = FTS->getSrcTy(); 
    Type * DestTy   = FTS->getDestTy();

    assert (SrcTy->isFloatingPointTy() && DestTy->isIntegerTy() && "The type of FPToSI is wrong!\n"); 

    Value * numBytesOfSrc     = 
        constructValueFromFunc(Framer::getBitwidth(SrcTy)/8, 
                                hook, 
                                0);
    Value * numBytesOfDest    = 
        constructValueFromFunc(Framer::getBitwidth(DestTy)/8, 
                                hook, 
                                1);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0), 
                    numBytesOfSrc, 
                    arglist,M);
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesOfDest, 
                    arglist,M);
    insertCastInstForArg (successorInst, arglist);
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doSIToFPInst   (SIToFPInst * SFI, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sitofp");
    
    Type * SrcTy    = SFI->getSrcTy(); 
    Type * DestTy   = SFI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isFloatingPointTy() && "The type of SIToFP is wrong!\n");

    Value * numBytesOfSrc     = constructValueFromFunc (Framer::getBitwidth(SrcTy)/8, hook, 0);
    Value * numBytesOfDest    = constructValueFromFunc (Framer::getBitwidth(DestTy)/8, hook, 1);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , numBytesOfSrc, arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfDest, arglist,M);
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doFPExt (FPExtInst * FEI, Instruction * successorInst, Module & M)
{
    Function * hook = M.getFunction ("FRAMER_forall_fpext");
    
    Type * SrcTy    = FEI->getSrcTy(); 
    Type * DestTy   = FEI->getDestTy();

    assert (SrcTy->isFloatingPointTy() && DestTy->isFloatingPointTy() && "The types of FPExt are wrong!\n");

    unsigned numBytesOfSrcTy = Framer::getBitwidth(SrcTy)/8;
    unsigned numBytesOfDestTy = Framer::getBitwidth(DestTy)/8;

    assert (numBytesOfSrcTy < numBytesOfDestTy && "SrcTy of FPExt must be smaller than the destination type.\n");

    Value * numBytesOfSrc     = constructValueFromFunc (numBytesOfSrcTy, hook, 0);
    Value * numBytesOfDest    = constructValueFromFunc (numBytesOfDestTy, hook, 1);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , numBytesOfSrc, arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , numBytesOfDest, arglist,M);
    
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);
 
}

void Framer::doPtrToIntInst (PtrToIntInst * PTI, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_ptrtoint (void * ptrToBeConvertedToInt, unsigned ptrSizeInBytes, unsigned numBytesOfDestType, uint64_t resultOfPtrToInt)

    Function * hook = M.getFunction ("FRAMER_forall_ptrtoint");
    
    Value * ptrToBeConvertedToInt   = PTI->getOperand(0);
    Value * ptrSizeInBytes          = constructValueFromFunc(dlayout->getPointerSize(), hook, 1);
    Value * numBytesOfDestType      = constructValueFromFunc((PTI->getType()->getIntegerBitWidth())/8, hook, 2);
    Value * resultOfPtrToInt        = PTI;

    assert (PTI->getOperand(0)->getType()->isPointerTy() && "PtrToInt's operand must be pointer typed.\n");
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0), ptrToBeConvertedToInt,  arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1), ptrSizeInBytes,         arglist,M); 
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2), numBytesOfDestType,     arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(3), resultOfPtrToInt,       arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doIntToPtrInst (IntToPtrInst * ITP, Instruction * successorInst, Module &M) 
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
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , intToBeConvertedToPtr, arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , ptrSizeInBytes,      arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , resultOfIntToPtr,      arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doAddrSpaceCastInst (AddrSpaceCastInst * I, Instruction * successorInst, Module & M)
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
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , ptrToBeCasted,     arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , addrSpaceOfSrcPtr, arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , addrSpaceOfDestPtr,arglist,M);
    
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);

}

/*
pushtoarglist does NOT insert castinst for arg. 
just creating a castinst, and then pushing to arglist.
*/
Instruction* 
Framer::createCastInst (Value * val, 
                    Type * Ty) //val (return):i8*->paramty
{ 
    Instruction * mycast= nullptr;

    if ((Ty->isPointerTy() && val->getType()->isPointerTy())
        || (Ty->isIntegerTy() && val->getType()->isVectorTy())) {

        mycast= new BitCastInst (val, Ty,"");
    }
    else if (isa<PtrToIntInst>(val) 
            || isa<TruncInst>(val) 
            || isa<FPToSIInst>(val)) {

        mycast= new ZExtInst (val, Ty, "");
    }
    else if (isa<SExtInst>(val)) {
        mycast= new SExtInst (val, Ty, "");
    }
    else if (Ty->isIntegerTy() && val->getType()->isIntegerTy()) {
        assert(Ty->getIntegerBitWidth() >= (val->getType())->getIntegerBitWidth()
                && "created val for hook's int bitwdith is bigger than hook's original type width!\n");
        mycast= new SExtInst (val, Ty, "");
    }
    else {
        errs()<<"createCastInst ERROR. val: "<<*val<<", Ty: "<<*Ty<<"\n";
        exit(0);
    }
    return mycast;
}

/*
void Framer::pushtoarglist (Instruction * insertBeforeMe,  
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
            if (paramTy->getIntegerBitWidth()!=Framer::getBitwidth(arg->getType())) {
                BitCastInst * mybitcastinst= new BitCastInst(arg, Type::getIntNTy(M.getContext(),Framer::getBitwidth(arg->getType())), "", insertBeforeMe);
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
*/


void Framer::doTruncInst (TruncInst * TR, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_trunc");
    Type * SrcTy    = TR->getSrcTy(); 
    Type * DestTy   = TR->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (Framer::getBitwidth(SrcTy) > Framer::getBitwidth(DestTy))
            && "TruncInst:: Both Src and Dest should be Int typed! and #SrcTyBytes > #DestTyBytes\n");
    //TODO: op(0)'s bitwidth should be larger than trunc's bitwidth.
    
    Value * numBytesOfSrcTy= constructValueFromFunc(Framer::getBitwidth(SrcTy)/8,hook,1); 
    Value * numBytesOfDestTy=constructValueFromFunc(Framer::getBitwidth(DestTy)/8,hook,2);
    
    vector<Value *> arglist;

    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(0),TR,              arglist, M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(1),numBytesOfSrcTy, arglist, M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(2),numBytesOfDestTy,arglist, M);
   
    insertCastInstForArg (successorInst, arglist); 
    insertFunctionCall (hook, successorInst, arglist);
}


void Framer::doSExtInst (SExtInst * SI, Instruction * successorInst,  Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sext");
    Type * SrcTy    = SI->getSrcTy(); 
    Type * DestTy   = SI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (Framer::getBitwidth(SrcTy) < Framer::getBitwidth(DestTy))
            && "SextInst:: Both Src and Dest should be Int typed! and #SrcTyBytes < #DestTyBytes\n");
    
    Value * numBytesOfSrcTy    = constructValueFromFunc (Framer::getBitwidth(SrcTy)/8, hook, 1); 
    Value * numBytesOfDestTy   = constructValueFromFunc (Framer::getBitwidth(DestTy)/8, hook, 2);
    
    vector<Value *> arglist;

    pushtoarglist(successorInst, hook->getFunctionType()->getParamType(0), SI,               arglist, M);
    pushtoarglist(successorInst, hook->getFunctionType()->getParamType(1), numBytesOfSrcTy,  arglist, M);
    pushtoarglist(successorInst, hook->getFunctionType()->getParamType(2), numBytesOfDestTy, arglist, M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doZExtInst (ZExtInst * ZI, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_zext");
    Type * SrcTy    = ZI->getSrcTy(); 
    Type * DestTy   = ZI->getDestTy();

    assert (SrcTy->isIntegerTy() && DestTy->isIntegerTy() && (Framer::getBitwidth(SrcTy) < Framer::getBitwidth(DestTy))
            && "ZextInst:: Both Src and Dest should be Int typed! and #SrcTyBytes < #DestTyBytes\n");
    //TODO: op(0)'s bitwidth should be larger than trunc's bitwidth.
    
    Value * numBytesOfSrcTy    = constructValueFromFunc (Framer::getBitwidth(SrcTy)/8, hook, 1); 
    Value * numBytesOfDestTy   = constructValueFromFunc (Framer::getBitwidth(DestTy)/8, hook, 2);
    
    vector<Value *> arglist;

    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(0),ZI,              arglist, M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(1),numBytesOfSrcTy, arglist, M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(2),numBytesOfDestTy,arglist, M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}
/*
void Framer::doOverflowBinaryOp (OverflowingBinaryOperator * OFO, Instruction * successorInst, Module & M)
{
        
    switch (OFO->getOpcode()) {
        case Instruction::Add :
            {
                //if (!HookDefinitionExists.count(Instruction::Add)) {
              
                AddOperator * AO = dyn_cast<AddOperator>(OFO);
                doAddOp (AO, successorInst, M); 
                break;
            }
        case Instruction::Sub :
            {
                //if (!HookDefinitionExists.count(Instruction::Sub)) {
                if (!HookDefinitionExists[Instruction::Sub]) {
                    dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                    break;
                }

                SubOperator * SO = dyn_cast<SubOperator>(OFO);
                doSubOp (SO, successorInst, M);
                break;
            }
        case Instruction::Mul :
            {
                if (!HookDefinitionExists[Instruction::Mul]) {
                    dbg(errs()<<"No hooks provided for this inst. Skipping..\n";) 
                    break;
                }

                MulOperator * MO = dyn_cast<MulOperator>(OFO);
                doMulOp (MO, successorInst, M);
                break;
            }
    }
}
*/


void Framer::doBinaryOp (BinaryOperator * OFO, Instruction * successorInst, Module & M)
{
    doAddOp (OFO, successorInst, M);
}

void Framer::doPossiblyExactOp  (PossiblyExactOperator * PEO, Instruction * successorInst, Module & M)
{
    switch (PEO->getOpcode()) {
        case Instruction::SDiv :
            {
                if (!HookDefinitionExists[Instruction::SDiv]) {
                    dbg(errs()<<"No hooks provided for SDiv inst. Skipping..\n";)
                    break;
                }

                SDivOperator * SDO = dyn_cast<SDivOperator>(PEO);
                doSDivOp (SDO, successorInst, M); 
                break;
            }
        case Instruction::UDiv :
            {
                if (!HookDefinitionExists[Instruction::UDiv]) {
                    dbg(errs()<<"No hooks provided for UDiv inst. Skipping..\n";)
                    break;
                } 

                UDivOperator * UDO = dyn_cast<UDivOperator>(PEO);
                doUDivOp (UDO, successorInst, M);
                break;
            }
        case Instruction::LShr :
            {
                if (!HookDefinitionExists[Instruction::LShr]) {
                    dbg(errs()<<"No hooks provided for LShr inst. Skipping..\n";)
                    break;
                } 

                LShrOperator * LSR = dyn_cast<LShrOperator>(PEO);
                doLShrOp (LSR, successorInst, M);
                break;
            }
        case Instruction::AShr :
            {
                if (!HookDefinitionExists[Instruction::AShr]) {
                    dbg(errs()<<"No hooks provided for AShr inst. Skipping..\n";)
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



void Framer::doSubOp (SubOperator * SO, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_subop (int64_t operand_0, int64_t operand_1, int64_t numBytesOfIntType)
    Function * hook = M.getFunction ("FRAMER_forall_subop");
    
    Type * OpTy = SO->getType();
    
    assert ((SO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Two operands of Sub operator should be the same typed and integertyped!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
   
    Value * numBytesOfIntType= constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);

    vector<Value *> arglist;
    
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(0),SO->getOperand(0),arglist,M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(1),SO->getOperand(1),arglist,M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(2),numBytesOfIntType,arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
     
}

void Framer::doMulOp (MulOperator * MO, Instruction * successorInst,  Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_mulop");
    
    Type * OpTy = MO->getType();
    
    assert ((MO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of Mul operator should be the same typed, int typed!\n");

    Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    
    vector<Value *> arglist;
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , MO->getOperand(0), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , MO->getOperand(1), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

//void Framer::doAddOp (AddOperator * AO, Instruction * successorInst, Module &M)
void Framer::doAddOp (BinaryOperator * OFO, Instruction * successorInst, Module &M)
{
    // perlbench
    if (Framer::getBitwidth(OFO->getType())>64) {
        return; 
    }
    //perlbench

    Function * hook = M.getFunction ("FRAMER_forall_addop");
    
   // Type * OpTy = OFO->getType();
    
   // assert ((OFO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
   //         && "Both of operands of ADD operator should be the same typed, int typed!\n");
    
    //Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    vector<Value *> arglist;
   /*void Framer::pushtoarglist(Instruction * insertBeforeMe,  
                                Type * paramTy,
                                Value * arg, 
                                vector<Value*> & arglist) */ 
  
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(0),OFO->getOperand(0),arglist,M);
    pushtoarglist(successorInst,hook->getFunctionType()->getParamType(1),OFO->getOperand(1),arglist,M);
   // pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist);
   
    //insertCastInstForArg (successorInst, arglist);
    //insertFunctionCall (hook, successorInst, arglist);
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (successorInst, arglist);
    modifiedPtr->insertBefore (successorInst);

/* CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (SI, arglist);
    modifiedPtr->insertBefore (SI);
    castAndreplaceUsesOfWithBeforeInst(SI, destAddress, modifiedPtr);
*/
}

void Framer::doSDivOp (SDivOperator * SDO, Instruction * successorInst, Module & M)
{
    Function * hook = M.getFunction ("FRAMER_forall_sdiv");
    
    Type * OpTy = SDO->getType();
    
    assert ((SDO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of SDiv operator should be the same typed, int typed!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
   
    Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);

    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , SDO->getOperand(0), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , SDO->getOperand(1), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);

}

void Framer::doUDivOp (UDivOperator * UDO, Instruction * successorInst, Module &M)
{
    //void FRAMER_forall_uDivop (int64_t operand_0, int64_t operand_1, int64_t numBytesOfIntType)

    Function * hook = M.getFunction ("FRAMER_forall_udiv");
    
    Type * OpTy = UDO->getType();
    
    assert ((UDO->getOperand(0)->getType() == OpTy) && (OpTy->isIntegerTy())
            && "Both of operands of UDiv operator should be the same typed, int typed!\n");
   
   //TODO: if it is NUW or NSW..?? wtf is that?
    Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , UDO->getOperand(0), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , UDO->getOperand(1), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
}

void Framer::doLShrOp (LShrOperator * UDO, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_lshr");
    
    Type * OpTy = UDO->getType();
   
    Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , UDO->getOperand(0), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , UDO->getOperand(1), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
}

void Framer::doAShrOp (AShrOperator * OP, Instruction * successorInst, Module &M)
{
    Function * hook = M.getFunction ("FRAMER_forall_ashr");
    
    Type * OpTy = OP->getType();
    
    assert ((OP->getOperand(0)->getType()->isIntegerTy()) && (OP->getOperand(1)->getType()->isIntegerTy())
            && "Both of operands of AShr operator should be int typed!\n");
   
    Value * numBytesOfIntType = constructValueFromFunc (Framer::getBitwidth(OpTy)/8, hook, 2);
    
    vector<Value *> arglist;
    
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(0) , OP->getOperand(0), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(1) , OP->getOperand(1), arglist,M);
    pushtoarglist (successorInst, hook->getFunctionType()->getParamType(2) , numBytesOfIntType, arglist,M);
   
    insertCastInstForArg (successorInst, arglist);
     
    insertFunctionCall (hook, successorInst, arglist);
 
}

void Framer::insertFunctionCall(Function * F, 
                                Instruction * insertBeforeMe, 
                                vector<Value*> & arglist) 
{
    CallInst * CI = CallInst::Create (F, arglist, "");
    CI->insertBefore (insertBeforeMe);
}

CallInst * Framer::insertHookAndReturn(Function * F, 
                                            Instruction * insertBeforeMe, 
                                            vector<Value*> & arglist) 
{
    CallInst * CI = CallInst::Create (F, arglist, "");
    CI->insertBefore (insertBeforeMe);
    return CI;
}

/* not used
Value * Framer::getEndAddrforMalloc (Value * baseAddr, Value * numBytes, Type * typeToConvertTo, Instruction * insertBeforeMe, Module & M)
{
    IntegerType * my64IntTy = Type::getInt64Ty (M.getContext());

    PtrToIntInst * baseAddrInInt = new PtrToIntInst (baseAddr, my64IntTy, "", insertBeforeMe);
    Instruction * addTotalByteNumToBaseAddr = 
                               BinaryOperator::Create (Instruction::Add, baseAddrInInt, numBytes, "", insertBeforeMe);
    IntToPtrInst * endAddress = new IntToPtrInst (addTotalByteNumToBaseAddr, typeToConvertTo, "", insertBeforeMe); 
     
    return endAddress;
     
}
Type* Framer::getResultTypeOfMalloc (CallInst * CI)
{
    //if CI is operand(0) of bitcast following the CI, and then stored to a pointertype.
    Function* calledF= CI->getCalledFunction();
    Type* malloctype = calledF->getReturnType(); 
     
    for (Value::use_iterator it = CI->use_begin(), ie = CI->use_end(); it!=ie ; ++it) {
        if (BitCastInst* user = dyn_cast<BitCastInst>((&*it)->getUser()) ) {
            for (Value::use_iterator iit = user->use_begin(), iie = user->use_end(); iit!=iie ; ++iit) {
                if (isa<StoreInst>((&*iit)->getUser())) {
                    malloctype= user->getDestTy();
                }
                else {
                }
            }
        }
        else {
        }
    }
    return malloctype;
}
*/




static Type *
getEffectiveTyOfHeap (Instruction * ins,
                      DominatorTree & dt)
{
  // initialise bci to find a bitcast deciding an effective type.

  Instruction * bci= nullptr;
  
  // find the dominating bci
  for (Value::user_iterator it= ins->user_begin(); it!= ins->user_end(); it++){
  
    BitCastInst * temp= dyn_cast<BitCastInst>(*it); 
    
    if (!temp) continue;
    
    // now a user is a bitcast. 
    
    if (!bci) {
        bci= temp; 
        continue;
    }
    // now we have a bci. 

    if (dt.dominates(temp, bci)) {
      bci= temp;
    }
  }
  
  ///
  // < alternative way to detect an effective type > 
  // If llvm-clang optimises Ty * p= malloc (sizeof(Ty)); 
  // the way above fails at detecting an effective type.
  // then do more heuristic to detect. 
  // ex) add_to_entry_list in dfa.c, 445.gobmk
  // 
  if (!bci) {
    
    StoreInst * sins= nullptr;
     
    for (Value::user_iterator it= ins->user_begin(); it!= ins->user_end(); it++){

      StoreInst * temp= dyn_cast<StoreInst>(*it); 

      if (!temp) continue;

      // now a user is a store. 
      
      if (temp->getOperand(0)!= ins) continue;
      
      // now a store user's op(0) is call malloc.

      if (!sins) {
        sins= temp; 
        continue;
      }
      // now we have a non-null sins. 

      if (dt.dominates(temp, sins)) {
        sins= temp;
      }
    }
    
    if (!sins) return nullptr; 
    
    // now store candidate. get its op. we assume op(0) is i8** type. 
    
    Type * opelemty= cast<PointerType>(sins->getOperand(1)->stripPointerCasts()->getType())->getElementType(); //store's ptr op must be a pointer.
   
    //errs()<<"\talternative - sin: "<<*sins<<"\n\t  op: "<<*sins->getOperand(1)<<"\n\t  opty: "<<*opelemty<<"\n"; 
  
    PointerType * elemty= dyn_cast<PointerType>(opelemty);
    
    if (!elemty) return nullptr;
    
    return elemty->getElementType();  
  
  }
  ///
  // Despite two tries, fail to get a bci deciding an effecitve type
  ///

  if (!bci) return nullptr;
  
  
  PointerType * destTy= dyn_cast<PointerType>(bci->getType());
  assert(destTy);

  //errs()<<"  involved BCI:"<<*bci<<", elemty: "<<*destTy->getElementType()<<"\n";

  return destTy->getElementType();
}



static bool
isCastWeDoNOTHandle (CastInst * ci,
                     DominatorTree & dt)
{
  /* (1) we do not handle bitcast to vector. */
  if (ci->getDestTy()->isVectorTy()) {
    return true; 
  }
  
  PointerType * sptr= dyn_cast<PointerType>(ci->getSrcTy());
  PointerType * dptr= dyn_cast<PointerType>(ci->getDestTy());
  
  if (!sptr || !dptr) {
    return true;  
  }
  if (sptr->getElementType()->isVectorTy()) {
    errs()<<"sptr vector. bci's op: "<<*ci->getOperand(0)<<"\n";    
  }
  if (dptr->getElementType()->isVectorTy()) {
    return true;
  }
  // op(0) is callinst and calledfunction is FRAMER.
  // we use the bci as an effective type-decision maker, so skip hooking for check.
  if (isa<CallInst>((ci->getOperand(0)))) { 
   
    CallInst * callins= cast<CallInst>(ci->getOperand(0));

    Function * fn= dyn_cast<CallInst>(callins)->getCalledFunction();
    
    if (!fn) return false;
     
    if (!fn->getName().startswith("FRAMER_forall_malloc") &&
        !fn->getName().startswith("FRAMER_forall_realloc") &&
        !fn->getName().startswith("malloc") &&
        !fn->getName().startswith("realloc") &&
        !isCustomWrapper(fn)) {
       
        if (fn->getName().startswith("FRAMER_")) {
            errs()<<"\tbci's callinst op is : "<<*callins<<"\n"; 
        }
        return false;
    }
    // now call to malloc wrappers (ours or custom-) 
     
    // checking if this bci(arg) is the dominating bci (i.e. type maker) for the callinst 
    for (Value::user_iterator it= callins->user_begin(); it!= callins->user_end(); it++){
  
      BitCastInst * temp= dyn_cast<BitCastInst>(*it); 
    
      if (!temp) continue;
    
      // now a user is a bitcast. 
    
      if (dt.dominates(temp, ci)) {
        return false;
      }
    }
    
    return true; 
  }
////////////////
      ///
    // Currently malloc is interposed by framer pass. (See doCallInstMalloc)
    // if bitcast operand is malloc call, no need to check type cast.
    ///
   /* if (CallInst * ci= dyn_cast<CallInst>(BCI->getOperand(0))) {
        Function * fnc= ci->getCalledFunction();
        if (fnc) {
            if (fnc->getName().equals("FRAMER_forall_malloc")) {
                errs()<<"Skip checking: "<<*BCI<<"\n";
                errs()<<"  op: "<<*BCI->getOperand(0)<<"\n";

                return; 
            }
        }
    }
*/
///// pasted from dobitcast
  return false;
}


///
// If we find a heap obj's effective type of our interest, 
// this returns its type. (types of our interest: struct) 
// else if call malloc (ci) is inside a malloc wrapper, returns void.
// otherwise, return null.
///
static Type * 
getHeapObjTyID (CallInst * ci, 
                DominatorTree & dt,
                Module & M)
{

#ifndef ENABLE_TRACK_ARRAYS        

  ConstantInt * objsize= getObjSizeFromCallInst(ci); 
   
  if (!objsize){ 

      // we treat malloc(sizeof()*n), where n is a var, 
      // or other forms (N + x?) as an array 
      // This way we'll miss malloc(sizeof(T)*1), which is not an array.   
      return nullptr;
  }

#endif // end of ENABLE_TRACK_ARRAYS

  ///
  // (case 1) The most desirable form : StructTy * ptr= malloc(N); 
  ///
  Type * destTy= getEffectiveTyOfHeap(ci, dt); 
  
  if (!destTy) {
      return nullptr;
  }
  // now desty is not null.

#ifdef TRACK_STRUCT_ALSO  
  
  // we handle only struct type. (TODO: class type later)
  if (!isa<StructType>(destTy)) {
    return nullptr;
  }

#endif
     
  /*  likely checking with non-aggregates would be cheaper
      than skipping (causing branches) checking them at runtime. */
    
#ifndef ENABLE_TRACK_ARRAYS        

  // now objsize is a constantint.

  uint64_t objsizec= objsize->getZExtValue();
  uint64_t dsize= M.getDataLayout().getTypeSizeInBits(destTy)/8;
   
    
  if (objsizec % dsize != 0) {
        ///
        // e.g. heap objects with a header/footer such as 
        // Ptrdist/bc (bc_struct*)malloc(sizeof(bc_struct)+length+scale)
        // spaceMiu doesn't handle this at the moment.
        ///
        return nullptr;
  }

  if (dsize==objsizec) {  // if it's a non-array
    return destTy;  
  }

#endif

  return nullptr;
}

/*
static CallInst *
getCallSiteOfExternalCaller (CallGraphNode * nd, //exter's caller. init 
                             Function * wrp, //xmalloc 
                             Module & M)
{
  Function * func= nd->getFunction(); //
  errs()<<"external's caller: "<<func->getName()<<"\n";
      
  for (Function::iterator fi=func->begin(); fi!=func->end(); fi++) {
    
    for (BasicBlock::iterator it= fi->begin(); it!=fi->end(); it++) {
         
      CallInst * ci= dyn_cast<CallInst>(&*it); 
      
      if (!ci) continue;
      
      // got ci.
      // now check if one of args is wrp. 
       
      for (int i=0; i< ci->getNumArgOperands (); i++) {
        
        Function * fp= dyn_cast<Function>(ci->getArgOperand(i));
        
        if (!fp) continue; 
        errs()<<"got func arg: "<<fp->getName()<<"\n";  
        
        // seems this is a problem.
        if (fp == wrp) return ci; 
      
      }
    }
  }
  
  return nullptr;
}

static void
replaceNewMallocWrapper (CallGraphNode * Wrapcaller, //external (obstack) 
                            // custom wrapper(xmalloc)'s external caller. 
                         Function * wrp, // xmalloc 
                         CallGraph & CG, 
                         Module & M)
{
  // 1. get caller's caller (obstack)
  // 2. then get the callinst calling xmalloc in AA
  errs()<<"replaceNewMallocWrapper starts..\n"; 
  
  for (CallGraph::iterator it=CG.begin(); it!=CG.end(); it++) {
    
    CallGraphNode * nd= &*((*it).second);

    for (CallGraphNode::iterator ni= nd->begin(); ni != nd->end(); ni++) {
    
      //if ((*ni).second != Wrapcaller) continue; 
      if ( ((*ni).second)->getFunction()) {
          
      }
      if ( (*ni).second != CG.getExternalCallingNode()) continue; 
      
      errs()<<"got it\n"; 
      // now we got a caller of external caller.
      CallInst * ci= getCallSiteOfExternalCaller(nd, wrp, M);
      
      assert(ci);   
      
      errs()<<"xmalloc caller?:"<<*ci<<"\n"; 
      
      ci->setArgOperand(3, M.getFunction("FRAMER_xmalloc")); 
      ci->setArgOperand(4, M.getFunction("FRAMER_xfree")); 
      
      errs()<<"changed: "<<*ci<<"\n";
      exit(0);
    }
  }
  
}
*/

// TODO: function pointer
void
Framer::hookWrapperCallSite (Function * caller, // wrapper's caller
                     Function * wrapper,
                     DominatorTree & DT,
                     Module & M)
{
  //errs()<<"\nwrapper's caller: "<<caller->getName()<<"\n";
  
  for (Function::iterator fi= caller->begin(); fi!=caller->end(); fi++) {
    
    Instruction * bckupnext = &*fi->begin(); 
    
    for (BasicBlock::iterator it= fi->begin(); it!=fi->end(); it++) {    
      
      if (&*it != &*bckupnext) continue;
      
      bckupnext = getNextInst(&*it);
       
      if (!isa<CallInst>(&*it)) continue;

      CallInst * ci= cast<CallInst>(&*it);

      Function * calledfunc= ci->getCalledFunction(); 

      if (!calledfunc) continue;
      
      if (!calledfunc->getName().startswith(wrapper->getName())) continue;
      
      // now got a callsite to the wrapper.
     
      errs()<<"  callinst: "<<*ci<<" // in "<<ci->getFunction()->getName()<<"\n"; 
      
      Type * effectiveTy= getHeapObjTyID(ci, DT, M);
     
      if (!effectiveTy) { // cant find an effective type in the function
        // then skip. At allocation, we already update type info with void 
        // effectiveTy= Type::getVoidTy(M.getContext());
        
        return;
      }
        
      unsigned tid= getFramerTypeID(effectiveTy);
      errs()<<"  -> update ty: "<<*effectiveTy<<" // tid:"<<tid<<" in "<<caller->getName()<<"\n"; 
     
      // Can I just access the header directly?
       
      // TODO: skip arrays
       
      Function * hook= M.getFunction("FRAMER_lazy_type_update");
      Instruction * successorInst= getNextInst(ci); 
      
      vector <Value*> arglist;
    
      pushtoarglist (successorInst, 
                     hook->getFunctionType()->getParamType(0), 
                     ci, 
                     arglist, M);
      pushtoarglist (successorInst, 
                     hook->getFunctionType()->getParamType(1), 
                     constructValueFromFunc (tid, hook, 1),
                     arglist, M);
    
      CallInst * newCI= CallInst::Create (hook, arglist, "FRAMER_lazy_type");
      insertCastInstForArg (successorInst, arglist);
      newCI->insertAfter(successorInst);
      
    }
  }
}

/// 
// Encountering a malloc family wrapper, spaceMiu finds a wrapper's callers,
// finds an effective type in the caller and inserts a hook 
// updating an effecitve type in the header at each callsite to a wrapper.
///
void 
Framer::doLazyTypeUpdate (Function * wrp,
                          CallGraph & CG,
                          DominatorTree & DT,
                          Module & M)
{
  CallGraphNode * wrapper= CG.operator[](wrp); // a malloc wrapper.     
  set <CallGraphNode*> Visited;
  
  // traverse all nodes to find callers of wrapper;
  for (CallGraph::iterator it=CG.begin(); it!=CG.end(); it++) {
    
    CallGraphNode * nd= &*((*it).second); // AA
      
    // for each node's callee
    
    for (CallGraphNode::iterator ni= nd->begin(); ni != nd->end(); ni++) {
    
      if ((*ni).second != wrapper) continue; 
      
      if (Visited.count(nd)) continue; 
        
      if (CG.getExternalCallingNode()==nd) { // here or outside for loop?
        // READ: 
        // disabled the following since llvm CG cannot get a caller
        // of a external function.
        // (internal func node --call--> external func node).
        // So, replacing its func arg (xmalloc) with framer_xmalloc 
        // is done at doCallInst.
        // replaceNewMallocWrapper(nd, wrp, CG, M);
    
        continue;
      }
      // nd is AA, ni is wrapper 
      // now insert a hook at a callsite to   
           
      hookWrapperCallSite(nd->getFunction(), wrp, DT, M); 
       
      Visited.insert(nd);
                       
    }
  }
}
/*  ALERT!!!!!   
Some BUG (not resolved yet) in doCallInstMalloc:
hooking Perl_safesysmalloc in perlbench causes segmentation fault.
(when hooking perl_sysmalloc is skipped, no seg fault.)
It seems miu's malloc/realloc wrapper causes seg fault 
when taking select instruction as an argument (size argument).
TODO: FIX IT LATER
*/  
Instruction *    
Framer::doCallInstMalloc (CallInst * CI, 
                          Instruction * successorInst, 
                          AAResults & AA,
                          DominatorTree & DT,                          
                          CallGraph & CG,
                          Module & M)
{
#ifdef DISABLE_HOOK_MALLOC_FAMILY_STATICALLY

    return nullptr;

#endif

    errs()<<"\n@@@@@@@@@\n"<<*CI<<" in "<<CI->getFunction()->getName()<<"\n";


    unsigned FramerTyID= AllTypeList.size(); // don't care type id. 
    bool isunion= false;
    
    /// 
    // If it's called in a malloc wrapper, return void type. 
    // (i.e. this ci is inside a malloc wrapper)
    ///

    
    if (isCustomWrapper(CI->getFunction())) {
            
        // if heap obj's effective type is determined void by getHeapObjTyID,
        // we hook a call site to malloc's wrapper, 
        errs()<<"  -> malloc inside wrapper: "<<CI->getFunction()->getName()<<"\n";
         
    #ifndef INLINE_CUSTOM_MALLOC_WRAPPER
        doLazyTypeUpdate(CI->getFunction(), CG, DT, M);
    #else
        
        return nullptr;

    #endif        
   
    }
    else {

        Type * destty= getHeapObjTyID(CI, DT, M);
        ///
        // if cannot get an effective type statically, do NOT track this obj.
        ///
        if (!destty) return nullptr;
       
        FramerTyID= getFramerTypeID (destty); 
       
        // now checking if it's an union.
        isunion= isUnionTy(destty);
        
        // TODO: return regarding BCI and extract destty from it?
        // then we can utilise bci to skip hooking? 

    }
    
    /// 
    /// now tracking this obj.
    /// 

    errs()<<"  Tid: "<<FramerTyID<<"\n";

    Function * wrapper = M.getFunction("FRAMER_forall_malloc");
   
    Value * typeinstance= 
        constructValueFromFunc (FramerTyID, wrapper, 1);
    Value * unioninstance= 
        constructValueFromFunc (isunion, wrapper, 2);
    
    // now, immediate bitcast successorins should be skipped. 
    // it is done at dobitcast.    
    
    vector <Value*> arglist;
    
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(0), 
                   CI->getArgOperand(0), 
                   arglist,M);
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(1), 
                   typeinstance, 
                   arglist,M);
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(2), 
                   unioninstance, 
                   arglist,M);
    
    CallInst * newCI = CallInst::Create (wrapper, arglist, "malloc_wrapper");
     
    Instruction * typeRestoringPtrForReplacedUse = 
        castAndreplaceAllUsesWith (CI, newCI); 
    
   // insertCastInstForArg (successorInst, arglist);
    newCI->insertBefore (CI); //then hook callinst inserted.
    
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter(newCI);
    }
    
    errs()<<"Mal Hook: "<<*newCI<<" // in "<<newCI->getFunction()->getName()<<"\n";

    return CI;
}

Instruction *    
Framer::doCallInstRealloc (CallInst * CI, 
                          Instruction * successorInst, 
                          AAResults & AA,
                          DominatorTree & DT,                          
                          CallGraph & CG,
                          Module & M)
{
#ifdef DISABLE_HOOK_MALLOC_FAMILY_STATICALLY

    return nullptr;

#endif

    errs()<<"@@@@@@@@@\n"<<*CI<<" in "<<CI->getFunction()->getName()<<"\n";

    unsigned FramerTyID= AllTypeList.size(); // don't care type. 
    bool isunion= false;;
    
    /// 
    // If it's called in a malloc wrapper, return void type. 
    // (i.e. this ci is inside a malloc wrapper)
    ///
    
    
    if (isCustomWrapper(CI->getFunction())) {
        
        errs()<<"  -> REalloc inside wrapper: "<<CI->getFunction()->getName()<<"\n";
      
        //errs()<<"\n(case 1) wrapper: "<<CI->getFunction()->getName()<<"\n";
        //destty= Type::getVoidTy (M.getContext());
        
        // if heap obj's effective type is determined void by getHeapObjTyID,
        // we hook a call site to malloc's wrapper, 
  
    #ifndef INLINE_CUSTOM_MALLOC_WRAPPER
        
        doLazyTypeUpdate(CI->getFunction(), CG, DT, M);
   
    //#else 

     //   return nullptr; 
    
    #endif
 
    }
    else {
  
         
        Type * destty= getHeapObjTyID(CI, DT, M);
        
        ///
        // We can NOT skip hooking realloc, even if fail to get an effective type,
        // since malloced obj may have been tagged. If skip it here, seg fault.
        ///  
        if (destty) {
            FramerTyID= getFramerTypeID (destty);
            // now checking if it's an union.
            isunion= isUnionTy(destty);
        }
  
    }
  
    
    /// 
    /// now tracking this obj.
    /// 
    
    errs()<<"  Tid: "<<FramerTyID<<"\n";
     
    Function * wrapper = M.getFunction("FRAMER_forall_realloc");
   
    
    // now, immediate bitcast successorins should be skipped. 
    // it is done at doBitCast, not here.    
    
    vector <Value*> arglist;
    
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(0), 
                   CI->getArgOperand(0), 
                   arglist,M);
    
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(1), 
                   CI->getArgOperand(1), 
                   arglist,M);
    
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(2), 
                   constructValueFromFunc (FramerTyID, wrapper, 2), 
                   arglist,M);
    
    pushtoarglist (successorInst, 
                   wrapper->getFunctionType()->getParamType(3), 
                   constructValueFromFunc (isunion, wrapper, 3), 
                   arglist,M);
    
    pushtoarglist (successorInst, 
            wrapper->getFunctionType()->getParamType(4), 
            constructValueFromFunc(AllTypeList.size(), wrapper, 4), 
            arglist,M); 
    
    CallInst * newCI= CallInst::Create (wrapper, arglist, "realloc_wrapper");
     
    Instruction * typeRestoringPtrForReplacedUse = 
        castAndreplaceAllUsesWith (CI, newCI); 
    
   // insertCastInstForArg (successorInst, arglist);
    newCI->insertBefore (CI); //then hook callinst inserted.
    
    if (typeRestoringPtrForReplacedUse != nullptr) {
        typeRestoringPtrForReplacedUse->insertAfter(newCI);
    }

    errs()<<"Real Hook: "<<*newCI<<" // in "<<newCI->getFunction()->getName()<<"\n";
    
    return CI;
}


Instruction* Framer::doCallInstFree(CallInst * CI, 
                                        Instruction * successorInst, 
                                        Module & M)
{
    Function * hook = M.getFunction("FRAMER_forall_call_free");
    
    vector <Value*> arglist;
    pushtoarglist (successorInst, 
                    hook->getFunctionType()->getParamType(0),
                    CI->getArgOperand(0), 
                    arglist,M);
   
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

void 
Framer::doCallLLVMMemTransfer (CallInst * CI,
                                Instruction * sucIns, 
                                AAResults & AA,
                              #ifdef ENABLE_SPACEMIU
                                vector <AllocaInst*> & ais,
                              #endif
                                Module &M)
{
  // (Src, Dest, numBytesToCopy, alignment, isVolatile )    
  
  dbg(errs()<<"MEM Trasnfer\n";) 
    
  Function * hook= nullptr;
    
  Value * destAddress= nullptr;
  Value * srcAddress= nullptr;
  Value * numBytesToCopy= nullptr;
  Value * numAlign= nullptr;
  Value * isVolatile= nullptr; 

  if (MemTransferInst * MI = dyn_cast<MemTransferInst>(CI)){
    destAddress     = MI->getRawDest();
    srcAddress      = MI->getRawSource();
    numBytesToCopy  = MI->getLength();
    //numAlign        = MI->getAlignmentCst();
    numAlign        = constructValueFromFunc(MI->getSourceAlignment(), hook, 2); //source alignment
    isVolatile      = MI->getVolatileCst(); 
  }
  else {
    errs()<<"Memtransfer. it ever enters here?\n";
    exit(0);

    destAddress=    CI->getArgOperand(0); 
    srcAddress=     CI->getArgOperand(1);  
    numBytesToCopy= CI->getArgOperand(2); 
    numAlign=       CI->getArgOperand(3);  
    isVolatile=     CI->getArgOperand(4); 
  }

  vector<Value *> dest_arglist;
  vector<Value *> src_arglist;
     
#ifdef ENABLE_SPACEMIU
  
    hook= M.getFunction ("FRAMER_type_update_at_memWRITE");
   
    Function * hook_untag= M.getFunction("FRAMER_untag_ptr_2");
     
    if(!isAliasWithUnionObj(destAddress, AA, ais, GVUnions, HeapUnions, M)) {
     
      // handle dest
       
      pushtoarglist(CI, 
                hook_untag->getFunctionType()->getParamType(0), 
                destAddress,     
                dest_arglist,
                M);
      
      // handle src

      pushtoarglist(CI, 
                hook_untag->getFunctionType()->getParamType(0), 
                srcAddress,     
                src_arglist,
                M);

    // handle dest ptr

    CallInst* destModifiedPtr= CallInst::Create (hook_untag, dest_arglist, "");
    insertCastInstForArg (CI, dest_arglist);
    destModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            destAddress, 
            destModifiedPtr);

    // handle src ptr
    
    CallInst* srcModifiedPtr= CallInst::Create (hook_untag, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            srcAddress, 
            srcModifiedPtr);

    }
    else {
     // errs()<<"## memtransfer has alias:: "<<*CI<<"\n";
        
      hook= M.getFunction ("FRAMER_type_update_at_memWRITE");

    ////
    
      Type * origty= destAddress->getType(); 
    
      if (isa<BitCastOperator>(destAddress)) {
        origty= cast<BitCastOperator>(destAddress)->getSrcTy();
      }
      else if (isa<GEPOperator>(destAddress)) {
        origty= cast<GEPOperator>(destAddress)->getPointerOperand()->getType();  
      }
      else {
        errs()<<"Memtransfer another ty: "<<*destAddress<<".. Exiting..\n";
        exit(0);
      }
    ////

      PointerType * pty= dyn_cast<PointerType>(origty); 
      assert(pty);
       
      short tid= getIdx(AllTypeList, pty->getElementType());
        
      assert(tid >=0); 

      Value * desttid= 
            constructValueFromFunc (tid, hook, 1);
      
      // handle dest ptr 
       
      pushtoarglist (CI, 
                hook->getFunctionType()->getParamType(0), 
                destAddress, 
                dest_arglist,M);

      pushtoarglist (CI, 
                hook->getFunctionType()->getParamType(1), 
                desttid, 
                dest_arglist,
                M);

      // handle src ptr  
      
      pushtoarglist(CI, 
                hook_untag->getFunctionType()->getParamType(0), 
                srcAddress,     
                src_arglist,
                M);
  
  // handle dest ptr

    CallInst* destModifiedPtr= CallInst::Create (hook, dest_arglist, "");
    insertCastInstForArg (CI, dest_arglist);
    destModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            destAddress, 
            destModifiedPtr);

    // handle src ptr
    
    CallInst* srcModifiedPtr= CallInst::Create (hook_untag, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            srcAddress, 
            srcModifiedPtr);
 
  } 
      
#else   
    hook= M.getFunction ("FRAMER_forall_call_llvm_memtransfer");
    
    assert(hook!=nullptr && 
            "memTransfer hook funcion is empty\n");
    
    // handle dest ptr
       
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(0), 
                    destAddress,   
                    dest_arglist,M);
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesToCopy,
                    dest_arglist,
                    M);
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(2), 
                    numAlign,      
                    dest_arglist,M);
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(3), 
                    isVolatile,    
                    dest_arglist,M);

    // handle src ptr
    
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(0), 
            srcAddress,    
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(1), 
            numBytesToCopy,
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(2), 
            numAlign,      
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(3), 
            isVolatile,    
            src_arglist,M);


    // handle dest ptr

    CallInst* destModifiedPtr= CallInst::Create (hook, dest_arglist, "");
    insertCastInstForArg (CI, dest_arglist);
    destModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            destAddress, 
            destModifiedPtr);

    // handle src ptr
    
    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
            srcAddress, 
            srcModifiedPtr);

#endif
}

void 
Framer::doCallLLVMMemSet (CallInst * MSI, 
                          Instruction * successorInst, 
                          Module &M)
{
    /* (Src, Dest, numBytesToCopy, alignment, isVolatile )*/    
    dbg(errs()<<"MEM SET\n";) 
    
    Function * hook= nullptr; 
    
    Value * destAddress; 
    Value * val;            
    Value * numBytesToCopy; 
    Value * numAlign;
    Value * isVolatile;      
    
    vector<Value *> arglist;
    
#ifndef ENABLE_SPACEMIU 

    hook = M.getFunction ("FRAMER_forall_call_llvm_memset");

    if (MemSetInst * MI = dyn_cast<MemSetInst>(MSI)){
        destAddress     = MI->getRawDest();
        val             = MI->getValue();
        numBytesToCopy  = MI->getLength();
        //numAlign        = MI->getAlignmentCst();
        numAlign        = MI->getDestAlign();
        isVolatile      = MI->getVolatileCst(); 
    }
    else {
        destAddress=    MSI->getArgOperand(0); 
        val=            MSI->getArgOperand(1);
        numBytesToCopy= MSI->getArgOperand(2); 
        numAlign=       MSI->getArgOperand(3);  
        isVolatile=     MSI->getArgOperand(4); 
    }
    
    pushtoarglist (MSI, 
                   hook->getFunctionType()->getParamType(0), 
                   destAddress, arglist, M);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(1), 
                   val, arglist,M);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(2), 
                   numBytesToCopy,arglist,M);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(3), 
                   numAlign, arglist,M);
    pushtoarglist (MSI, hook->getFunctionType()->getParamType(4), 
                   isVolatile, arglist,M);
    
#else
    
    if (MemSetInst * MI = dyn_cast<MemSetInst>(MSI)){
     
    hook=  M.getFunction("FRAMER_untag_ptr_2"); 
    
    destAddress  = MI->getRawDest();
     
    pushtoarglist (MI, 
                   hook->getFunctionType()->getParamType(0), 
                   destAddress, arglist, M);
    }
    else {
        errs()<<"wtf is this?\n";
        exit(0);    
    }
#endif
    
    CallInst * modifiedPtr = CallInst::Create (hook, arglist, "");
    insertCastInstForArg (MSI, arglist);
    modifiedPtr->insertBefore (MSI);
    castAndreplaceUsesOfWithBeforeInst (MSI, destAddress, modifiedPtr);
}

//perlbench
void Framer::doCallstrlentemp(
                        CallInst *CI,
                        Instruction *successorInst, 
                        Module &M) {

    Function *hook= M.getFunction ("FRAMER_forall_call_strlentemp");
    assert(hook!=nullptr && "FRAMER_forall_call_strlentemp is null.\n");

    Value * srcAddress= CI->getArgOperand(0); 
    vector<Value *> src_arglist;

    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(0), 
            srcAddress,    
            src_arglist,M);

    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        srcAddress, 
                                        srcModifiedPtr);
}
//perlbench

//perlbench
void Framer::doCallstrchr(CallInst *CI,Instruction *successorInst, Module &M) {
    Function *hook= M.getFunction ("FRAMER_forall_call_strchr");
    assert(hook!=nullptr && "FRAMER_forall_call_strchr is null.\n");

    Value * srcAddress= CI->getArgOperand(0); 
    Value * myint= CI->getArgOperand(1); 

    vector<Value *> src_arglist;

    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(0), 
            srcAddress,    
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(1), 
            myint,
            src_arglist,M);

    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        srcAddress, 
                                        srcModifiedPtr);
}
//perlbench

void Framer::doCallstrcpy(CallInst * CI, Instruction * successorInst, Module &M) 
{
    Function * hook = M.getFunction ("FRAMER_forall_call_strcpy");
    Function * hooksrc = M.getFunction ("FRAMER_untag_ptr_2");
    assert(hook!=nullptr && "strcpy hook func is null.\n");
    
    Value * dest=CI->getArgOperand(0); 
    Value * src= CI->getArgOperand(1);  

    vector<Value *> dest_arglist;
    vector<Value *> src_arglist;
    
    /// create hook call for dest //
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(0), 
                    dest,   
                    dest_arglist,M);
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(1), 
                    src,   
                    dest_arglist,M); 
    
    CallInst* destModifiedPtr= CallInst::Create (hook, dest_arglist, "");
    insertCastInstForArg (CI, dest_arglist);
    destModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        dest, 
                                        destModifiedPtr);
    /// create hook call for src //
    pushtoarglist(CI, 
            hooksrc->getFunctionType()->getParamType(0), 
            src,    
            src_arglist,M);
    
    CallInst* srcModifiedPtr= CallInst::Create (hooksrc, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        src, 
                                        srcModifiedPtr);
}

void Framer::doCallstrn___ (CallInst * CI, Instruction * successorInst, Module &M, unsigned temp) 
{
    Function * hook = M.getFunction ("FRAMER_forall_call_strn___");
    
    assert(hook!=nullptr && "strn___ hook func is null.\n");

    Value * destAddress=    CI->getArgOperand(0); 
    Value * srcAddress=     CI->getArgOperand(1);  
    Value * numBytesToCopy= CI->getArgOperand(2); 

    ////
    Value * tempfuncval= constructValueFromFunc(temp,hook,2);  ////
    ////

    vector<Value *> dest_arglist;
    vector<Value *> src_arglist;
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(0), 
                    destAddress,   
                    dest_arglist,M);
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(1), 
                    numBytesToCopy,
                    dest_arglist,
                    M);
   
   ////
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(2), 
                    tempfuncval,
                    dest_arglist,
                    M);
 
    ////
    
    CallInst* destModifiedPtr= CallInst::Create (hook, dest_arglist, "");
    insertCastInstForArg (CI, dest_arglist);
    destModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        destAddress, 
                                        destModifiedPtr);

    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(0), 
            srcAddress,    
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(1), 
            numBytesToCopy,
            src_arglist,M);

   ////
    pushtoarglist (CI, 
                    hook->getFunctionType()->getParamType(2), 
                    tempfuncval,
                    src_arglist,
                    M);
 
    ////



    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        srcAddress, 
                                        srcModifiedPtr);
}

void Framer::handleArgAttr (CallInst * CI, Module & M)
{
    Function * hook=  M.getFunction ("FRAMER_untag_ptr_2");
    assert(isa<Function>(CI->getCaller()) && 
            "handleArgAttr's calledval is not function! do something..\n");
    
    Function * calledf= cast<Function>(CI->getCaller());
    Function::arg_iterator ait= calledf->arg_begin();
     
    for (unsigned i=0;i<CI->getNumArgOperands();i++){
        Value * From =CI->getArgOperand(i); 
        
        errs()<<"\nArg "<<i<<":: "<<*From<<"\n";
        if (Function * f= dyn_cast<Function>(From)) {
            if (f->getName().startswith("FRAMER_")) {
                ait++;
                continue;     
            }
        }
        if ((&*ait)->hasStructRetAttr() || (&*ait)->hasByValAttr()) { 
            
            errs()<<"sret or byval\n";
            vector<Value*> arglist; 
            pushtoarglist (CI, hook->getFunctionType()->getParamType(0), From, arglist, M);
            insertCastInstForArg (CI, arglist);
            CallInst * tagStrippedPtr = CallInst::Create (hook, arglist);
            
            tagStrippedPtr->insertBefore (CI);
            
            errs()<<"SRET new CI: "<<*CI<<"\n";
            
            if (From->getType()!=hook->getReturnType()){  
                Instruction* casted= createCastInst(tagStrippedPtr, From->getType());
                casted->insertBefore(CI);        
                CI->setOperand(i,casted);
            }
            else {
                CI->setOperand(i, tagStrippedPtr); 
            }
        }
        ait++; 
    }
    errs()<<"handleargattr called\n";
}

void Framer::doCallmem___ (CallInst * CI, Instruction * successorInst, Module &M) 
{
    Function * hook = M.getFunction ("FRAMER_forall_call_strn___");
    
    assert(hook!=nullptr && "doCallmem___ hook func is null.\n");

    Value * srcAddress=     CI->getArgOperand(0); 
    Value * numBytesToCopy= CI->getArgOperand(2); 

    vector<Value *> src_arglist;

    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(0), 
            srcAddress,    
            src_arglist,M);
    pushtoarglist (CI, 
            hook->getFunctionType()->getParamType(1), 
            numBytesToCopy,
            src_arglist,M);

    CallInst* srcModifiedPtr= CallInst::Create (hook, src_arglist, "");
    insertCastInstForArg (CI, src_arglist);
    srcModifiedPtr->insertBefore (CI);
    castAndreplaceUsesOfWithBeforeInst (CI, 
                                        srcAddress, 
                                        srcModifiedPtr);
}

void Framer::doCallExternalFunc (CallInst * CI, Instruction * successorInst, Module &M)
{
    dbg(errs()<<"entered external\n";)
    
    Function * hook     = M.getFunction ("FRAMER_untag_ptr_2");

    for (unsigned i = 0 ; i < CI->getNumArgOperands (); i++) {
        Value * From =CI->getArgOperand(i); 

        if (! (From->getType()->isPointerTy()
            || From->getType()->isAggregateType())) {
            dbg(errs()<<"\tNeither Pointer nor aggregated. Skipping..\n";)
            continue;
        }
        if (isSafePtr(From->stripPointerCasts())) {
            continue; 
        }
        
        // can we skip constant? constant (such as gep) can be also out-of-bound, right?
        
        vector<Value *> arglist; 
        pushtoarglist (CI, hook->getFunctionType()->getParamType(0), From, arglist, M);
        insertCastInstForArg (CI, arglist);
        CallInst * tagStrippedPtr = CallInst::Create (hook, arglist);
        tagStrippedPtr->insertBefore (CI);
        
        if (From->getType()!=hook->getReturnType()){  
            Instruction* casted= createCastInst(tagStrippedPtr, From->getType());
            casted->insertBefore(CI);        
            CI->setOperand(i,casted);
        }
        else {
            CI->setOperand(i, tagStrippedPtr); 
        }
    }
    dbg(errs()<<"new CI: "<<*CI<<"\n";)
}

static bool
isWrapperCall (CallInst * ci)
{
  for (int i=0; i< ci->getNumArgOperands (); i++) {

    Function * fp= dyn_cast<Function>(ci->getArgOperand(i));

    if (!fp) continue; 

    if (isCustomWrapper(fp)) return true; 
  
  }

  return false;

}

//DISASTER!!! REWRITE LATER
Instruction* 
Framer::doCallInst (CallInst * CI, 
                    Instruction * successorInst,
                    AAResults & AA,
                 #ifdef ENABLE_SPACEMIU
                    DominatorTree & DT,
                    CallGraph & CG,
                    vector <AllocaInst*> & LocalUnions,
                 #endif
                    Module &M)
{
    Value * calledValue= CI->getCaller()->stripPointerCasts();
    Instruction * toBeRemoved = NULL;

 #ifdef ENABLE_SPACEMIU
 
    handleHeapUnions(CI, HeapUnions);

 #endif
    
    if (Function * calledfunc = dyn_cast<Function>(calledValue))  { 
       
      //// interposed malloc function seemed replaced. so filter it out.
        
        if (calledfunc->getName().startswith("FRAMER")) {
            return nullptr; 
        }
     
        // If function pointer (particular for gcc)     
        // if (calledfunc == M.getFunction("_obstack_begin")) {
        if (isWrapperCall(CI)) {
            errs()<<"isWrapperCall. do something "<<*CI<<"\n";
            exit(0);  
        }
        if (calledfunc == M.getFunction("_obstack_begin")) {
            
            //errs()<<"### _obstack_begin ### CI 1: "<<*CI<<"\n";
            //errs()<<"    in func: "<<(CI->getFunction())->getName()<<"\n"; 
            
            CI->setArgOperand(3, M.getFunction("FRAMER_xmalloc")); 
            CI->setArgOperand(4, M.getFunction("FRAMER_xfree")); 
            //errs()<<"### changed: "<<*CI<<"\n";
            
           //     JIN: READ! 
           //     xmalloc in gcc pass malloc as a function pointer argument
           //     to a library function, and segmentation fault inside the lib
           //     function! so had to do this. Maybe this is resolved by 
           //     untagging by hardware support?
           //return nullptr;      
        }
      
        if (calledfunc == M.getFunction("_obstack_newchunk")) {
           ; 
        }
        if (calledValue == M.getFunction(StringRef("malloc"))) {
            toBeRemoved= doCallInstMalloc (CI, successorInst, AA, DT, CG, M);  
        }
        else if (calledValue == M.getFunction(StringRef("realloc"))) {
            toBeRemoved= doCallInstRealloc (CI, successorInst, AA, DT, CG, M);  
        }
        else if (
            calledValue == M.getFunction(StringRef("free")) ||
            //calledValue == M.getFunction(StringRef("realloc")) ||
            calledValue == M.getFunction(StringRef("calloc")) || 
            calledValue == M.getFunction(StringRef("FRAMER_malloc")) ||
            calledValue == M.getFunction(StringRef("FRAMER_free")) ||
            calledValue == M.getFunction(StringRef("FRAMER_realloc")) ||
            calledValue == M.getFunction(StringRef("FRAMER_calloc")) || 
            calledValue == M.getFunction(StringRef("strcmp")) || 
            calledValue == M.getFunction(StringRef("strncmp")) || 
            calledValue == M.getFunction(StringRef("strncpy")) || 
            calledValue == M.getFunction(StringRef("memcmp")) || 
            calledValue == M.getFunction(StringRef("memchr")) || 
            calledValue == M.getFunction(StringRef("strchr")) || 
            calledValue == M.getFunction(StringRef("strncat")) || 
            calledValue == M.getFunction(StringRef("strtol")) || 
            calledValue == M.getFunction(StringRef("strcpy")) 
            ) {
            /// Make sure these functions are not treated as external one!
            // otehrwise, framer will untag the arg, and it's problematic for realloc
            return NULL; 
        }
        else if (calledfunc->getName().startswith("llvm.memcpy") 
            || calledfunc->getName().startswith("llvm.memmove")) {
            
            doCallLLVMMemTransfer (CI, successorInst, AA, 
                                #ifdef ENABLE_SPACEMIU
                                  LocalUnions, 
                                #endif
                                  M);
          
        }
        else if (calledfunc->getName().startswith("llvm.memset")) {
            doCallLLVMMemSet (CI, successorInst, M);
        }
        else if (calledfunc->getName().startswith("strxfrm")){
            errs()<<"string function called. do something. test if the func does not check..\n";
            errs()<<*CI<<"--\n";
            exit(0);
        }
        else if (calledfunc->isDeclaration()) {
            doCallExternalFunc (CI, successorInst, M);
        }
        else {
            ;
        }
    }
    /// only for perlbench to avoid Call graph construction..
    else if (CI->getFunction()->getName().equals("Perl_PerlIO_flush")
            ) {
        doCallExternalFunc (CI, successorInst, M);
    }
    // perlbench

    else if (Instruction * inst= dyn_cast<Instruction>(calledValue)) {
        

        if (isa<PHINode>(inst)) {
            // This is for running perlbench. CPU 2006. delete later and do proper thing. 
            if (inst->getParent()->getParent()->getName().equals("PerlIO_openn") 
                || inst->getParent()->getParent()->getName().equals("Perl_sortsv")
                || inst->getParent()->getParent()->getName().equals("S_mergesortsv")
                || inst->getParent()->getParent()->getName().equals("S_sortsv_desc")) {
                ; 
            }
            else {
                //errs()<<"** do something. call phi -- "<<*inst<<"\n";
                //errs()<<"\t"<<"in func "<<inst->getFunction()<<"\n";
                //exit(0);
            }
        }
        else if (LoadInst * li= dyn_cast<LoadInst>(inst)){
            //it may not be external func, but to avoid handling CFG, we just untag all the pointer args.

            // 1. get pointer operand li->getOperand() (func_ptr)
            // 2. get uses of func_ptr. -> if store inst && func_ptr is SI's pointer ptr_op
            // && no SI uses between the SI and li, where each SI's ptr op is not func_ptr
            //, if it's external function. then docallexternalfunc. otherwise do nothing. 

            Value * getfunc= li->getPointerOperand();
            while (!isa<Function>(getfunc->stripPointerCasts())) {
                if (LoadInst * lii = dyn_cast<LoadInst>(getfunc->stripPointerCasts())) {
                    getfunc= lii->getPointerOperand();        
                }
                else if (CallInst * lii=dyn_cast<CallInst>(getfunc->stripPointerCasts())) {
                    getfunc= lii->getCaller(); 
                }    
                else {
                    //errs()<<"Load's op (cant track assignment): "<<*(getfunc->stripPointerCasts())<<"\n";
                    //errs()<<"Function: "<<li->getFunction()->getName()<<"\n";
                    break;
                    //return NULL;
                    //exit(0);
                }
            }
            Function * calledfunc= dyn_cast<Function>(getfunc);
            if (!calledfunc)  return NULL;

            if (calledfunc == M.getFunction("_obstack_begin")) {
                ;
            }

            if (calledfunc == M.getFunction(StringRef("malloc"))) {
                toBeRemoved= doCallInstMalloc (CI, successorInst, AA, DT, CG, M);  
            }
            else if (calledfunc == M.getFunction(StringRef("realloc"))) {
                toBeRemoved= doCallInstRealloc (CI, successorInst, AA, DT, CG, M);  
            }

            if (//calledfunc == M.getFunction(StringRef("malloc")) ||
                //calledfunc == M.getFunction(StringRef("free")) ||
                //calledValue == M.getFunction(StringRef("realloc")) ||
                calledValue == M.getFunction(StringRef("calloc")) || 
                calledValue == M.getFunction(StringRef("FRAMER_malloc")) ||
                calledValue == M.getFunction(StringRef("FRAMER_free")) ||
                calledValue == M.getFunction(StringRef("FRAMER_realloc")) ||
                calledValue == M.getFunction(StringRef("FRAMER_calloc")) || 
                calledValue == M.getFunction(StringRef("strcmp")) || 
                calledValue == M.getFunction(StringRef("strncmp")) || 
                calledValue == M.getFunction(StringRef("strncpy")) || 
                calledValue == M.getFunction(StringRef("memcmp")) || 
                calledValue == M.getFunction(StringRef("memchr")) || 
                calledValue == M.getFunction(StringRef("strchr")) || 
                calledValue == M.getFunction(StringRef("strncat")) || 
                calledValue == M.getFunction(StringRef("strtol")) || 
                calledValue == M.getFunction(StringRef("strcpy"))) {
                return NULL; // *functions to be interposed at link time*
            }
            else if (calledfunc->getName().startswith("llvm.memcpy") 
                    || calledfunc->getName().startswith("llvm.memmove")) {
                doCallLLVMMemTransfer (CI, successorInst, AA, 
                                     #ifdef ENABLE_SPACEMIU
                                       LocalUnions, 
                                     #endif  
                                       M);
            }
            else if (calledfunc->getName().startswith("llvm.memset")) {
                doCallLLVMMemSet (CI, successorInst, M);
            }
            else if (calledfunc->getName().startswith("strxfrm")){
                errs()<<"string function called. do something. test if the func does not check..\n";
                errs()<<*CI<<"--\n";
                exit(0);
            }

////////////
           
           /* else if (calledfunc->getName().startswith("str")) {
                errs()<<"2 called func may be string func. do something. \n";
                errs()<<calledfunc->getName()<<"\n";
                exit(0);
            }*/
            else if (calledfunc->isDeclaration()) {  
                doCallExternalFunc (CI, successorInst, M);
            }
            else {
                //errs()<<"FuncPTR Inst: "<<*CI<<" in "<<CI->getFunction()->getName()<<"\n"; 
                dbg(errs()<<"invoking framer hook!\n";) 
            }
        }
    } // upto here. when calledvalue == inst

    else if (isa<Argument>(calledValue)) {
        // THIS is only for running perlbench. CPU 2006.
       

        if (CI->getParent()->getParent()->getName().equals("perl_parse")
            || CI->getParent()->getParent()->getName().equals("S_parse_body")
            || CI->getParent()->getParent()->getName().equals("S_qsortsvu")){
            ; 
        }
        else { 
            //errs()<<"\n\tcall arg. do something. CI: "<<*CI<<"\n";
            //errs()<<"\tfunc holding CI: "<<CI->getParent()->getParent()->getName()<<"\n";
            //do something.
        } 
    }
    else if (isa<InlineAsm>(calledValue)) {
        /// this is only get perlbench through. do something later.
        if (CI->getParent()->getParent()->getName().equals("S_unpack_rec")
            || CI->getParent()->getParent()->getName().equals("S_pack_rec")
            || CI->getParent()->getParent()->getName().equals("S_mergesortsv")
            || CI->getParent()->getParent()->getName().equals("Perl_my_poll")
            || CI->getParent()->getParent()->getName().equals("store")
            || CI->getParent()->getParent()->getName().equals("store_blessed")
            || CI->getParent()->getParent()->getName().equals("store_scalar")
            || CI->getParent()->getParent()->getName().equals("store_array")
            || CI->getParent()->getParent()->getName().equals("store_hash")
            || CI->getParent()->getParent()->getName().equals("store_tied_item")
            || CI->getParent()->getParent()->getName().equals("store_code")
            || CI->getParent()->getParent()->getName().equals("store_other")
            || CI->getParent()->getParent()->getName().equals("retrieve")
            || CI->getParent()->getParent()->getName().equals("retrieve_lscalar")
            || CI->getParent()->getParent()->getName().equals("old_retrieve_array")
            || CI->getParent()->getParent()->getName().equals("old_retrieve_hash")
            || CI->getParent()->getParent()->getName().equals("retrieve_array")
            || CI->getParent()->getParent()->getName().equals("retrieve_hash")
            || CI->getParent()->getParent()->getName().equals("retrieve_blessed")
            || CI->getParent()->getParent()->getName().equals("retrieve_idx_blessed")
            || CI->getParent()->getParent()->getName().equals("retrieve_hook")
            || CI->getParent()->getParent()->getName().equals("retrieve_tied_idx")
            || CI->getParent()->getParent()->getName().equals("retrieve_utf8str")
            || CI->getParent()->getParent()->getName().equals("retrieve_flag_hash")
            || CI->getParent()->getParent()->getName().equals("retrieve_netint")
            ) {
        // this is only for perlbench. do proper thing later.
            ;
        }
        else {
           errs()<<"\tCall ASM. do something -- "<<*CI<<"\n";
           //exit(0); 
        }
    }
    else if (MemTransferInst * MCI = dyn_cast<MemTransferInst>(CI) ) {
        if (HookDefForCalledFuncExists[LLVMMemTransferIsCalled]) {
            doCallLLVMMemTransfer (MCI, successorInst, AA, 
                                 #ifdef ENABLE_SPACEMIU
                                   LocalUnions, 
                                 #endif
                                   M);
        }
    }    
    else if (MemSetInst * MSI = dyn_cast<MemSetInst>(CI) ) {
        if (HookDefForCalledFuncExists[LLVMMemSetIsCalled]) {
            doCallLLVMMemSet (MSI, successorInst, M);
        }
    }
    else {
        errs()<<"CALL. do something:: "<<*CI<<"\n"; 
        errs()<<"calledvalue: "<<*calledValue<<"\n";
        exit(0);
    }

// TODO. CONSIDER ME: Do we need this?? Commenting out now..
//    if (CI->hasStructRetAttr()||CI->hasByValArgument()) { 
        
//        handleArgAttr(CI, M);
//    }
//  
    
    return toBeRemoved;
}

#ifdef ENABLE_SPACEMIU

void 
Framer::doBitCastInst (BitCastInst * BCI, 
                       Instruction * sucIns,
                       AAResults & AA,
                       vector <AllocaInst*> & ais, 
                       Module & M)
{
#ifdef DISABLE_TYPECAST_CHECKS
    
    return;

#endif 
       
    PointerType * destptr= dyn_cast<PointerType>(BCI->getDestTy()); 
    PointerType * srcptr= dyn_cast<PointerType>(BCI->getSrcTy());
    
    if (!destptr || !srcptr) return;  
     
    dbg(errs()<<"\nBitcast SRC: "<<*BCI->getOperand(0)<<", DEST Ty: "<<*BCI->getDestTy()<<"\n");
    

    /// what if it's union type?  
    /// 1. src is union type && the pointer is allocation with the same union type.
    /// 2. src is union type && the pointer is not allocation
    /// union type cast checking first or downcast? 
   
     
    if (isUnionTy(srcptr->getElementType()) 
        && isAliasWithUnionObj(BCI->getOperand(0), AA, ais, GVUnions, HeapUnions, M)
        && isSafeCastofUnionTy(srcptr->getElementType(), 
                              destptr->getElementType(),
                              &M.getDataLayout())) {
         
        return;     
    }

  #ifndef ENABLE_FUNCTION_POINTER   
    //if ((srcptr->getElementType())->isFunctionTy()
    //    || (destptr->getElementType())->isFunctionTy()) {
        //errs()<<"  :: Function ptr casting\n";
        //return;
    //}
  #endif
 
    if (!isDownCast (srcptr, destptr, AllTypeList, DownCasts)
        && !((srcptr->getElementType())->isFunctionTy() 
              || (destptr->getElementType())->isFunctionTy())) {
        
      return; 
    }
    dbg(errs()<<"  ----> Downcast\n";)

    ///////////
    Function * hook = M.getFunction("FRAMER_forall_bitcast");
    
    short desttid= getIdx(AllTypeList,
                          destptr->getElementType());
    
    assert(desttid >=0); 
     
    //unsigned destTsize= 
    //    Framer::getBitwidth(destptr->getElementType())/8; 
    
    bool isunion= isUnionTy(destptr->getElementType());
        
//// voronoi debuggin
dbg(    
    errs()<<"## bci: "<<*BCI<<" ( "<<BCI->getFunction()->getName()<<" )\n";
    errs()<<"  src:"<<getIdx(AllTypeList,srcptr->getElementType())<<", ";  
    errs()<<*srcptr->getElementType()<<"\n";
    errs()<<"  dest: "<<desttid<<", ";
    errs()<<*destptr->getElementType()<<"\n";
)
////////
    //errs()<<"  -> hooked\n";
    
    vector<Value *> arglist;
    
    pushtoarglist (sucIns, 
        hook->getFunctionType()->getParamType(0), 
        BCI, arglist,M);
    
    Value * dest= 
            constructValueFromFunc (desttid, hook, 1);
    pushtoarglist (sucIns, 
        hook->getFunctionType()->getParamType(1), 
        dest, arglist,M);
    
    Value * constisUnionTy= 
            constructValueFromFunc(isunion, hook, 2); 
    pushtoarglist (sucIns, 
        hook->getFunctionType()->getParamType(2), 
        constisUnionTy, arglist,M);
    
    //Value * constdestTsize= 
    //        constructValueFromFunc(destTsize, hook, 3); 
    //pushtoarglist (sucIns, 
    //    hook->getFunctionType()->getParamType(3), 
    //    constdestTsize, arglist,M);
    
    pushtoarglist (sucIns, 
        hook->getFunctionType()->getParamType(3), 
        constructValueFromFunc(MaxOffset, hook, 3), 
        arglist,M);
   
    pushtoarglist (sucIns, 
        hook->getFunctionType()->getParamType(4), 
        constructValueFromFunc(AllTypeList.size(), hook, 4), 
        arglist,M);
     
     //TODO set type table row/column count as a global on pass code, and pass them to the hook as a constant arg\n");
     
    CallInst * modified= CallInst::Create(hook, arglist, "");
    insertCastInstForArg (sucIns, arglist);
    modified->insertBefore(sucIns);

    //errs()<<"\nSRC Ty: "<<*BCI->getSrcTy()<<", DES Ty: "<<*BCI->getDestTy()<<" ("<<*BCI->getOperand(0)<<")\n";
    //errs()<<"modified: "<<*modified<<"\n"; 
}

#endif

uint64_t  
Framer::getArraySizeforGV (Type * allocatedObjTy) 
{
    if (ArrayType * arr = dyn_cast<ArrayType>(allocatedObjTy)){
        uint64_t size = arr->getNumElements();
        return size; //uint64_t type..
    }
    else {
        return 1;
    }
}

bool Framer::isToBeTaggedType (Type* t)
{
    bool isToBeTagged = 0;

    if ( 
      #ifdef TRACK_STRUCT_ALSO
        t->isVectorTy() || 
        t->isStructTy()||
      #endif
        t->isArrayTy()){ 
         isToBeTagged = 1;
    }
    return isToBeTagged; 
}
/*
Value* Framer::createPads(Value* val, Module &M)
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

/*
void Framer::padObject (Value* obj, Module &M)
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
nn
        if (gvalign == 16) {
            GlobalVariable* dummyheader= new GlobalVariable( M,
                    HeaderTy,
                    false,
                    GV->getLinkage(),
                    nullHeader,
                    "",
                    header);
            dbg(errs()<<"\tAlignment of GV is 16, hence, 2 headers added\n";) 
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
*/

Constant* Framer::tagConstantPtr (Constant* ptr, 
                                        Constant* tag, 
                                        Constant* flag, 
                                        Module & M)
{
    //dbg(errs()<<"entered tagConstantPtr\n";)
    Constant* tagInPosition= 
        ConstantExpr::getShl(tag,ConstantInt::getSigned(Type::getInt64Ty(M.getContext()),48));
    Constant* flagInPosition=
        ConstantExpr::getShl(flag, 
                            ConstantInt::getSigned(Type::getInt64Ty(M.getContext()), 63));
    //dbg(errs()<<"exiting tagConstantPtr\n\n";) 
    
    return ConstantExpr::getOr (ConstantExpr::getPtrToInt(ptr, tagInPosition->getType()), 
                                ConstantExpr::getOr(tagInPosition, flagInPosition));   
}

Constant* Framer::getPaddedEndInt(GlobalVariable* paddedGV, Module & M)
{
    vector<Value*> idx={ConstantInt::get(Type::getInt32Ty(M.getContext()), 0),
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 2)};
    Constant* endAddr= 
        ConstantExpr::getInBoundsGetElementPtr (cast<PointerType>(paddedGV->getType()->getScalarType())->getContainedType(0u),
                                                paddedGV,
                                                idx);
    return ConstantExpr::getPtrToInt(endAddr, Type::getInt64Ty(M.getContext()));
}

Constant* Framer::getLogFrameSize (Constant* base, Constant* end, Module & M)
{
    dbg(errs()<<"inside getlogframesize\n";) 
    
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
    dbg(errs()<<"exiting getlogframesize..\n";)
    return ConstantExpr::getSub(ConstantInt::get(Type::getInt64Ty(M.getContext()), 64),
                                clzResult);
}

Constant* Framer::getOffset (Constant* base, Module & M)
{
    //mask=. flag =1
    Constant* getOffsetMask= 
        ConstantInt::getSigned(Type::getInt64Ty(M.getContext()), 0x7FFF);
    return ConstantExpr::getAnd(base, getOffsetMask);
}

Constant* 
Framer::getTaggedConstantPtr( GlobalVariable* basePadded,
                                      Constant* origPtr,
                                      Module & M)
{
    
    Constant* basePaddedInt= ConstantExpr::getPointerCast(basePadded,
                                                        Type::getInt64Ty(M.getContext()));
    dbg(errs()<<"basePaddedInt: "<<*basePaddedInt<<"\n";)
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
        
    dbg(errs()<<"exiting getTaggedConstantPtr\n";)
    return ConstantExpr::getIntToPtr(taggedPtr, origPtr->getType());
}

/*void Framer::updateHeaderIfSmalledFramed (Constant* tagged, GlobalVariable* ) 
{
    //extract flag. (1) create mask (1000..). (2) And (mask, tagged)  
    Constant* getFlag= ConstantExpr::getAnd(initVec, tagged);
    Constant* cond_isSmallFrame= ConstantExpr::getICmp (ICMP_EQ, getFlag, initVec);
    Constant* header?= ConstantExpr::getSelect (cond_isSmallFrame, 

    //if small-frame (1?), get header address (idx 0 0? create gep etc)
    
    // write in the header. store id and size. changes to headerT should be caught by assertion here.
    
    // then what should be changed to avoid duplicate updates?  
}*/

Constant* 
Framer::createHeaderInitializer (GlobalVariable* GV,
                                         unsigned Tid,
                                         unsigned numElems,
                                         unsigned numBytesOfElemTy)
                                         //unsigned gvsize)
{
    vector<Constant*> fields= 
        {ConstantInt::get(HeaderTy->getElementType(0), Tid, true), 
         ConstantInt::get(HeaderTy->getElementType(1), numElems*numBytesOfElemTy, true), 
      #ifdef ENABLE_SPACEMIU
         ConstantInt::get(HeaderTy->getElementType(2), numBytesOfElemTy, true), 
         Constant::getNullValue(HeaderTy->getElementType(3)),
         Constant::getNullValue(HeaderTy->getElementType(4))};
      #else
         Constant::getNullValue(HeaderTy->getElementType(2))};
      #endif

    return ConstantStruct::get(HeaderTy, fields);
}

GlobalVariable * 
Framer::createGVHoldingTag (Constant * origGV, 
            Constant * tagged, Module & M, 
            GlobalVariable * paddedGV, GlobalVariable * GVToDel)
{
    Type * ty= tagged->getType();
    
    GlobalVariable * gvTag= new GlobalVariable(M, 
                                               ty, 
                                               false, 
                                               GlobalValue::ExternalLinkage,
                                               origGV,
                                               Twine("newGVHoldingTag_").concat(GVToDel->getName()),
                                               GVToDel);

                                               
    return gvTag;                        
}

GlobalVariable* 
Framer::doGlobalVariable (GlobalVariable * GV, 
                          Function * F, 
                          Instruction * insertBeforeMe, 
                          Module & M,
                          //set<pair<GlobalVariable*, Constant*>> & inits)
                          set<tuple<GlobalVariable*, Constant*, Constant*>> & inits)
{
    /*  Hook sig: void * FRAMER_global_variable 
        (void * gv, enum BASICType assignedTy, uint64_t numElems, unsigned numBytes) where
        GV is the location of GV, assignedTY is the typeID of allocated object in enumtype,
        numElems is #elements of Array (1 for a non-array), 
        numBytes is #num of bytes of allocated obj (numbytes of an element of an Array if it's array).
        currently inserBeforeMe is the 1st inst of 1st BB of main. (new BB)
     */
    dbg(errs()<<"\nGV-- "<<*GV<<"\n";) 
    
    if (GV->use_empty()) {
        dbg(errs()<<"\tuse list empty. skipping..\n";)
        return nullptr;
    }
   
    if (GV->getName().equals("Alphabet")) {
        //errs()<<"skip Alphabet..\n"; // Segmentation fault due to this gv! disabled..
                                        //debug later..
        return nullptr; 
    }
    //unsigned FramerTyID;
    int FramerTyID= 0;
    unsigned numElems= 0;
    unsigned numBytesOfElemTy= 0;

    Type * assignedObjTy = 
        cast<PointerType>(GV->getType())->getElementType();
    Type* mytype=nullptr;

  #ifndef TRACK_STRUCT_ALSO
    /* if global object is struct typed, skip hooking it. */ 
    if (isa<StructType>(assignedObjTy)) return nullptr;
  #endif     
   
  #ifndef ENABLE_TRACK_ARRAYS 
    if (isa<ArrayType>(assignedObjTy)) return nullptr; 
  #endif

////
//seg fault! We currently skip padding/tagging this ..

  if (GV->getName().startswith("PL_sv_undef")) { 
      //-----> 
    return nullptr;
  }
////  
    if (ArrayType * arr = dyn_cast<ArrayType>(assignedObjTy)) {
        numElems = arr->getNumElements();
        Type* elemTyOfArray = arr->getElementType();
        mytype= PointerType::get(elemTyOfArray, GV->getType()->getPointerAddressSpace());
        dbg(errs()<<"mytype: "<<*mytype<<"\n";) 
        
        numBytesOfElemTy = (Framer::getBitwidth (elemTyOfArray))/8;
        assert(numBytesOfElemTy!=0 &&"numBytesOfElemTy is zero\n");
        
        unsigned temptid= getFramerTypeID(elemTyOfArray);
        FramerTyID = (int)temptid;
        assert(temptid==((int)FramerTyID));
    }
    else if (StructType* st=dyn_cast<StructType>(assignedObjTy)){
        if (st->isOpaque()) {
            errs()<<"OPAQUE struct type. do not pad me. skip me later instead of exiting\n";
            errs()<<*st<<"\n";
            exit(0);
        }
        numElems= 1;
        numBytesOfElemTy= (Framer::getBitwidth (assignedObjTy))/8; 
        assert(numBytesOfElemTy!=0 &&"numBytesOfElemTy is zero\n");
        
        unsigned temptid= getFramerTypeID(assignedObjTy); 
        FramerTyID= (int)temptid; 
        assert(temptid==((int)temptid));
        
        mytype=st->getElementType(0); 
        //get argument for getbitwidth. (it should be elemty)
    }
    else {
        errs()<<"Allocated global variable is vector type! do something\n";
        exit(0);
    }
    dbg(errs()<<"\nGV: "<<*GV<<"\n";) 
    
tempGVcount++;
    //----- wrap an object into struct from here.
    vector<Type*> paddedObjTyList= {HeaderTy, assignedObjTy, OffByOneTy}; 
    //vector<Type*> paddedObjTyList= {HeaderTy, assignedObjTy}; //** offbyone fix 
    
    StructType* paddedTy= StructType::create (M.getContext(), 
                                            paddedObjTyList, 
                                            "paddedStruct",
                                            true);
    /////////////////////////////////////////////
    //// -- create initializer from here. ///////

////////debug.1
    
 //   errs()<<"PADDING GV: "<<GV->getName()<<"\n"; 
     
    Constant* GVinitializer;
    Constant* hdInitializer;
    bool isConstant=false;
    
    if (GV->hasInitializer()) {
        GVinitializer= GV->getInitializer();    
    }
    else {
        GVinitializer= Constant::getNullValue(assignedObjTy); 
    }
   
   // errs()<<" create HeaderInitializer starts\n";
     
        // ?? difference between hasInitializer (above) and isConstant? forgot..  
    if (GV->isConstant()) {
        hdInitializer= createHeaderInitializer (GV, 
                                            FramerTyID,
                                            numElems,
                                            numBytesOfElemTy);
        isConstant=true;
    }
    else {
        hdInitializer= Constant::getNullValue(HeaderTy);
    }
   // errs()<<" create HeaderInitializer ends\n";
    
//// debug.2 
     
    vector<Constant*> paddedObjlist={hdInitializer, //Constant::getNullValue(HeaderTy), 
                                     GVinitializer, 
                                     Constant::getNullValue(OffByOneTy)}; //** offbyone fix
    Constant* paddedObj= ConstantStruct::get(paddedTy, paddedObjlist); 
    //// --- create initializer upto here.
    
    ///////////////////////////////////////////////
    ////--- create/insert wrapped object.
    GlobalVariable* paddedGV= new GlobalVariable(M,
                                                paddedTy, 
                                                GV->isConstant(),
                                                GV->getLinkage(),
                                                paddedObj,
                                                Twine("GVpad_").concat(GV->getName()), //"paddedGV",
                                                GV);
   
    dbg(errs()<<"padded GV: "<<*paddedGV<<"\n";)
    
    paddedGV->setAlignment(Align(16)); //set it as 16, since sometimes memset's alignment is 16.
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

    dbg(errs()<<"origObj: "<<*origObj<<"\n";)
   
    //////////////////////////////////////////////////////////// 
    // get tag for constantGV, and tag it.
    Constant* taggedConstantPtr= getTaggedConstantPtr(paddedGV, origObj, M);
    
    // Create a global variable holding tagged pointer as an initializer,
    // and replace uses of the GV with this variable. 
    // this is to avoid heavy constant expression for a tag is propagated
    // repetitively.
    GlobalVariable * gvTG= createGVHoldingTag(origObj, taggedConstantPtr, M, paddedGV, GV); 

    dbg(errs()<<"gvTag: "<<*gvTG<<"\n";)

#ifndef DISABLE_TAGGING_GV
    ////////////////////

    // now iterating uses of GV again, since an GV initializer with constant expr
    // is illegal.
    castAndreplaceAllUsesWithForGV(GV, taggedConstantPtr, 
                            origObj, gvTG, FramerLoads, inits); 
   

    /// now creating hook function call
   
    // we saved the operand(0) of inttoptr, since bitcast (Ty* inttoptr blibli to Ty), Ty2 
    // are merged into Ty2* inttoptr blibli to Ty2
   // paddedGVs.push_back(taggedConstantPtr); // no need to insert origObj 
    paddedGVs.push_back(taggedConstantPtr->getOperand(0)); // no need to insert origObj 
     
    vector<Value *> arglist;
    pushtoarglist (insertBeforeMe, 
            F->getFunctionType()->getParamType(0), 
            taggedConstantPtr, //ptrtype //origObj, //GV, 
            arglist,M);
#else
//else of DISABLE_TAGGING_GV

    castAndreplaceAllUsesWithForGV(GV, origObj, 
                            origObj, gvTG, FramerLoads, inits); 
    
    vector<Value *> arglist;
    pushtoarglist (insertBeforeMe, 
            F->getFunctionType()->getParamType(0), 
            taggedConstantPtr, 
            arglist,M);

#endif
// endif of DISABLE_TAGGING_GV

    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(1) , 
                    constructValueFromFunc(FramerTyID, F, 1), 
                    arglist,M); 

    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(2) , 
                    constructValueFromFunc (numElems, F, 2), 
                    arglist,M); 
                    //numElemsCons, arglist); 
    
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(3) , 
                    constructValueFromFunc(numBytesOfElemTy, F, 3), 
                    arglist,M);
     
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(4) , 
                    constructValueFromFunc(isConstant, F, 4), 
                    arglist,M);
    
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(5) , 
                    gvTG, 
                    arglist,M);

  #ifdef ENABLE_SPACEMIU  
   
    bool is_union= isUnionTy(assignedObjTy);
    Value * constisUnionTy= 
            constructValueFromFunc(is_union, F, 6); 
 
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(6) , 
                    constisUnionTy, 
                    arglist,M);

  #endif

////debug.3.5.try this   
/*
    vector<Value*> idx_base={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 1)};
    vector<Value*> idx_end={ConstantInt::get(IntegerType::get(M.getContext(), 32), 0),
                        ConstantInt::get(IntegerType::get(M.getContext(), 32), 2)};
    Constant* mybase= 
        ConstantExpr::getGetElementPtr(
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
                    arglist,M);
    pushtoarglist (insertBeforeMe, 
                    F->getFunctionType()->getParamType(6), 
                    myend, //ptrtype //origObj, //GV, 
                    arglist,M);
*/

///debug.4.   

/// perlbench.s
/*    unsigned isPLtokenbuf=0;
    if (GV->getName().equals("PL_tokenbuf")){
        errs()<<"is isPLtokenbuf\n";
        isPLtokenbuf=1;
    }
    pushtoarglist ( insertBeforeMe, 
                    F->getFunctionType()->getParamType(7) , 
                    constructValueFromFunc(isPLtokenbuf, F, 7), 
                    arglist,M);
 */
         
/// perlbench.e
    
    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
    
    updatepaddedGV(GV,origObj,inits); 
    
    return GV;
} 

/*
void Framer::doGlobalVariable (GlobalVariable * GV, Function * F, Instruction * insertBeforeMe, Module & M)
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
        numBytesOfElemTy = (Framer::getBitwidth (assignedObjTy))/8; //get argument for getbitwidth. (it should be elemty)
        errs()<<"GV non Array. #bytesofElemTy: "<<numBytesOfElemTy<<"\n";
    }
    else {
        //numBitsOfElemTy = Framer::getBitwidth (cast<ArrayType>(GV->getType())->..? //how can I get the type of global array?
        numBytesOfElemTy = (Framer::getBitwidth (cast<ArrayType>(assignedObjTy)->getElementType()))/8; //get argument for getbitwidth. (it should be elemty)
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

bool Framer::hasConstructorAttribute (GlobalVariable * GV)
{
    return (GV->hasAppendingLinkage() && GV->getName().equals(StringRef("llvm.global_ctors"))); 
}

bool Framer::hasDestructorAttribute(GlobalVariable *GV)
{
    return (GV->hasAppendingLinkage() && GV->getName().equals(StringRef("llvm.global_dtors"))); 
}

void Framer::runOnGlobalVariables (Module &M)
{
    errs()<<"runOnGlobalVariables starting..\n";
   
    //set<pair<GlobalVariable*, Constant*>> inits;
    set<tuple<GlobalVariable*, Constant*, Constant*>> inits;
    /* tuple: original GV, Taggedpointer (initializer), untagged for store inst */
    
    Function * hook = M.getFunction("FRAMER_forall_global_variable");
    assert(hook!=nullptr && "GV hook is null\n");
    /* getting the place where the new instruction should be inserted to 
    Function::iterator it_fstBB = Func_main->begin(); 
    it_fstBB++; // the second BB of Main (BB in charge of global variables)
    Instruction * insertBeforeMe = --(it_fstBB->end());
    */

    Instruction * insertBeforeMe= &*(Func_main->begin()->begin()); 
    GlobalVariable* successorGV = &*M.global_begin();
    vector<GlobalVariable*> toBeRemovedList; 
   
    for (Module::global_iterator gi = M.global_begin(), 
            ge=M.global_end(); gi!=ge ; ++gi) {
        
        dbg(errs()<<"GI:: "<<*gi<<"\n";)
                   
        if (&*gi != &*successorGV) {
        //    errs()<<"\tAdded by hook. skipping..\n";
            continue;
        }
        successorGV = getNextGV(&*gi, M);

        if (((&*gi)->getName()).startswith(prefix_of_hookGV_name)) {
            dbg(errs()<<"\tSKIP: Hook Global value.\n";)
            ; 
        }
        else if (((&*gi)->getName()).startswith("llvm.used")
                || (&*gi)->getName().startswith("switch.table")) {
            /// skip llvm-generated global variables. /////
            dbg(errs()<<"SKIP: \tllvm.used \n";)
                ; 
        }
        else if ( isPrintfStr(&*gi)) {
            dbg(errs()<<"\tSKIP: (printf str).\n";)
            ; 
        }
        else if (hasConstructorAttribute(&*gi) 
                || hasDestructorAttribute(&*gi)) {
            dbg(errs()<<"\tSKIP: (ctor/dtor attr).\n";)
            ; 
        }
        else if (!isToBeTaggedType ((&*gi)->getValueType())){
            dbg(errs()<<"\tSKIP: non-aggregated type or non-pointer.\n";)
                ; 
        }
        else if (((&*gi)->getName()).endswith("Perl_pp_gmtime.dayname")
            || ((&*gi)->getName()).endswith("Perl_pp_gmtime.monname")) {
            errs()<<"** skipping "<<(&*gi)->getName()<<"\n";
            // perlbench. time related string
            ; 
        }
#ifndef DISABLE_HOOK_GLOBAL_VARIABLE
        else {
            GlobalVariable* GVToBeRemoved= doGlobalVariable (&*gi, hook, insertBeforeMe, M, inits);
        } 
#endif
//endif of DISABLE_HOOK_GLOBAL_VARIABLE   
    }
    
    
    if (toBeRemovedList.size()>0) {
        for (vector<GlobalVariable*>::iterator ii=toBeRemovedList.begin();
            ii!= toBeRemovedList.end();++ii) {
                       
            dbg(errs()<<"GV TO BE REMOVED: "<<**ii<<"\n";)
            (*ii)->eraseFromParent();
        }
    }
    BasicBlock::iterator it= Func_main->begin()->end();
    it--;
    Instruction * lastins= &*it;

    setupGVInitializer(inits, lastins);  
}

void Framer::flagHooksDefinitionExists (Module &M)
{
    /* insert an entry (key: instruction number, value: exists/not exists) to the table. 
        Only instructions whose hook functions are provuded by users are processed at the iteration based on this table. */
    
    //TODO: insert  an entry to the table. unsigned int key: 0...2^8, bool hookexists.. ..(or just one int, and ...use POS, or SOP operation?) 
    size_t hookPrefixStrlen = StringRef(prefix_of_hookfunc_name).size();  
    
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
        if (((&*mi)->getName()).startswith(prefix_of_hookfunc_name)) {
            dbg(errs()<<"mi->getName():: "<<mi->getName()<<"\n";)
            StringRef instKindInStr = (mi->getName()).drop_front(hookPrefixStrlen);
            
            dbg(errs()<<"\tHook Prefix Name: "<<instKindInStr<<"\n";)
            
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
            else if (instKindInStr.equals("addop"))     
                {HookDefinitionExists[Instruction::Add]=1;}
            else if (instKindInStr.equals("subop"))     
                {HookDefinitionExists[Instruction::Sub]=1;}
            else if (instKindInStr.equals("mulop"))     
                {HookDefinitionExists[Instruction::Mul]=1;}
            
            else if (instKindInStr.equals("udiv"))      
                {HookDefinitionExists[Instruction::UDiv]=1;}
            else if (instKindInStr.equals("sdiv"))      
                {HookDefinitionExists[Instruction::SDiv]=1;}
            else if (instKindInStr.equals("lshr"))      
                {HookDefinitionExists[Instruction::LShr]=1;}
            else { 
                dbg(errs()<<"\tno hook provided!! Skipping..\n";)
            } 
        }
    }
}

void Framer::create1stBBOfMain (Module &M)
{
   fstBBOfMainFunction->splitBasicBlock(&*fstBBOfMainFunction->begin(), "fstBBOfMain");
}

void 
Framer::doInitFuncHook (Module & M)
{
    Function * F= 
        M.getFunction("FRAMER_do_initializing");
    assert (F!= nullptr 
            && "FRAMER_do_initializing empty!\n");

    Instruction* insertBeforeMe= &*(Func_main->begin()->begin());
    
    errs()<<"type1: "<<*StructTyTable->getType()<<"\n";

    vector<Value *> arglist;

    Value * numStructTy= 
            constructValueFromFunc (structTyCount, F, 0);
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(0), 
                   numStructTy, arglist,M);
  
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(1), 
                   StructTyTable, arglist, M);


#ifdef ENABLE_SPACEMIU 
 
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(2), 
                   rtOffsetTbl, arglist, M);
    
    Value * consttotalofs= 
            constructValueFromFunc(totaloffsetcount, F, 3);  
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(3), 
                   consttotalofs, arglist, M);
    
    Value * constmaxtysperoff= 
            constructValueFromFunc(maxtysperoff, F, 4); 
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(4), 
                   constmaxtysperoff, arglist, M);
    
    Value * constmaxoffsetval= 
            constructValueFromFunc(maxoffsetval, F, 5); 
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(5), 
                   constmaxoffsetval, arglist, M);
    
    Value * consttblentrysize= 
            constructValueFromFunc(tblentrysize, F, 6); 
    pushtoarglist (insertBeforeMe, 
                   F->getFunctionType()->getParamType(6), 
                   consttblentrysize, arglist, M);
    pushtoarglist (insertBeforeMe,
                   F->getFunctionType()->getParamType(7),
                   SafecastTable, arglist, M);

#endif

    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    // before any insertion of new insts, replace all uses.
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
    errs()<<"\n Done with doInitFuncHook\n"; 
}
    
/*
void Framer::assertBasicTyTable(Module &M)
{
    //assert((TypeKind::LLVMVectorTypeKind+1)==llvmbasicTyCount && 
    errs()<<"FixedVectorTyID: "<<Type::FixedVectorTyID<<", llvmbasicTyCount: "<<llvmbasicTyCount<<"\n";
    assert((Type::FixedVectorTyID+1)==llvmbasicTyCount && 
    "llvm's typeID enum has been updated?? check the count of enum, typeid\n"); 
}

void Framer::createUserStructTyList (Module &M)
{
    /// collecting only identified struct types. // 
    /// Opaque types are added on the fly. // 
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    for(vector<StructType*>::iterator it = temp.begin(), ie=temp.end();it!=ie;++it)
    {
        // when two struct types have the same physical layout, 
        // llvm deletes others, and keeps one alive. 
        //so should keep all identified struct types,
        // since Framer types may be the chosen ones.
        if ((*it)->isOpaque()) {
            errs()<<"opaque. skipping: "<<**it<<"\n";
            continue;
        }


    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    // before any insertion of new insts, replace all uses.
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
}
    
void Framer::assertBasicTyTable(Module &M)
{
    assert((Type::LLVMVectorTypeKind+1)==llvmbasicTyCount && 
    "llvm's typeID enum has been updated?? check the count of enum, typeid\n"); 
}

void Framer::createUserStructTyList (Module &M)
{
    /// collecting only identified struct types. // 
    /// Opaque types are added on the fly. // 
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    for(vector<StructType*>::iterator it = temp.begin(), ie=temp.end();it!=ie;++it)
    {
        // when two struct types have the same physical layout, 
        // llvm deletes others, and keeps one alive. 
        //so should keep all identified struct types,
        // since Framer types may be the chosen ones.
        if ((*it)->isOpaque()) {
            errs()<<"opaque. skipping: "<<**it<<"\n";
            continue;
        }


    CallInst * CI = CallInst::Create (F, arglist, ""); // hook func callinst created.
    // before any insertion of new insts, replace all uses.
    insertCastInstForArg (insertBeforeMe, arglist);
    CI->insertBefore (insertBeforeMe); //then hook callinst inserted.
}
void Framer::assertBasicTyTable(Module &M)
{
    assert((Type::LLVMVectorTypeKind+1)==llvmbasicTyCount && 
    "llvm's typeID enum has been updated?? check the count of enum, typeid\n"); 
}
*/ 

void Framer::createUserStructTyList (Module &M)
{
    /// collecting only identified struct types. // 
    /// Opaque types are added on the fly. // 
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    for(vector<StructType*>::iterator it = temp.begin(), ie=temp.end();it!=ie;++it)
    {
        // when two struct types have the same physical layout, 
        // llvm deletes others, and keeps one alive. 
        //so should keep all identified struct types,
        // since Framer types may be the chosen ones.
        if ((*it)->isOpaque()) {
            errs()<<"opaque. skipping: "<<**it<<"\n";
            continue;
        }
        allStructTyList.push_back(*it); //create constant. then push?
        dbg(errs()<<"structlist name: "<<(*it)->getStructName()<<"\n";)
    }
    structTyCount = allStructTyList.size(); 
    //contains only used one. includes substruct, struct.  
}

unsigned Framer::getMaxFieldCountOfStruct()
{
    unsigned maxcount=0;
    for (vector<StructType*>::iterator it=allStructTyList.begin(),
            ie=allStructTyList.end();it!=ie;++it) {
        unsigned count = (*it)->getNumElements();
        if (count > maxcount) {
            if (maxcount >100) {
                maxcount100temp++;
                continue; 
            }
            maxcount = count;
        }
    }
    dbg(errs()<<"final max count:: "<<maxcount<<"\n";) 
    return maxcount; 
}

void Framer::createStructTypeTable(Module &M) 
{
    unsigned max_field_count= getMaxFieldCountOfStruct();
    errs()<<"max field count: "<<max_field_count<<"\n";

    Type* structsizeT=  IntegerType::getInt32Ty (M.getContext()); 
    ArrayType* FieldsArrayT=  ArrayType::get(IntegerType::get(M.getContext(),32), max_field_count);
    vector<Type*> onestructTylsit= {structsizeT, FieldsArrayT}; 
    StructType* oneStructT = StructType::create(
        M.getContext(), onestructTylsit, StringRef("FRAMER_oneStryctTy")); 
    
    vector<Constant*> StructTypeVector;
    
    for (vector<StructType*>::iterator it=allStructTyList.begin(), 
            ie=allStructTyList.end();it!=ie;++it) {
        if ((*it)->isOpaque()) {
            errs()<<"Opaque found in struct type list:\n\t"<<**it<<"\n";
            exit(0);
        }
        unsigned structsize= 0; 
        int framertyid= -1;
        Constant * fieldconst; 
        vector<Constant*> fields;
      
        structsize = (unsigned)(dlayout->getTypeSizeInBits(*it)); 
        dbg(errs()<<"Non-opaque. structsize: "<<structsize<<"\n";)

        StructType::element_iterator elemit = (*it)->element_begin(); 

        for(unsigned i=0 ; i< max_field_count ; i++) {  
            if(i >= (*it)->getNumElements()) {
                framertyid=-1; 
            }
            else {
                framertyid= (int)getFramerTypeID(*elemit);   
            }
            fieldconst = ConstantInt::get(IntegerType::get(M.getContext(), 32),(unsigned)framertyid); 
            fields.push_back(fieldconst);
            assert(fields.size() <= max_field_count && "fields vector pushing wrong!\n");
            elemit++;
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
        dbg(errs()<<"Struct info inserted: "<<*onestructconst<<"\n";) 
    }
    ArrayType* StructsT=    ArrayType::get(oneStructT, StructTypeVector.size());
    Constant* structTableArray = ConstantArray::get(StructsT, StructTypeVector);
     
    errs()<<"structTAbleArray crected\n";
     
    StructTyTable = new GlobalVariable (M, 
                                        StructsT, //StructTyArr, 
                                        true, 
                                        GlobalValue::ExternalLinkage,
                                        structTableArray,//nullStructTbl,
                                        "FRAMER_StructTyTable");
}

void Framer::doInitialSetup (Module &M)
{
    errs()<<"itializing starting..\n";
    dlayout = &(M.getDataLayout());
   
    Func_main= M.getFunction ("main");
    assert (Func_main && "main empty!!\n");
    
    fstBBOfMainFunction     = &*Func_main->begin();
    fstInstOfMainFunction   = &*((Func_main->begin())->begin());
    
    assert (fstInstOfMainFunction && "fstInstOfMainFunction empty!\n"); 

    // catching header type.
    
    vector <StructType*> temp= M.getIdentifiedStructTypes();
    for(vector<StructType*>::iterator it= temp.begin(); it!=temp.end(); ++it)
    {
        if ((*it)->getName().startswith("struct.FRAMER_Headers")) {
           HeaderTy= *it;
           break;  
        }
    }
    //%struct.FRAMER_Headers.1 = type { i32, i32, i32, i16, i16 }
    //HeaderTy= M.getTypeByName(StringRef("struct.FRAMER_Headers"));

    assert(HeaderTy && "Check if FRAMER_Headers is re-named or ever used.\n");
    OffByOneTy= Type::getInt8Ty (M.getContext());
    

    const StructLayout * headerTyLayout= 
            dlayout->getStructLayout (HeaderTy);
    headerTySize= headerTyLayout->getSizeInBytes (); 
    errs()<<"headerTySize: "<<headerTySize<<"\n";
    headerTyAlign= (unsigned)(headerTyLayout->getAlignment()).value();
    
    assert (headerTySize==16 
            && "check headerTy size.\n"); 
    assert (!headerTyLayout->hasPadding() 
            && "type must be packed!!\n"); 

    //assertBasicTyTable(M); 
    dbg(errs()<<"assertedBasictypetable done \n";)
    
    createUserStructTyList(M);

    dbg(errs()<<"createUserStructTyList done \n";)

  #ifdef ENABLE_SPACEMIU

    /* currently, opaque and packed structures not included. */
    
    createAllTypeList(AllTypeList, M);
    
    /* One extra type added (compatible-with-all-types) - 
    a heap object allocated by a custom wrapper with no effective type */
    
     
    errs()<<">>>used type size: "<<AllTypeList.size()<<"\n"; 
  
    errs()<<">>> start or type tables........\n";
    
    createTypeTables (AllTypeList, SafeCasts, 
                      DownCasts, tyoffsets, 
                      flatrtoffsets, //just one tid at one offset. 
                      MaxOffset,
                      M);
    
    maxoffsetval= getMaxCount_offsets (tyoffsets
                                 ,maxoffsperty 
                                 ,totaloffsetcount 
                                 ,maxtysperoff
                                 );
    errs()<<"1. MaxOffset: "<<MaxOffset<<"\n";
    errs()<<"2. flatrtoffsets 0's size: "<<(flatrtoffsets.at(0)).size()<<"\n";
    setUpSomeRTTypes (SafeTidsTy,
                      oneOffsetTy,
                      maxtysperoff,
                      maxoffsperty,
                      tyoffsets.size(),
                      tblentrysize,
                      M);
   
    max_upcasts= getMaxCount (SafeCasts);
    assert(max_upcasts != 0);

    errs()<<"#All types:\t"<<AllTypeList.size()<<"\n";
    errs()<<"MaxOffset:\t"<<MaxOffset<<"\n";
    errs()<<"max_upcasts:\t"<<max_upcasts<<"\n";

    errs()<<">>> end or type tables........ \n";
  
  #endif   // endif of ENABLE_SPACEMIU
    
    flagHooksDefinitionExists(M);
    dbg(errs()<<"flagHooksDefinitionExists done \n";)
    
    create1stBBOfMain (M); // BB processing global vars.
    dbg(errs()<<"create1stBBOfMain done \n";)
    
}



bool 
Framer::runOnBasicBlock (BasicBlock &BB, 
                         DominatorTree & dt, 
                         AAResults & AA,
                       #ifdef ENABLE_SPACEMIU
                         vector <AllocaInst*> & LocalUnions,
                       #endif
                         CallGraph & CG,
                         Module &M)
{
    /* successorInst is introduced to store the original next instruction 
         distinguished from insts added by the pass. */ 
    Instruction * successorInst = &*BB.begin();
    vector<Instruction*> toBeRemovedList; 
    for (BasicBlock::iterator it = BB.begin(), ie = BB.end();it != ie; ++it) {
       
        dbg(errs()<<"\nInst:::\t"<<*it<<"\n";)
        
        if (&*it != &*successorInst) {
  
            dbg(errs()<<"\tadded by hook? skipping..\n";) 
            continue;
        }
        successorInst = getNextInst(&*it);
        
        ////// skip hooking instructions for GV bounds check.
        set<Instruction*>::iterator findit= 
            FramerLoads.find(&*it); 
        
        if (findit!=FramerLoads.end()) {
            continue; 
        }
        
        //// upto here
         
        if (AllocaInst * AI = dyn_cast<AllocaInst>(it) ){
    
    #ifndef DISABLE_HOOK_ALLOCA
            if (!HookDefinitionExists[Instruction::Alloca]) {
                dbg(errs()<<"No hooks provided for alloca inst. Skipping..1\n";) 
                continue;
            }
            Instruction* toBeRemoved= doAllocaInst (AI, 
                            successorInst, 
                          #ifdef ENABLE_SPACEMIU
                            LocalUnions, 
                          #endif
                            M);
          
            
            if (toBeRemoved!= 0x0) { 
              
             
                toBeRemovedList.push_back(toBeRemoved);
            }
    #endif /* end of DISABLE_HOOK_ALLOCA */

        }

#ifndef DISABLE_INSTRUMENT_STORE_LOAD

        else if (LoadInst * LI = dyn_cast<LoadInst>(it) ) {
          /*  TODO: this is an optimization.. let it be in userhook.c
            if (PointersAreTagged) {
                restoreModifiedPtr (LI);
            }
          */ 
            if (!HookDefinitionExists[Instruction::Load]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";) 
                continue;
            }
            if (IntegerType * intty= dyn_cast<IntegerType>(LI->getType())) {
                if (intty->getBitWidth()==1) {
                    dbg(errs()<<"SKIP: Valop's type is int, and size is 1.\n";)
                    continue;    
                }
            }
            if (isSafePtr(LI->getPointerOperand())) {
                dbg(errs()<<"skip. safeptr: "<<*LI->getPointerOperand()<<"\n";)
                safeptr++;
                continue;
            }
    #ifdef SKIP_NON_TAGGED 
            if (isNonTagged(LI, AA, M)) {
                safeptr++;
                continue;    
            }
    #endif
          #ifdef ENABLE_SPACEMIU

            doLoadInstForSpaceMiu (LI, successorInst, dt, 
                                   AA, LocalUnions, M);
          #else  

            doLoadInst (LI, successorInst, dt, AA, M);

          #endif
        }
        else if (StoreInst * SI = dyn_cast<StoreInst>(it) ) {
            if (!HookDefinitionExists[Instruction::Store]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            }
            if (IntegerType * intty= dyn_cast<IntegerType>(SI->getValueOperand()->getType())) {
                if (intty->getBitWidth()==1) {
                    dbg(errs()<<"SKIP: Valop's type is int, and size is 1.\n";)
                    continue;    
                }
            }
            if (isSafePtr(SI->getPointerOperand())) {
                safeptr++;
                continue;
            }
    #ifdef SKIP_NON_TAGGED 
          
            if (isNonTagged(LI, AA, M)) {
                safeptr++;
                continue;
            }
    #endif
            // for Store, this skipping test goes inside doStore. since we might tag referencing??
            
          #ifdef ENABLE_SPACEMIU 
           
            doStoreInstForSpaceMiu (SI, successorInst, dt, 
                                   AA, LocalUnions, M);
          #else
         
            doStoreInst (SI, successorInst, dt, M);
          
          #endif
        }

#endif  // end of DISABLE_INSTRUMENT_STORE_LOAD
           
    #ifndef DISABLE_CHECKS_AT_GEP
      
        else if (GetElementPtrInst * GEP = dyn_cast<GetElementPtrInst>(it)) {
            dbg(errs()<<"entering GEP..?\n";)
            if (!HookDefinitionExists[Instruction::GetElementPtr]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..4\n";)
                continue;
            }
            unsigned issafeaccess=isSafeAccess(GEP, M, 0, paddedGVs);
            if (issafeaccess==SAFESTATICALLY) {
                tempgepsafe++;
                continue; 
            }
            doGetElementPtrInst (GEP, successorInst, M);
        }

    #endif

        else if (CallInst * CI = dyn_cast<CallInst>(it)) {
            if (!HookDefinitionExists[Instruction::Call]) {
                dbg(errs()<<"No hooks provided for Call (llvm.memcpy) inst. Skipping..\n";) 
                continue;
            }
            
            Instruction * toBeRemoved= 
                doCallInst (CI, successorInst, AA, dt, CG, 
                          #ifdef ENABLE_SPACEMIU
                            LocalUnions, 
                          #endif
                            M);
            
            if (toBeRemoved!= 0x0) { 
                toBeRemovedList.push_back(toBeRemoved);
            }
        }
      #ifdef ENABLE_SPACEMIU

        else if (BitCastInst * BCI = dyn_cast<BitCastInst>(it)){
            if (!HookDefinitionExists[Instruction::BitCast]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            }
            if (isSafePtr(BCI->getOperand(0))) {
                //errs()<<"skip. SPACEMIU: safeptr: "<<*BCI->getOperand(0)<<"\n";
                safeptr++;
                continue;
            }
            if (isCastWeDoNOTHandle(BCI, dt)) {
                continue;
            }

            doBitCastInst (BCI, successorInst, AA, LocalUnions, M);        
        }
      #endif
      
        /*
        else if (PtrToIntInst * PTI = dyn_cast<PtrToIntInst>(it)) {
            if (!HookDefinitionExists[Instruction::PtrToInt]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            }
            doPtrToIntInst (PTI, successorInst, M);
        }
        else if (IntToPtrInst * ITP = dyn_cast<IntToPtrInst>(it)) {
            doIntToPtrInst (ITP, successorInst, M);
        }
        else if (SIToFPInst * STF = dyn_cast<SIToFPInst>(it)) {
               if (!HookDefinitionExists[Instruction::SIToFP]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            }
            
            doSIToFPInst (STF, successorInst, M);
        }
        else if (FPToSIInst * STF = dyn_cast<FPToSIInst>(it)) {
            if (!HookDefinitionExists[Instruction::FPToSI]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            }
            
            doFPToSIInst (STF, successorInst, M);
        }
        
        else if (TruncInst * TR = dyn_cast<TruncInst>(it)) {
            if (!HookDefinitionExists[Instruction::Trunc]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            } 
            
            doTruncInst (TR, successorInst, M);
        }
        else if (SExtInst * SI = dyn_cast<SExtInst>(it)) {
            if (!HookDefinitionExists[Instruction::SExt]) {
                dbg(errs()<<"No hooks provided for this inst. Skipping..\n";)
                continue;
            } 
            doSExtInst (SI, successorInst, M);
        }
        */
        
        /*
        else if (BinaryOperator * BO = dyn_cast<BinaryOperator>(it)) {
                doBinaryOp (BO, successorInst, M);
        }*/
        /*else if (PossiblyExactOperator * PEO = dyn_cast<PossiblyExactOperator>(it)) {
            doPossiblyExactOp (PEO, successorInst, M);
        }*/
        else {
            //TODO: add other cases such as cast.
            ;
        }

    }
    // remove existing instruction (such as x=call malloc(n)..) 
    dbg(errs()<<"to be removed size: "<<toBeRemovedList.size()<<"\n"; )
    if (toBeRemovedList.size()>0) {
        for (vector<Instruction*>::iterator ii=toBeRemovedList.begin(), ie= toBeRemovedList.end();
            ii!=ie; ++ii) {
            dbg(errs()<<"TO BE REMOVED: "<<**ii<<"\n";) 
            (*ii)->eraseFromParent();
        } 
    }

  dbg(
   // errs()<<"sssss\n";
   // for (BasicBlock::iterator it = BB.begin(), ie = BB.end();it != ie; ++it) {
   //     errs()<<"ins: "<<*it<<"\n";        
   // }
   // errs()<<"eeeee\n";
  )
    return true;
}
/*
bool Framer::isLeafOfDomTree (BasicBlock* bb, PostDominatorTree & postDT)
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
*/
void Framer::insertEpilogueOfFunc (Instruction* tagged, 
                                        Module &M)//, 
                                        //PostDominatorTree & postDT)
{
    dbg(errs()<<"Epilog:: "<<*tagged<<"\n";)

    vector <Value*> arglist= {tagged};

    Function* F= tagged->getFunction(); 
    BasicBlock* allocaBB= tagged->getParent();
    Function::iterator mainit= Func_main->begin(); 
    advance(mainit, 1);
   // CallInst * CI = CallInst::Create(
   //     M.getFunction ("FRAMER_reset_entries_for_alloca"), 
   //                         arglist, 
   //                         "");

    if (allocaBB== &(F->front()) && F!=Func_main) { //skip main. since we will unmap anyway..
        Instruction * scopeEnd= scopeIsFunc(tagged);
        if (scopeEnd==nullptr) {
            for (Function::iterator bi=F->begin(),be=F->end(); bi!=be;++bi) { // for BB
                Instruction * TI= (&*bi)->getTerminator();
                assert(TI!=nullptr && "TerminatorInst is null.\n");

                if (isa<ReturnInst>(TI)) {
                  CallInst * CI = CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), arglist, "");
                    CI->insertBefore(TI);
                    continue;
                }
                else if (isa<UnreachableInst>(TI)) {
                  CallInst * CI= CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), arglist, "");
                    CI->insertBefore(TI);
                    continue;
                }
            }
        }
        else {
            CallInst * CI = CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), arglist, "");
            CI->insertBefore(scopeEnd);          
        }
    }
    else {
        CallInst * CI= CallInst::Create(M.getFunction ("FRAMER_reset_entries_for_alloca"), 
                                    arglist, 
                                    "");

        Value* scopeStart=nullptr; //call llvm.stacksave
        Value* mySavedStack= nullptr; 
        Instruction * insertBeforeMe=nullptr;

        // get scopestart 
        unsigned stackSaveCount=0;
        for (BasicBlock::iterator it= allocaBB->begin(), ie=allocaBB->end(); it!=ie; ++it) {
            if (CallInst * ci= dyn_cast<CallInst>(&*it)) {
                if (ci->getCalledFunction()->getName().startswith("llvm.stacksave")) {
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
                        if (ci->getCalledFunction()->getName().startswith("FRAMER_forall_store")) {
                            mySavedStack= (ci->getArgOperand(0))->stripPointerCasts();           
                        }
                        else {errs()<<"??? not hook familly?\n"; exit(0); }
                    }
                    else { errs()<<"what case is this in epilogue?\n"; exit(0);} 
                }
            }
            else {;}
        }
        if (!(stackSaveCount==1 && scopeStart !=nullptr && mySavedStack != nullptr)) {
            dbg(errs()<<"** alloca not in entry BB, nor having llvm.lifetime\n";
            errs()<<"   in the function: "<<tagged->getFunction()->getName()<<"\n";)

            //// this case, I assume alloca is consumed only in the BB. 
            ///  so inserting epilog at the end of the BB.
            BasicBlock::iterator lInst= allocaBB->end();
            lInst--;
            dbg(errs()<<"   back inst: "<<*lInst<<"\n";)

            CI->insertBefore(&*lInst);
            return;
        }
        dbg(errs()<<"got scopstart\n";)
        // get scope_end
        for (Function::iterator it=F->begin(), ie= F->end(); it!=ie; ++it) {
            unsigned stackrestorecount=0;
            for (BasicBlock::iterator bit= (&*it)->begin(), bie=(&*it)->end(); bit!=bie; ++bit) {
                dbg(errs()<<"bit: "<<*bit<<"\n";)
                if (!isa<CallInst>(&*bit)) {
                    continue; 
                }
                CallInst * restore=cast<CallInst>(&*bit);     
                if (!(restore->getCalledFunction()->getName()).startswith("llvm.stackrestore")){ 
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
                    if (ci->getCalledFunction()->getName().startswith("FRAMER_forall_load")
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
}

/*
void Framer::insertEpilogueOfFunc (AllocaInst* tagged, Module &M, DominatorTree & FDomTree)
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

void Framer::doExitingMain (Module &M)
{
    vector <Value*> arglist;
    Function * exitmain= M.getFunction ("FRAMER_exit_main");
    assert(exitmain!=nullptr && "FRAMER_exit_main empty!\n"); 
    
    for (Function::iterator bi=Func_main->begin(),
            be=Func_main->end(); bi!=be;++bi) { // for BB
        
        Instruction * TI= (&*bi)->getTerminator();
        assert(TI!=nullptr && "TerminatorInst is null.\n");
        
        if (isa<ReturnInst>(TI)) {
            CallInst * CI= CallInst::Create(M.getFunction ("FRAMER_exit_main"), 
                    arglist, 
                    "");
            CI->insertBefore(TI);
            continue;
        }
        else if (isa<UnreachableInst>(TI)) {
            BasicBlock::iterator it (TI);
            assert (it!=(&*bi)->end() && "cannot find TI\n");
            it--;
            assert(isa<CallInst>(&*it) && "not call exit? what case is this?\n");
            CallInst * CI= CallInst::Create(M.getFunction ("FRAMER_exit_main"), 
                    arglist, 
                    "");
            CI->insertBefore(&*it);
            continue;
        }
    }
}

bool 
Framer::runOnFunction (Function &F, 
                       Module &M, 
                       CallGraph & CG)
{

/////// printing inst
  dbg(        
    if (F.getName().startswith("Perl_leave_scope") ||
            F.getName().startswith("xmalloc") ||
            F.getName().startswith("xrealloc")
            ) { 
            errs()<<"=== original ================================0\n";
            errs()<<F<<"\n";
            errs()<<"===================================1\n";
    }
  )
///////// 


    dbg(errs()<<"now running on Function:  "<<F.getName()<<" processing...\n";)
       
    DominatorTree &dt= getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
    AAResults & aaresult= getAnalysis<AAResultsWrapperPass>(F).getAAResults();

   
  /* Used only for SpaceMiu */
  #ifdef ENABLE_SPACEMIU
    vector <AllocaInst*> LocalUnions; 
  #endif  
  
  /* end of SPACEMIU */

    for (Function::iterator fi = F.begin(), 
            fe = F.end(); fi!=fe ; ++fi ){
        
        if (&*fi == &*Func_main->begin() 
            && (F.getName() == "main")) {
            //skip // since it is basicblock for global variable processing hooks.     
            continue; 
        }
       
        Framer::runOnBasicBlock (*fi, 
                dt, 
                aaresult, 
              #ifdef ENABLE_SPACEMIU  
                LocalUnions, 
              #endif
                CG,
              //  F,
                M);//, postDT); 

    }
    dbg(errs()<<"after func iteration\n";)
   
    //setupScopeOfLocals (F, M); 
    
    if (F.getName().equals("main")) {
        doExitingMain(M);
    }
    dbg(errs()<<"after do exiting main\n";)

/////// printing inst
  dbg(
    if (F.getName().startswith("Perl_leave_scope")// ||
  //      F.getName().startswith("xmalloc") ||
  //      F.getName().startswith("xrealloc")
        ) { 
        errs()<<"===modified ================================0\n";
        errs()<<F<<"\n";
        errs()<<"===================================1\n";
    }
  )
///////// 
    return true;
}

bool Framer::runOnModule (Module &M) 
{
    framerpasscounter++;


    if (!M.getFunction("main") || M.getIdentifiedStructTypes().size()==0) {
        return true;
    }

    doInitialSetup (M);

    runOnGlobalVariables(M); 
    
    CallGraph & CG= getAnalysis<CallGraphWrapperPass>().getCallGraph();
     
  #ifdef ENABLE_SPACEMIU
 
    createGVUnionsList(M, GVUnions);    
 
  #endif


    errs()<<"Starting run on functions..\n"; 
    /// processing each instruction for each BB for each function
    
    for (Module::iterator mi=M.begin(), me=M.end(); mi!=me ; ++mi) {
        dbg(errs()<<"Function::  "<<mi->getName()<<"\t"; )
        
        if (isHookFamilyFunction (&*mi)) {
            dbg(errs()<<"\t::Hook.Skipping..\n";)
            continue;
        }
        if ((&*mi)->isDeclaration()) {
            dbg(errs()<<"\t::decl.skipping..\n";) 
            continue; 
        }

        runOnFunction(*mi, M, CG);
    }

    errs()<<"\nAfter run on all function. now createStructTypeTable starting..\n";

    createStructTypeTable(M);

    errs()<<">> createStructTypeTable done \n";
  
    // * create runtime safecast table. *
   
    // TODO: now we inserted safecasts to tyoffsets, so this is redundant??
    // so commmented out.

////////////////////////////////////////////////////////////    
#ifdef ENABLE_SPACEMIU     

    max_upcasts= getMaxCount (SafeCasts);
    assert(max_upcasts != 0);
     
    createRTSafeCastsTable (SafeCasts, 
                            SafecastTable, 
                            max_upcasts, 
                            M); 

    // TODO: optimized RT type tables. 
    // for example, framers' types that are not used outside hooks.
    // mind that LLVM merges same structure types, and framer's types can be chosen. 

    errs()<<"1. MaxOffset::: "<<MaxOffset<<"\n";
    createRTOffsetTable (AllTypeList, 
                         flatrtoffsets,
                         MaxOffset,
                         rtOffsetTbl, 
                         M);
    
    assert(rtOffsetTbl!=nullptr);
    
#endif 
     
    doInitFuncHook(M);
    
    errs()<<"GV counts: "<<tempGVcount<<"\n";
    errs()<<"tempload: "<<tempload<<"\n";
    errs()<<"temploadsafe: "<<temploadsafe<<"\n";
    errs()<<"tempstore: "<<tempstore<<"\n";
    errs()<<"tempstoresafe: "<<tempstoresafe<<"\n";
    errs()<<"tempgepsafe: "<<tempgepsafe<<"\n";
    errs()<<"safeptr: "<<safeptr<<"\n";
    errs()<<">>>>>>>>>>>leaving Framer........\n\n"; 

    return true;

    
}


