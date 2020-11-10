#ifdef __cplusplus
extern "C" {
#endif

//#include "./hooks.h"
#include "./framertypes.h"
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <stddef.h>
#include <errno.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <unistd.h>
#include <fcntl.h>
#include <math.h>
#include <string.h>
#include <assert.h>
//#include <stdbool.h>
#include <signal.h>
//#include <smmintrin.h>

#ifndef USERSHOOK_H_
#define USERSHOOK_H_

//////////
/// re-define bool since LLVM src code has conflicts with bool in stdbool.h




///////////////////////////////////
#undef ENABLE_INTERPOSE_MALLOC_FAMILY


//#define DEBUG
#ifdef DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif

//#define ASSERT_DEBUG
#ifdef ASSERT_DEBUG
#  define assert_dbg(x) x
#else
#  define assert_dbg(x) 
#endif


//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

//#define inlining hooks in the loop (check Framer's loopopt pass)
#define FULL_INLINING

//#define STORE_ONLY_CHECK

#define DISABLE_CHECKS_AT_GEP


// better enable above all the time..otherwise 
//function body of hooks are optimized away..:(


// for bitcast, planning to skip tracking arrays
// for some experiments. (like typesan)
////////////////////////////////////////

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// disabling operation done at _alloca.
//  skipping tagging and updating metadata. (so all ptrs are untagged) 
//
//#define DISABLE_GLOBAL_METADATA_UPDATE
//#define DISABLE_ALLOCA_METADATA_UPDATE

//#define DISABLE_CHECK_BOUNDS

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//#define DISABLE_HEAP_METADATA_UPDATE //--> is this used?

dbg(
extern unsigned FRAMER_tempGVcount;
extern unsigned FRAMER_tempstorecount;
extern unsigned FRAMER_temploadcount;
//extern unsigned FRAMER_tempbitcastcount;

extern unsigned FRAMER_Ntempload   ;
extern unsigned FRAMER_Ntempstore  ;
extern unsigned FRAMER_Ntempmem    ;
extern unsigned FRAMER_Ntempset     ;
extern unsigned FRAMER_Ntempstrncat ;
extern unsigned FRAMER_Ntempstrcpy  ;
extern unsigned FRAMER_Ntempstrcmp  ;
extern unsigned FRAMER_Ntempstrncpy ;
extern unsigned FRAMER_Ntempmemcmp  ;
extern unsigned FRAMER_Ntempmemchr  ;
)

//extern int FRAMER_BasicTy_table [22]; 

/* for Type table */
extern unsigned         FRAMER_structTy_count; 
extern StructEntryT*    FRAMER_baseOfStructTable;

extern FRAMER_Bool_*  FRAMER_baseOfSafeCastTable;
extern unsigned         FRAMER_safecast_col_num;
extern unsigned         FRAMER_safecast_row_num;

// old one upto here.
extern char * FRAMER_baseOf_OffsetTable;
extern short FRAMER_total_offset_count;  // on SpaceMiu's version 2, this is dummy.
extern short FRAMER_max_ty_count_per_off;
extern short FRAMER_max_offset_val;

/* for Metadata table */
extern int FRAMER_fd;
extern int errno;

extern uintptr_t FRAMER_metatable_count;

extern uintptr_t FRAMER_metadata_file_size;

/* TABLES */
// HERE, StructTy ARRAY is inserted by llvm! 

extern HeaderT* FRAMER_PointerTy_Table; 

/// error! at laos
//#ifdef ENABLE_SPACEMIU
//  extern EntryT* FRAMER_TABLE;
//#else
  extern SlotT* FRAMER_TABLE;
//#endif
// laos upto here

//TYPE HASH TABLE
//extern GHashTable *hash;

// to resolve problem!!
extern char **environ ; 

#ifdef COUNT_BIG_SMALL_OBJECTS
  extern unsigned FRAMER_BIG_FRAMED_OBJECT_COUNT;
  extern unsigned FRAMER_SMALL_FRAMED_OBJECT_COUNT;
#endif

__attribute__((__used__))
__attribute__((always_inline))
static void FRAMER_supplementary_exit()
{
//    printf("Out-of-bounds. Exiting\n");
#ifndef MEASURE_RUNTIME
    exit(0);
#else
    asm("nop");
#endif
}

__attribute__((__used__))
//__attribute__((always_inline))
static unsigned 
FRAMER_decide_log_framesize (void * p, 
                             unsigned objsize)
{
    /// framesize only for stack and heap, that are not padded by one byte///
    /// (globals are padded by one byte unlike stack/heap obj) ///

    assert_dbg(assert( (((uintptr_t)p <= FRAMER_end_addr_userspace) 
            && ((uintptr_t)(p + (objsize-1))) < FRAMER_end_addr_userspace)
            && "object is out of bound of FRAMER_end_addr_userspace!\n");)

    assert( ((uintptr_t)p <= FRAMER_end_addr_userspace) 
            && ((uintptr_t)((char*)p + (objsize-1))) < FRAMER_end_addr_userspace);

    uintptr_t xor_result= ((uintptr_t)p) ^ ((uintptr_t)((char*)p+objsize));
    int myclzl = __builtin_clzl ((unsigned long)xor_result); //TODO: safe cast? 
    unsigned N = (unsigned)(64 - myclzl);

#ifdef COUNT_BIG_SMALL_OBJECTS
    if (N <= FRAMER_log_slotsize) { //FRAMER_log_slotsize == 15
        FRAMER_SMALL_FRAMED_OBJECT_COUNT++;
    }
    else {
        FRAMER_BIG_FRAMED_OBJECT_COUNT++;
    }
#endif    

    return N; 
}
/*
__attribute__((__used__))
//__attribute__((always_inline))
static FRAMER_Bool_ FRAMER_supplementary_isStructTy (unsigned id)
{
    FRAMER_Bool_ is_struct;
    if (id >=FRAMER_total_BasicTyCount 
        && id < FRAMER_total_BasicTyCount+FRAMER_structTy_count ) {
        is_struct=true; 
    }
    else{
        is_struct=false;
    }
    return is_struct;
}*/

__attribute__((__used__))
//__attribute__((always_inline))
static FRAMER_Bool_ FRAMER_is_N_tagged (uintptr_t tag) //not TyIDtagged!
{
    /* add assertion that flag  must be 0.*/
    FRAMER_Bool_ isN= false;
    if((tag>>FRAMER_num_used_bits_in_ptr) < FRAMER_TyIDStart) {
        isN= true;
    }
    return isN;
}

#ifdef TYPECHECK
__attribute__((__used__))
static FRAMER_Bool_ 
FRAMER_is_N_tagged_2 (uintptr_t tag) //not TyIDtagged!
{
    /* add assertion that flag  must be 0.*/
    FRAMER_Bool_ isN= false;
    if(tag<FRAMER_TyIDStart) {
        isN= true;
    }
    return isN;
}
#endif

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t 
FRAMER_supplementary_get_table_index (uintptr_t slotbase) 
{
    uintptr_t shadow_index = 
        ((slotbase - FRAMER_slotbase_of_userspace_start)
        /(1ULL<<FRAMER_log_slottable_interval));
    return shadow_index; 
}

__attribute__((__used__))
//__attribute__((always_inline))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static FRAMER_Bool_ FRAMER_update_entry (
        EntryT* ptr, 
        void* padded_obj_base) 
{
    FRAMER_Bool_ entry_available= 1;
    EntryT m = *ptr;

//    if (m.base !=0) {
//        entry_available= 0;
//    }
//    else {
        ptr->base= (void*)padded_obj_base; //save the address of header now!
//    }
    
    return entry_available; 
}

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t 
FRAMER_supplementary_get_slotbase_from_untag (uintptr_t p, 
                                              unsigned N)//uintptr_t N) 
{
    //uintptr_t slotbase = p & ((~0)<<N);
    uintptr_t slotbase = (p >> N)<<N;
    assert_dbg(assert(N<64 && "check the result if correct..\n");)
    return slotbase;   
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else 
__attribute__((noinline))
#endif
static EntryT* 
FRAMER_get_entry_addr (uintptr_t p, 
                       unsigned N)
{ 
    //p:untagged ptr
   
    //starting from getting a slot base;
    uintptr_t slotbase= 
        FRAMER_supplementary_get_slotbase_from_untag (p, N);
    // get slot index. 
    uintptr_t shadow_index= 
        FRAMER_supplementary_get_table_index(slotbase); 
    //get a pointer 
 
 
   /* EntryT* M= FRAMER_TABLE + shadow_index*FRAMER_num_of_entries_per_slot; 
    EntryT* myentry= M+(N-FRAMER_log_slottable_interval); 
    
    dbg(printf("\tslot base:\t%p\n", 
        (void*)slotbase);)
    dbg(printf("\tM:\t%p, @entry:%p\nCHECK entry addr is correct!",
        M, myentry);)
    dbg(exit(0);) 
   */ 
   
    SlotT* M= FRAMER_TABLE + shadow_index; 
    EntryT* m= M->slotarray;
    EntryT* myentry= m+(N-FRAMER_log_slottable_interval); 
    
    dbg(printf("\tslot base:\t%p,\tsizeof(slotT):%lu\n", 
        (void*)slotbase, sizeof(SlotT)));
    dbg(printf("\tM:\t%p",M));
    dbg(printf("\tm:\t%p, @entry:%p\n",
        m,m+(N-FRAMER_log_slottable_interval)));
  
//////////////     


    return myentry; 
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER 
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static FRAMER_Bool_ 
FRAMER_update_table (void* padded_obj_base, 
                     unsigned N)
{
  /*dbg(    
    if(N<=15 && N>64){
        dbg(printf("Wrong N at updating table. fat_base: %p, N: %u\n", 
                    padded_obj_base,N);)
      #ifndef MEASURE_RUNTIME        
        exit(0);
      #else
        asm("nop");
      #endif
    }
  ) */   
    EntryT* m= FRAMER_get_entry_addr((uintptr_t)padded_obj_base, N);
    
    // getting a pointer to the entry up to here. 
    return FRAMER_update_entry (m, 
                                padded_obj_base); 
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER 
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void 
FRAMER_update_header (void* padded_obj_base, //untagged 
                      int FramerTypeID,
                      unsigned raw_object_size
       
                  #ifdef ENABLE_SPACEMIU

                    #ifdef ENABLE_TRACK_ARRAYS
                      ,unsigned numBytesPerElem
                    #endif

                      ,FRAMER_Bool_ isUnionTy
                  #endif
                      )
{
    assert(raw_object_size != 0);
    HeaderT * h =   (HeaderT*)padded_obj_base; 

    h->FramerTyID=  FramerTypeID;
    h->size =       raw_object_size;
  
#ifdef ENABLE_SPACEMIU
  
 #ifdef ENABLE_TRACK_ARRAYS
    h->elemsize= numBytesPerElem;
    printf("if FRAMER_forall_malloc is enabled, we don't need this. probably. Fix this if necessary.\n");
    exit(0);

 #endif

    h->isUnionTy= (short)isUnionTy;
  
#endif

    dbg(printf("\tupdate HEADER @:\t%p\n", h));
    dbg(printf("\tRAW_SIZE:\t%d\n",h->size));
    dbg(printf("\tFramerTyID:\t%d\n",h->FramerTyID));
}

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_cal_offset (void * p)
{
    return (((uintptr_t)p) & 0x7FFF);  
}

/* returns the base of RAW object (after header) */
__attribute__((__used__))
//__attribute__((always_inline))
static void* 
FRAMER_supplementary_tag_ptr (void * p, 
                              uintptr_t tag, 
                              FRAMER_Bool_ flag)
{
    uintptr_t flgvec;
    if (flag==FRAMER_is_bigframe) {
        flgvec=0; 
    }
    else{
        flgvec = ((uintptr_t)1)<<63;
    }
    uintptr_t tagvec = tag<<48; 
    uintptr_t taggedPtr = (flgvec | tagvec) | (uintptr_t)p; 
     
    /*printf("\tTagging..\n");
    printf("\torig:\t%p\n", p);
    printf("\tflag:\t%p\n", (void*)flgvec);
    printf("\ttag:\t%p\n", (void*)tagvec);
    printf("\ttagged_p:\t%p\n", (void*)taggedPtr);
*/
    return (void*)taggedPtr;
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static FRAMER_Bool_ FRAMER_supplementary_extract_flag (void* p)
{
    return ((uintptr_t)p)>>63; 
}

/*
__attribute__((__used__))
//__attribute__((always_inline))
static HeaderT* FRAMER_supplementary_retrieve_from_header(uintptr_t p, 
                                                    uintptr_t tagvec)
{
    // Actually.. not retrieve from header, but get header address
    uintptr_t slotbase= p & FRAMER_header_slot_base_mask; 
    
    uintptr_t offset= (tagvec & FRAMER_mask_only_flag_out)>>FRAMER_num_used_bits_in_ptr; 
    HeaderT* hd_p = (HeaderT*)(slotbase + offset);
     
    return hd_p;      
}
*/

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static HeaderT* 
FRAMER_cal_header_addr(uintptr_t p, 
                       unsigned offset) //tag shifted & flag out
{
    // Actually.. not retrieve from header, but get header address
//    uintptr_t slotbase= p & FRAMER_header_slot_base_mask; 
    uintptr_t slotbase= (p >> 15) << 15; 
    
    //uintptr_t offset= (tagvec & FRAMER_mask_only_flag_out)>>FRAMER_num_used_bits_in_ptr; 
    HeaderT* hd_p = (HeaderT*)(slotbase + offset);
     
    return hd_p;      
}

#ifndef ENABLE_SPACEMIU

//__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_empty_metadata_entry (uintptr_t untagged, 
                                         uintptr_t tagvec)
{
    //get corresponding slot base.
    assert_dbg(assert(tagvec!=0 && "tagvec is empty! exiting..\n");)
    assert(tagvec!=0);
    unsigned N= (unsigned)(tagvec>>FRAMER_num_used_bits_in_ptr);
dbg(
    if (N<=15 && N>64) {
        dbg(printf("Wrong N at emptying entry. at: %p, N: %u\n", 
                    (void*)untagged,N);)
      #ifndef MEASURE_RUNTIME        
        exit(0);
      #else
        asm("nop");
      #endif
    }
dbg)
    EntryT* m= FRAMER_get_entry_addr(untagged, N); 

   // printf(">> empty entry: %p\n", m);

    memset (m, 0, sizeof(EntryT)); 
}
#endif

/*
__attribute__((__used__))
__attribute__((always_inline))
//__attribute__((optnone))
static EntryT* 
FRAMER_supplementary_retrieve_from_table (uintptr_t p, uintptr_t tagvec)
{
    //get corresponding slot base.
    unsigned N= (unsigned)(tagvec >>FRAMER_num_used_bits_in_ptr);
    EntryT* m= FRAMER_get_entry_addr(p, N);

    return m;
}
*/

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static HeaderT* 
FRAMER_retrieve_from_table (uintptr_t p, unsigned N)
{
    //get corresponding slot base.
    EntryT* m= FRAMER_get_entry_addr(p, N);
    return  (HeaderT*)(m->base); 
   // return m;
}


//__attribute__((__used__))
__attribute__((always_inline))
static EntryT* 
FRAMER_supplementary_retrieve_from_table_inlining (uintptr_t p, 
                                                   uintptr_t tagvec)
{
    //get corresponding slot base.
    unsigned N= (unsigned)(tagvec >>FRAMER_num_used_bits_in_ptr);
    EntryT* m= FRAMER_get_entry_addr(p, N);

    return m;
}

/*
__attribute__((__used__))
//__attribute__((always_inline))
static int FRAMER_supplementary_check_bounds_only (uintptr_t p, 
                                            uintptr_t p_end, //addr+sizeof(type) e.g.) *((int*)p)
                                            char* base, 
                                            int size)
{
    uintptr_t end = (uintptr_t)(base+size-1); // bound.
    int status= FRAMER_is_outofbound;

    if ((p >= (uintptr_t)base && p<=end)
        && (p_end >= (uintptr_t)base && p_end<=end)){ //inbound
        status= FRAMER_is_inbound; 
    }
    //else if (p==end){ // is off-by-one
    //    status= FRAMER_is_outofframe; //out-of-bound       
    //}
    dbg(printf("base addr:\t%p, size: %d\n", base,size);
        printf("p addr:\t%p\n", (void*)p);
        printf("end addr:\t%p\n", (void*)end);
        printf("p_end:\t%p\n", (void*)p_end);
        )
    dbg(printf("\tSTATUS:\t%d\n", status);)
    return status; 
}
*/

// #ifndef ENABLE_SPACEMIU 1 

__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t 
FRAMER_supplementary_check_inframe(uintptr_t p, //untagged 
                                   uintptr_t gepbase, //untagged 
                                   //uintptr_t logframesize)
                                   unsigned logframesize)
{
    uintptr_t temp= (~0)<<logframesize; 
    return (p^gepbase)&temp; 
}

// #endif

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static uintptr_t 
FRAMER_extract_tagvec (void* p)
{
    return ((uintptr_t)p) & FRAMER_mask_content_out;
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
__attribute__((optnone))
#endif
static uintptr_t 
FRAMER_untag_ptr (void * p)
{
//    untagcount++;
    return (((uintptr_t)p) & FRAMER_mask_tag_out); 
//(v.2)    return ((uintptr_t)p<<16)>>16 ; 
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void* 
FRAMER_untag_ptr_2 (void * p)  // for Pass
{
//    untagcount++;
//    return (void*)(((uintptr_t)p) & FRAMER_mask_tag_out); 
    return (void*)(((uintptr_t)p<<16)>>16) ; 
}

//#ifndef ENABLE_SPACEMIU 2

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void* 
FRAMER_supplementary_compare_idx (unsigned size, 
                                  size_t idx, 
                                  void * ptr)
{ //this size is num_elems of arrays or struct, not num_bytes
    // compare

   #ifdef REPLACE_ASSERT_WITH_IF
    if (!(size>idx)) {
        dbg(printf("f1\n");)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
      #endif
    }
   #else
    assert(size>idx);
   #endif
    return (void*)FRAMER_untag_ptr (ptr);
}

__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void* 
FRAMER_supplementary_compare_size (size_t objsize, 
                    size_t idx, unsigned tysize, 
                    unsigned elemsize, void * ptr)
{
    // compare
   #ifdef REPLACE_ASSERT_WITH_IF
    //if (!(objsize>=(idx+1)*elemsize)) {printf("2\n");exit(0);}
    if (!(objsize>=(idx*elemsize)+tysize)) {
        dbg(printf("f2\n");)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else        
        asm("nop");
      #endif
    }
   #else 
    //assert(objsize>=(idx+1)*elemsize);
    assert(objsize>=idx*elemsize+tysize); 
   #endif
    return (void*)FRAMER_untag_ptr (ptr);
}

/*
__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void* 
FRAMER_supplementary_compare_type (size_t objsize, 
                    unsigned optysize, void * ptr)
{
    // compare
   #ifdef REPLACE_ASSERT_WITH_IF
    if (!(optysize>=objsize)) {
        dbg(printf("f3\n");)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
      #endif
    }
   #else
    assert(optysize>=objsize);
   #endif
    return (void*)FRAMER_untag_ptr (ptr);
}

__attribute__((__used__))
//__attribute__((always_inline))
static unsigned FRAMER_supplementary_get_type_size (unsigned tid, unsigned numBytes)
{ 
    assert_dbg(assert(tid!=0 && "voidtype is deferefenced?\n");)
    assert(tid!=0);
    // FRAMER_BasicTy_table in bits 
    // numBytes as 
    unsigned tsize=0;
    //do something 
    if (tid== IntegerTyID){ //integerTy has multiple kinds of int types
                            //so, we handle intty first.
        //DOUTFUL. Framer pass is supposed to pass paddedTyID (basicID+int), and why add 6?
        dbg(printf("not supposed to enter here. check. \n");)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
      #endif
    }
    else if (tid==VectorTyID) {
        return numBytes; //size arg of store/load saved in *BYTES*
    }
    else if (tid < FRAMER_total_BasicTyCount) { //not int, but other basic type
        tsize= FRAMER_BasicTy_table[tid]; //size of basictype saved in *BITS*
    }
    else {
        unsigned sid= tid-FRAMER_total_BasicTyCount;
        StructEntryT* sindex= FRAMER_baseOfStructTable + sid; //size of struct saved in *BITS* 
        tsize= sindex->tysize;
    }
    //dbg(printf("\tTyID:\t%u,TypeSIZE:\t%u\n", tid, tsize)); 
    assert_dbg(assert(tsize!=0 && "Size of type is 0! Exiting...\n");) 
    assert(tsize!=0); 
    dbg(if (tsize==0) {
        printf("tsize is 0 or less than 8 bits!\n"); 
        printf("tid: %u, numBytes: %u\n", tid, numBytes);
        exit(0);
    })
    return tsize/8;
}

static unsigned 
FRAMER_supplementary_get_type_size_inlining (unsigned tid, unsigned numBytes)
{ 
    assert_dbg(assert(tid!=0 && "voidtype is deferefenced?\n");)
    assert(tid!=0);
    unsigned tsize=0;
    //do something 
    if (tid== IntegerTyID){ //integerTy has multiple kinds of int types
                            //so, we handle intty first.
        //DOUTFUL. Framer pass is supposed to pass paddedTyID (basicID+int), and why add 6?
        dbg(printf("not supposed to enter here. check. \n");)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
      #endif
        //tsize= FRAMER_BasicTy_table[tid+6]; 
    }
    else if (tid==VectorTyID) {
        return numBytes; //size arg of store/load saved in *BYTES*
    }
    else if (tid < FRAMER_total_BasicTyCount) { //not int, but other basic type
        tsize= FRAMER_BasicTy_table[tid]; //size of basictype saved in *BITS*
    }
    else {
        unsigned sid= tid-FRAMER_total_BasicTyCount;
        StructEntryT* sindex= FRAMER_baseOfStructTable + sid; //size of struct saved in *BITS* 
        tsize= sindex->tysize;
    }
    //dbg(printf("\tTyID:\t%u,TypeSIZE:\t%u\n", tid, tsize)); 
    assert_dbg(assert(tsize!=0 && "Size of type is 0! Exiting...\n");) 
    assert(tsize!=0); 
    dbg(if (tsize==0) {
        printf("tsize is 0 or less than 8 bits!\n"); 
        printf("tid: %u, numBytes: %u\n", tid, numBytes);
        exit(0);
    })
    return tsize/8;
}
*/

//#endif // end of ifndef ENABLE_SPACEMIU 2

__attribute__((__used__))
__attribute__((always_inline))
static unsigned 
FRAMER_extract_tagval (void *p)
{
    return (uintptr_t)p>>FRAMER_num_used_bits_in_ptr;
}

// #ifndef ENABLE_SPACEMIU 3

#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((__used__))
__attribute__((__noinline__))
static int 
FRAMER_retrieve_from_header(HeaderT * mptr)
{
  return mptr->size;
}
#endif

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#endif
static void * FRAMER_check_mem_access_INSIDE (
    unsigned tag,
    uintptr_t untagged_p,
    unsigned numBytesToAccess)
{
    FRAMER_Bool_ flag= (FRAMER_Bool_)(tag>>15);  
    tag= tag&(0x7FFF); // now flag out & shifted! use it as a val. 
    
    char* base= NULL;
    int objsize= 0;
    HeaderT* mptr= NULL;
    
    if (flag) {  //small-framed: flag=1
        mptr= FRAMER_cal_header_addr(untagged_p, tag); 
    }
  #ifdef TYPECHECK    
    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged_2(tag)) { 
            // big-framed object //TODO
  #else 
    else{
  #endif
     //   EntryT* m = FRAMER_retrieve_from_table (untagged_p, tag); //TODO
     //   mptr= (HeaderT*)(m->base); 
        mptr = FRAMER_retrieve_from_table (untagged_p, tag); //TODO
            //technically,not base but header!named in the old approach..
    }
  #ifdef TYPECHECK    
    else { 
        /// TypeID is tagged. (flag=big_frame && ID + FRAMER_TyIDStart(100)) //
        // it's using spare bits of big-framed flagged tags 
        ///do something later
        return (void*)untagged_p;    
    }
  #endif

  #ifdef ISOLATE_CALCULATION_OF_HEADER
    objsize= FRAMER_retrieve_from_header(mptr);
    //objsize= mptr->size;
  #endif

  #ifndef ISOLATE_CALCULATION_OF_HEADER 
 
    objsize = mptr->size;
  //  assert (objsize!=0); 
    if (objsize==0) { // for GV, we do not update if it's constant.
        //asm("NOP");
        return (void*)untagged_p; 
    } 
    
    base = (char*)mptr + sizeof(HeaderT);
    assert (base!=NULL); 

    dbg(printf("\t@hd:\t%p\n", mptr));
    dbg(printf("\t@hd:\t%p\n", mptr));
    dbg(printf("\tbase:\t%p\n", base));
    

    uintptr_t end=  (uintptr_t)(base+objsize-1);
    uintptr_t p_end= untagged_p + numBytesToAccess-1;
    dbg(printf("\tend:\t%p\n", (void*)end);)
    dbg(printf("\tp_end:\t%p\n", (void*)p_end);)
    dbg(printf("\tptr:\t%p\n", (void*)untagged_p);)
    
   #ifdef REPLACE_ASSERT_WITH_IF
    if(!(untagged_p>=(uintptr_t)base) || !(p_end <= end)) {
        // printf("maybe called from strncmp\n");
        // printf("\tstr:\t%s\n", (char*)untagged_p);
      dbg(
        printf("\tfatbase:\t%p\n", base);
        printf("\tbytenum:\t%u\n", numBytesToAccess);
        printf("\tsize:\t%d\n", objsize);
        
        printf("\tptr:\t%p\n", (void*)untagged_p);
        printf("\tend:\t%p\n", (void*)end);
        printf("\tp_end:\t%p\n", (void*)p_end);
      )
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
        //printf("FR_err: %p, %p\n", (void*)untagged_p, base);
      #endif
    }
    //asm ("nop");
   #else
    assert((untagged_p>=(uintptr_t)base) && (p_end <= end)); 
        /// this keeps being optimized away run on LNT, along with function body at opt -O2!!
   #endif
    
    dbg(if (!(untagged_p>=(uintptr_t)base) || !(p_end <= end)){ 
        printf("\nnumBytesToAccess: %d\n", numBytesToAccess);
        printf("FRAMER ERROR: out-of-bound at mem access\n"
                "\tAddr: %p.\n", (void*)untagged_p);
    })

  #endif //end of ISOLATE_CALCULATION_OF_HEADER
    return (void*)untagged_p;
}

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void * FRAMER_check_mem_access (
    void * addr,
    unsigned numBytesToAccess)
{
  #ifndef DISABLE_CHECK_BOUNDS 
/*  uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    
    // printf("tagged: %p\n",addr);
    if (untagged_p==(uintptr_t)addr) {
        return addr;
    }
    if (numBytesToAccess==0) {
        return (void*)untagged_p;   
    }
    unsigned tag= FRAMER_extract_tagval(addr); 
    // NOW SHIFT DONE. having flag
*/
    unsigned tag= FRAMER_extract_tagval(addr); 
    // NOW SHIFT DONE. having flag

    if (tag==0) {
        return addr;    
    }
    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    
    if (numBytesToAccess==0) {
        return (void*)untagged_p;   
    }

////////////   
    asm("NOP");

    return FRAMER_check_mem_access_INSIDE(tag,untagged_p,
                                          numBytesToAccess);

  #else
    
    return (void*)FRAMER_untag_ptr(addr);
  
  #endif
}


__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline)) 
#else
__attribute__((noinline))
#endif
static void * 
FRAMER_check_mem_access_inlining (
    void * addr,
    unsigned numBytesToAccess)
{
#ifndef DISABLE_CHECK_BOUNDS 
/*    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    if (untagged_p==(uintptr_t)addr) {
        return addr;
    }
    if (numBytesToAccess==0) {
        return (void*)untagged_p;   
    }
    unsigned tag= FRAMER_extract_tagval(addr); // NOW SHIFT DONE. having flag
*/
    unsigned tag= FRAMER_extract_tagval(addr); 
    // NOW SHIFT DONE. having flag

    if (tag==0) {
        return addr;    
    }
    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    
    if (numBytesToAccess==0) {
        return (void*)untagged_p;   
    }
///////////////////

    FRAMER_Bool_ flag= (FRAMER_Bool_)(tag>>15);  /// 
    tag= tag&(0x7FFF); // now flag out & shifted! use it as a val.  ////
     
    char* base= NULL;
    int objsize= 0;
    HeaderT* mptr= NULL;
   
    if (flag) {
        mptr= FRAMER_cal_header_addr(untagged_p, tag);    

    }
  #ifdef TYPECHECK
    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged_2(tag)) { 
  #else
    else {
  #endif
       // EntryT* m = FRAMER_retrieve_from_table (untagged_p, tag);     /////
       // mptr= (HeaderT*)(m->base); //technically,not base but header!named in the old approach..
        mptr = FRAMER_retrieve_from_table (untagged_p, tag);     /////
       
    }
  #ifdef TYPECHECK
    else { 
        /// TypeID is tagged. (flag=big_frame && ID + FRAMER_TyIDStart(100)) //
        // it's using spare bits of big-framed flagged tags 
        ///do something later
        return (void*)untagged_p;    
    }
  #endif

  #ifdef ISOLATE_CALCULATION_OF_HEADER
    objsize= FRAMER_retrieve_from_header(mptr);
    //objsize= mptr->size;
  #endif
 
 #ifndef ISOLATE_CALCULATION_OF_HEADER

    objsize = mptr->size;
    //assert(objsize!=0); 
    if (objsize == 0) {
        //asm("NOP"); 
        return (void*)untagged_p;    
    }
    
    base = (char*)mptr + sizeof(HeaderT);
    assert(base!=NULL); 

    uintptr_t end=  (uintptr_t)(base+objsize-1);
    uintptr_t p_end= untagged_p + numBytesToAccess-1;

  #ifdef REPLACE_ASSERT_WITH_IF    
    if(!((untagged_p>=(uintptr_t)base) && (p_end <= end))) {
        dbg(printf("Out of bound.inln.\n");)
      #ifndef MEASURE_RUNTIME
        exit(0); 
      #else 
        asm("nop"); 
      #endif 
     }
  #else
    assert((untagged_p>=(uintptr_t)base) && (p_end <= end)); //(1) 
  #endif

 #endif // ISOLATE_CALCULATION_OF_HEADER    
    return (void*)untagged_p;
#else // DISABLE_CHECK_BOUNDS
    return (void*)FRAMER_untag_ptr(addr);
#endif // DISABLE_CHECK_BOUNDS

}

//#endif  //end of ifNdef of enable_typecheck 

dbg(
__attribute__((__used__))
//__attribute__((always_inline))
static FRAMER_Bool_ 
FRAMER_supplementary_isBigAddr (void *p)
{
    // if upper 16 bits are already used by userprogram, return true.
    FRAMER_Bool_ tagtaken=false;
    //uintptr_t result= ((uintptr_t)p) & (~FRAMER_mask_tag_out); 
    uintptr_t result= ((uintptr_t)p) & FRAMER_mask_content_out; 
    if (result!=0) { // 
        tagtaken=true; 
    }
    return tagtaken; 
}
)
__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void 
FRAMER_forall_global_variable (void * taggedPtr, 
                               int FramerTypeID,  
                               unsigned numElems, 
                               unsigned numBytesPerElem,
                               FRAMER_Bool_ isConstant,
                               char ** gvTag //holding the tag
                             #ifdef ENABLE_SPACEMIU 
                               , FRAMER_Bool_ isUnionTy 
                             #endif 
                               )
                 // void* mybase, void* myend, //myend not used. delete?
                 // unsigned isPLtokenbuf)
{
#ifndef DISABLE_GLOBAL_METADATA_UPDATE
  
  dbg( 
    printf("\nHOOK Global Variable:: \n");
   // printf("\ttaggedPtr:\t%p\n", taggedPtr);
   // printf("\tnumElems:%d\n", numElems);
    printf("\tFramerTypeID:%u\n", FramerTypeID);
   // printf("\t*gvtag: %p\n", *gvTag);
  )
    
    *gvTag= (char*)taggedPtr;
         
    unsigned raw_obj_size= numElems * numBytesPerElem; 
    unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT) + 1; 

    FRAMER_Bool_ flag= FRAMER_supplementary_extract_flag (taggedPtr); 
    uintptr_t tagvec= FRAMER_extract_tagvec (taggedPtr); 
    char* untagged_p= (char*)FRAMER_untag_ptr(taggedPtr);
  
  dbg( 
    printf("\tThinbase:\t%p\n", taggedPtr);
  )
    char* hd_addr = untagged_p - sizeof(HeaderT); 
    assert_dbg(assert(tagvec!=0LL && "Global variable pointers are not tagged!\n");)
    assert(tagvec!=0LL);
   
    //unsigned N_or_offset= (unsigned)((tagvec & FRAMER_mask_only_flag_out)>>FRAMER_num_used_bits_in_ptr); 
    /// p: hidden padded_obj_base. header inserted by pass.

    // update metadata either in the table or obj header. 
    
    if (flag) {
        dbg(printf("\tSMALL FRAME\n"));
    }
    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged(tagvec)){ //flag==0
        
        dbg(printf("\tBIG FRAME\n"));
        
        unsigned N_or_offset= tagvec>>48; 
        
        FRAMER_Bool_ entry_available = 
            FRAMER_update_table(hd_addr,N_or_offset);   
        
        assert_dbg(assert (entry_available 
                &&  "corresponding entry in the table is not 0!"
                    "possibly overlapped allocation?\n");) 
        assert (entry_available); 
    }
    else { //FramerTyID tagged.(sharing '0' flag with big-framed objects)
        ;
    }
    if (!isConstant) {
        FRAMER_update_header (hd_addr, 
                FramerTypeID,
                raw_obj_size
            #ifdef ENABLE_SPACEMIU
         
              #ifdef ENABLE_TRACK_ARRAYS
                ,numBytesPerElem
              #endif
               
                ,isUnionTy 
            #endif   
                );

    } // Constant global's header is updated at compile time. 
    //TODO: maybe header for ALL GLOBAL can be updated at compile time?
#endif

#ifdef COUNT_BIG_SMALL_OBJECTS
    if (flag==FRAMER_is_smallframe) {
        FRAMER_SMALL_FRAMED_OBJECT_COUNT++;
    }
    else {
        FRAMER_BIG_FRAMED_OBJECT_COUNT++;
    }
#endif  

}

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void* 
FRAMER_forall_alloca (char * thinBase, 
                            unsigned numElems,
                            int FramerTypeID, 
                            unsigned numBytesPerElem
                        #ifdef ENABLE_SPACEMIU 
                            ,FRAMER_Bool_ isUnionTy
                        #endif 
                            )
                            //void* locationOfFramerTyEntry)
{    
#ifndef DISABLE_ALLOCA_METADATA_UPDATE
  dbg(
    printf ("HOOK Alloca\n");
    printf("\tTthinbase:\t%p\n", thinBase);
//    printf("\t#Elems:\t%d\n", numElems);
    printf("\tTypeID:\t%d\n", FramerTypeID);
  )

  dbg(
    if (FRAMER_supplementary_isBigAddr(thinBase)){
        dbg(printf("ALLOCA isBigAddr: %p\n", thinBase);)
        exit(0);
    }
  ) 
    char* tagged_p= NULL;    
    char* fatbase= thinBase - sizeof(HeaderT); //header address
    
    dbg(printf("\theader addr:\t%p\n", fatbase));
    
    unsigned raw_obj_size = numElems*numBytesPerElem;
    unsigned padded_obj_size = sizeof(HeaderT)+raw_obj_size;
    
    //printf("\traw size:\t%d\n", raw_obj_size);
    //printf("\tHeader addr:\t%p\n", p);

    unsigned N= FRAMER_decide_log_framesize (fatbase, padded_obj_size);  
    uintptr_t tag=0;
    FRAMER_Bool_ whichframe;

    // update metadata in the obj header, but for big-framed obj, update entry also.(@header) 
    if (N > FRAMER_log_slotsize) {
        dbg(printf("\tbig frame\n"));

        FRAMER_Bool_ entry_available = 
            FRAMER_update_table (fatbase, N);   
        
        assert_dbg(assert (entry_available 
                && "corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n");) 
        assert (entry_available); 
        
        tag= (uintptr_t)N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        dbg(printf("\tsmall\n"));
        
        tag= FRAMER_supplementary_cal_offset(fatbase);
        whichframe= FRAMER_is_smallframe; 
    }
    FRAMER_update_header (fatbase, 
                          FramerTypeID,
                          raw_obj_size

                    #ifdef ENABLE_SPACEMIU
                      
                        #ifdef ENABLE_TRACK_ARRAYS
                          , numBytesPerElem
                        #endif
                     
                          , isUnionTy
                    #endif
                          );

    tagged_p = (char*)FRAMER_supplementary_tag_ptr(fatbase, 
                                            tag, 
                                            whichframe);     
    
    dbg(printf("\ttagged:\t%p\n", tagged_p));
   
    tagged_p= tagged_p + sizeof(HeaderT);

    return tagged_p;
#else
    return thinBase;
#endif
}

//// 
/// FRAMER_forall_malloc is interposed during compile time by framer pass.
//// 
#ifdef ENABLE_SPACEMIU
 
__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void * 
FRAMER_forall_malloc (size_t raw_obj_size, 
                      int FramerTypeID,  
                      FRAMER_Bool_ isUnionTy 
                      )
{
#ifdef DISABLE_ALL_CHECKS
 
    return malloc(raw_obj_size);
 
#else  
    
    dbg(
      printf("\nHOOK Malloc\n");
    )

    unsigned padded_obj_size= (unsigned)(raw_obj_size+sizeof(HeaderT)); 
    
    // allocating
    void * p = malloc(padded_obj_size);
    assert (p!=NULL);
   
    dbg(
      if (FRAMER_supplementary_isBigAddr(p)){
        printf("Malloc isBigAddr: %p\n", p);
        exit(0);
      }
    )

    dbg(
      printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%lu\n\tPadded Objsize:\t%lu\n", p, raw_obj_size, padded_obj_size);
    )
    
    
    // initialising buffer 
    // memset (p, 0, padded_obj_size); 
    
    unsigned N = FRAMER_decide_log_framesize (p, padded_obj_size);  
    dbg ( printf("\tLog(Frame):\t%d\n", N) );

    uintptr_t tag= 0;
    FRAMER_Bool_ whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;

    if (N > FRAMER_log_slotsize) {
 
        FRAMER_Bool_ entry_available = 
            FRAMER_update_table (p, N); 
        assert_dbg(assert (entry_available 
                && "malloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n");) 
       
      dbg( 
        
        if (entry_available==0) {
            printf(">> N: %d, p: %p\n", N, p);           
        } 
      )
        
        assert (entry_available); 
        
        tag= (uintptr_t)N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
    
  #ifdef ENABLE_SPACEMIU    
    
    //int heapTID= FRAMER_is_heap_obj; //TODO: heaptid:= tid arg?  
    
    FRAMER_update_header(p, FramerTypeID, raw_obj_size, 
    // TODO: heapTID := framer tid arg

    #ifdef ENABLE_TRACK_ARRAYS
      raw_obj_size, 
    #endif
    
    false); 
  
  #else    
 
    FRAMER_update_header(p, VoidTyID, raw_obj_size); 

  #endif    
  
  dbg( 
    printf("\tpadded_P:\t%p\n\tFramerTypeID:\t%u\n", p, FramerTypeID);
  )
   
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
 
    assert(tagged_p != 0);
     
    return ((char*)tagged_p + sizeof(HeaderT));
#endif 
}
#endif // ENABLE_SPACEMIU

//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

#ifdef ENABLE_SPACEMIU

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void * 
FRAMER_forall_realloc (void* thin_base, 
                       size_t size,
                       int FramerTypeID,  
                       FRAMER_Bool_ isUnionTy,
                       int XTyID)
{

#ifdef DISABLE_ALL_CHECKS
    return realloc(thin_base, size);
#else  

    dbg(printf("\nHOOK realloc\n"));
    
    uintptr_t tagvec= FRAMER_extract_tagvec (thin_base); 
    // check if it's tagged  
    
  #ifdef ENABLE_SPACEMIU 
   
    #ifdef ENABLE_TRACK_ARRAYS  
      assert(tagvec!=0);
    #else
      if (tagvec==0) {
        return realloc(thin_base, size);
      }
    #endif
  
  #endif
      
    uintptr_t untagged_p= FRAMER_untag_ptr(thin_base);
    uintptr_t padded_base = untagged_p - sizeof(HeaderT);
    
    ///
    // if tid== xtyid (Failed at detecting an effective type of realloc),
    // then don't instrument it.//////
    /// 
    if (FramerTypeID==XTyID) {
        return realloc((void*)padded_base, size);
    }

    FRAMER_Bool_ flag= FRAMER_supplementary_extract_flag (thin_base); 

    unsigned padded_obj_size= size + sizeof(HeaderT);  

  #ifndef ENABLE_SPACEMIU    
    //1.1. reset metatable entry, if it's big frame.
     if (flag==FRAMER_is_bigframe){ 
        FRAMER_empty_metadata_entry (padded_base, tagvec);
    }
  #endif
    assert_dbg(assert((HeaderT*)padded_base!=NULL 
             && "Hook realloc: Header is NULL at free! Double free?\n");)
    assert((HeaderT*)padded_base!=NULL); 

    dbg(printf("\told thin_base:\t%p\n", thin_base));
    
    // 2.call realloc and pass untagged hidden base and new size (padded)
    void * p = realloc((void*)padded_base, padded_obj_size);
    assert_dbg(assert(p!=NULL && "realloc returned NULL");) 
    assert(p!=NULL);
    
    dbg(if (p==NULL) {
        printf("realloc returned NULL. exiting..\n");
        exit(0);
    })
     
    dbg(
      printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%lu\n", 
        p, size, padded_obj_size);
    )
    
    // 3. do the rest like malloc with returned ptr, 
    // and return ptr to the beginning of actual object.
    
    uintptr_t N = (uintptr_t)FRAMER_decide_log_framesize (p, padded_obj_size);  
    
    uintptr_t tag=0;
    FRAMER_Bool_ whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    
    if (N > FRAMER_log_slotsize) {
        
        FRAMER_Bool_ entry_available = 
            FRAMER_update_table (p, N); 
        
        assert_dbg(assert (entry_available 
                && "realloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n");) 
        assert (entry_available); 
        
        tag= N;
        whichframe= FRAMER_is_bigframe;
       //printf("\ttagged_p:\t%p\n", tagged_p);
    }
    else {
        //dbg(printf("\trealloc. small frame\n")); 
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
  
  #ifdef ENABLE_SPACEMIU    
    
    FRAMER_update_header(p, FramerTypeID, size, 

    #ifdef ENABLE_TRACK_ARRAYS
      raw_obj_size, 
    #endif
    
        false); 
  
  #else    
 
    FRAMER_update_header(p, VoidTyID, size); 

  #endif    
    
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
 
    assert(tagged_p != 0);

    return ((char*)tagged_p+sizeof(HeaderT)); 

  #endif
}
#endif // ENABLE_SPACEMIU


#ifndef ENABLE_SPACEMIU

__attribute__((__used__))
__attribute__((always_inline))
static void FRAMER_forall_getelementptr (void * GEP, 
                                    void * baseOfGEP) 
{
    return;
  #ifndef DISABLE_CHECKS_AT_GEP
    unsigned tag= FRAMER_extract_tagval(GEP); // NOW SHIFT DONE. having flag
    if (tag==0) {
        return;
    }
    FRAMER_Bool_ flag= (FRAMER_Bool_)(tag>>15);  
    tag= tag&(0x7FFF); // now flag out & shifted! use it as a val. 
 
    unsigned logframesize= FRAMER_log_slotsize;

    #ifdef TYPECHECK    
      if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged_2(tag)){ //n>15
    #else    
      if (flag==FRAMER_is_bigframe){ //n>15
    #endif
         logframesize= tag;
      }
    /////////

  #ifdef TYPECHECK    
    else if(flag==FRAMER_is_smallframe){
        logframesize= FRAMER_log_slotsize;
    }
    else { //tag is just typeID (flag==is_bigframe)
        return;
    }
  #endif
    uintptr_t is_inframe= FRAMER_supplementary_check_inframe((uintptr_t)GEP,//untagged_p, 
                                                        (uintptr_t)baseOfGEP,//untagged_gepbase, 
                                                        logframesize);
    assert(is_inframe==0);
  #endif
// end of DISABLE_CHECKS_AT_GEP
}

#endif //end of ENABLE_SPACEMIU

__attribute__((__used__))
__attribute__((always_inline))
static void * FRAMER_forall_store_inlining ( 
                        void * addr, //destAddress, 
                        unsigned numBytesOfSrcTy)
{
    dbg(printf("store inln\n");)

  #ifdef FULL_INLINING 
    
    return FRAMER_check_mem_access_inlining(addr, numBytesOfSrcTy);

  #else 

    return FRAMER_check_mem_access(addr, numBytesOfSrcTy);

  #endif
}

__attribute__((__used__))
__attribute__((always_inline))
static void * FRAMER_forall_store ( 
                        void * addr, 
                        unsigned numBytesOfSrcTy)
{
    dbg(printf("STORE. %p, numBytes: %u\n", addr, numBytesOfSrcTy);)
    return FRAMER_check_mem_access(addr, numBytesOfSrcTy);
}


__attribute__((__used__))
__attribute__((always_inline))
static void * 
FRAMER_forall_load (void * addr, 
                        //unsigned FramerTypeID, 
                        unsigned numBytesOfLoadedContent)
                         /// when we meet p_content = load <pointerty> p, 
                         //  p must be pointer, and p_contenr may be or not.
                         /// addrToBeloaded: p , resultTy: a type of p_content  
{
    return FRAMER_check_mem_access(addr, numBytesOfLoadedContent); 
}


__attribute__((__used__))
__attribute__((always_inline))
static void * FRAMER_forall_load_inlining (void * addr, 
                        unsigned numBytesOfLoadedContent)
{
  #ifdef FULL_INLINING
    return FRAMER_check_mem_access_inlining(addr, numBytesOfLoadedContent); 
  #else
    return FRAMER_check_mem_access(addr, numBytesOfLoadedContent);
  #endif
}


__attribute__((__used__))
__attribute__((always_inline))
static void * FRAMER_forall_call_llvm_memtransfer (

    void * addr, 
    uint64_t numBytesToCopy, 
    unsigned numAlign, 
    FRAMER_Bool_ isVolatile )
{
  dbg(
    printf("HOOK MEMTRANSFER\n");
    printf("\taddr:\t%p\n", addr);
  )
  return FRAMER_check_mem_access (
        addr, numBytesToCopy); 
}

__attribute__((__used__))
__attribute__((always_inline))
static void * FRAMER_forall_call_llvm_memset(void * addr,
                                    signed char val,
                                    uint64_t numBytesToCopy, 
                                    unsigned numAlign, 
                                    FRAMER_Bool_ isVolatile )
{
    dbg(printf("HOOK MEM SET \n"));
    assert_dbg(assert(numAlign <= 16 
               && "FRAMER assumes memset alignment is <=16!\n")); 
     
    return FRAMER_check_mem_access (
            addr, numBytesToCopy); 
}


#ifdef ENABLE_SPACEMIU

__attribute__((__used__))
static void *
FRAMER_get_tyentry (short objTyid,
                    unsigned MaxOffset) 
{
  unsigned idx= (MaxOffset+1)*2*(int)objTyid;
  return  (char*)FRAMER_baseOf_OffsetTable+idx;
}

#endif


__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#else
__attribute__((always_inline))
#endif
static HeaderT * 
FRAMER_get_header_addr (uint64_t untagged_p,
                        unsigned tag) //tag holds flag here.
{
    FRAMER_Bool_ flag= (FRAMER_Bool_)(tag>>15);  
    tag= tag&(0x7FFF); // now flag out & shifted! use it as a val. 
    
    char* base= NULL;
    HeaderT* mptr= NULL;
    
    if (flag) {
        // here, tag is un-flagged. 
        mptr= FRAMER_cal_header_addr(untagged_p,tag); 
    }
 
  #ifdef TYPECHECK    

    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged_2(tag)) { 

  #else 

    else {

  #endif
        mptr = FRAMER_retrieve_from_table (untagged_p, tag); //TODO
        //technically,not base but header!named in the old approach..
    }
    return mptr;
}

#ifdef ENABLE_SPACEMIU

__attribute__((__used__))
static FRAMER_Bool_
FRAMER_check_safecast (unsigned offset, 
                       short destyid, //dest type ID of bitcast or mem access
                       short objTyid,
                       unsigned Maxoffset,
                       unsigned totaltycount) //padded ty count
{

dbg(
  printf("\t* baseOf_OffsetTable:\t%p\n",       
          FRAMER_baseOf_OffsetTable);
)
  
  short* initptr= (short*)FRAMER_get_tyentry(
                          objTyid,
                          Maxoffset);
   
  assert(initptr!=NULL);
  
  dbg( printf ("*initptr: %p\n", *initptr);  ) 

/// From here, version 3. (If you wanna see version 1,2, check previous repo)
/// Type relation table (TR) is a TxT array, where T is #total_types.  
/// If Ty_x is safely converted to Ty_y, then
/// TR[x][y] = 1, otherewise 0.
    
  short tidatoff= *(initptr + offset); //initptr is short* typed. 

dbg(  

  //printf("#################\n");
  printf("\noffset:\t%d, tidatoff:\t%d\n", offset, tidatoff);
  printf("objTyid:\t%d, destyid:\t%d\n", objTyid, destyid);
  //printf("Maxoffset:\t%d, totaltycount:\t%d\n", Maxoffset, totaltycount);

)
  /// 
  // sometimes bitcast is applied at an offset where is meaningless.
  // e.g. out of bound in perlbench
  /// 
  if (tidatoff < 0) {
    
    //printf("-> ERROR: Bitcast at meaningless offset (%d)\n", offset); 
    //exit(0);

    return false;    
    //return true;    
  }

  return (*(FRAMER_baseOfSafeCastTable + (tidatoff*(totaltycount+1))+destyid));
  
}

#ifdef ENABLE_TRACK_ARRAYS

    __attribute__((__used__))
__attribute__((always_inline))
static uint64_t 
FRAMER_get_elembase (uintptr_t ptr, //untagged
                     uint64_t base,
                     unsigned elemsize,
                     unsigned objsize)
{
    if (elemsize==objsize) {
        return base;    
    }
   
    uint64_t elembase= base;
    
    while(true) {
        
        uint64_t obo= elembase+elemsize;  
        
        if (ptr < obo) {
            break;    
        }
        elembase= obo;
    }
    return elembase;
}

#endif // end of ENABLE_TRACK_ARRAYS

/*
///
// commented out since now we use T*T matrix for relation table.
///

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void 
FRAMER_update_types_for_heap_obj (HeaderT* ptr,
                                  short destTid,
                                #ifdef ENABLE_TRACK_ARRAYS
                                  unsigned destTsize,
                                #endif
                                  unsigned raw_obj_size,
                                  FRAMER_Bool_ isUnionTy)
{
    ptr->FramerTyID= destTid; //FramerTyID update here

    dbg(  

            printf("\tFramerTyID:\t%d\n", ptr->FramerTyID);
            printf("\tisUnionTy:\t%d\n", ptr->isUnionTy);
            printf("\tRTTunion:\t%d\n", ptr->RTTunion);

       )
    #ifdef ENABLE_TRACK_ARRAYS

        assert(raw_obj_size >= destTsize);

    // if (destTsize==raw_obj_size){
    //  ptr->elemsize= destTsize; //already stored at allocation site. 
    //}

    // (2) if raw_objsize mod bitcasts' destty's size == 0 (not equal)
    // --> save desty's id in the header and ...some array info in the header also.

    if (destTsize < raw_obj_size
            && ((raw_obj_size%destTsize) == 0)) {

        ptr->elemsize= destTsize;   

        if (isUnionTy) {
            ptr->isUnionTy= (short)isUnionTy;
            ptr->RTTunion= 0;
        }
    }

    // (3) we assume that it is used as a byte array. 
    // assign ty (-1) FRAMER_is_heap_Init.

    else {
        printf("what case? destTsize: %d, raw_obj_size: %d\n",
                destTsize, raw_obj_size); exit(0);
    }

    #endif

}
*/



__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void *
FRAMER_type_update_at_memWRITE (void * addr,
                                short destyid) //get typeid of val 
{
  dbg(printf("\nHOOK STORE (memWRITE)\n");
    printf("\tAddr:\t%p\n", addr);
    printf("\tDest Tid:\t%d\n", destyid);
   ) 
    
    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
  
  #ifdef ENABLE_STRICT_UNION_CHECKING
 
    // if ENABLE_STRICT_UNION_CHECKING is on, Framer pass hooks ALL mem access.
    // if it's off, Framer pass hooks only mem access whose pointer operand
    // is alias with an union-typed object.
    
    if (untagged_p==(uintptr_t)addr) {
        return (void*)untagged_p;
    } // TODO: we insert this only for aggregated type (union), so unnecessary?
   
    if (!isUnionTy) {
        return (void*)untagged_p; 
    }
  #else  

    unsigned tag= FRAMER_extract_tagval(addr); 

    HeaderT* mptr= FRAMER_get_header_addr (untagged_p, tag);
    //RTTunion is set 1 at memory allocation. 
   
    dbg(printf("\tFramerTid:\t%d\n", mptr->FramerTyID);)
    
    mptr->RTTunion= destyid;
  
  #endif
    
    return (void*)untagged_p;
}

/*
//__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#else
__attribute__((always_inline))
#endif
static void
FRAMER_mark_heap_array (HeaderT * hd)
{
    hd->FramerTyID= FRAMER_IS_HEAP_ARRAY;
}


__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#else
__attribute__((always_inline))
#endif
static FRAMER_Bool_ 
FRAMER_is_heap_array (HeaderT * hd)
{
    if (hd->FramerTyID == FRAMER_IS_HEAP_ARRAY) {
        return true;
    }
    return false;
}


__attribute__((__used__))
//__attribute__((always_inline))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void 
FRAMER_handle_heap_object_for_cast (uint64_t untagged_p,
                                    uint64_t base,
                                    unsigned objsize,
                                    short destyid,
                                    unsigned destTsize,
                                    HeaderT * mptr,
                                    FRAMER_Bool_ isUnionTy)
{
dbg(
  if (objsize==1) {
    printf("ptr:\t%p  (objsize==1)\n", (void*)untagged_p);
    printf("base:\t%p\n", (void*)base);
    printf("header:\t%p \n", mptr);
    printf("destid:\t%d\n", destyid);
    printf("dTsize:\t%d\n", destTsize);
    printf("objtid:\t%d\n", mptr->FramerTyID);
  }
)

  if (untagged_p == base) {   
       
    dbg(  printf("\t--> MALLOC! Original tyid:%d\n", 
             mptr->FramerTyID);)

    #ifndef ENABLE_TRACK_ARRAYS

      if (objsize > destTsize) {
        FRAMER_mark_heap_array(mptr);
        return; 
      }

    #endif

    // the heap's 1st bitcast. structure-type. 
    FRAMER_update_types_for_heap_obj (mptr, destyid, 
      #ifdef ENABLE_TRACK_ARRAYS
        destTsize,
      #endif  
        objsize,
        isUnionTy); 
         
    }

    // if the FYID is FRAMER_is_heap_obj, then skip cast check anyway.
    // even if untagged_p != base.
    // e.g.) heap alloc->ptr arith->then typecast: we don't handle this. skip.  

    return;

}
*/

__attribute__((__used__))
//__attribute__((always_inline))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void
FRAMER_check_casts ( void* addr,
                     short destyid,
                     //unsigned destTsize,
                     FRAMER_Bool_ isUnionTy,
                     unsigned Maxoffset,
                     unsigned totaltycount ) // 
{
    unsigned tag= FRAMER_extract_tagval(addr);
    
    if (tag==0) { return; }
    
    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    
    HeaderT* mptr= FRAMER_get_header_addr (untagged_p, tag);
    
    short tyid= mptr->FramerTyID;

  #ifndef INLINE_CUSTOM_MALLOC_WRAPPER
    
    // if an obj type is X type, then return  
    if (tyid==totaltycount) {
        return;  
    }
  
  #endif        

    char * base= (char*)mptr + sizeof(HeaderT);
    // now we got the base. 
  
dbg(    
    printf("\n\tuntaggedp:\t%p\n", (void*)untagged_p); 
    printf("\tHeader:\t%p\n", mptr);
    printf("\tBase:\t%p\n", base);
    printf("\nptr: %p, base: %p\n", (void*)untagged_p, base); 
)  

  #ifdef ENABLE_TRACK_ARRAYS
  
    unsigned objsize= mptr->size;

    uint64_t elembase= FRAMER_get_elembase ((uintptr_t)untagged_p,
                                   (uint64_t)base, 
                                   mptr->elemsize, 
                                   mptr->size); 
 
  #else
    
    uint64_t elembase= (uint64_t)base;  
 
  #endif 
    
    uint64_t offset= untagged_p - elembase;
 
dbg( 
  printf("ptr:\t%p, elembase:\t%p\n", (void*)untagged_p, (void*)elembase); 
)
  
  if (!FRAMER_check_safecast(offset, destyid, 
                             mptr->FramerTyID, 
                             Maxoffset,
                             totaltycount)) {
    asm("NOP");
    
  dbg( 
    printf("ptr:\t%p, elembase:\t%p\n", (void*)untagged_p, (void*)elembase); 
    printf("offset:\t%d\n", (unsigned)offset);
    printf(" --> Unsafe\n"); 
    //// for bzip2. this can be performed if we gets error id.
    size_t * ptratoff= (size_t*)untagged_p; 
    printf("void ptr's content: %#018zx\n", *ptratoff); 
    exit(0);
  )
  
  }
}


__attribute__((__used__))
//__attribute__((always_inline))
//__attribute__((optnone))
//__attribute__((noinline))
static void 
FRAMER_forall_bitcast (void * addr,
                       short destyid,
                       FRAMER_Bool_ isUnionTy,
                       //unsigned destTsize,
                       unsigned maxOffset,
                       unsigned totaltycount // only used type count 
                       ) // telling if dest ty is union
{
dbg(
    printf("\nHOOK BITCAST ######\n");
    printf("\tpointer:\t%p\n", addr);
    printf("\tmaxOffset:\t%u\n",maxOffset);
    printf("\tmax_upcasts:\t%u\n",max_upcasts);
    exit(0);
)    

// *TODO: based on the ptr, get the byte's type id. *
// currently pass static src id, and see if it's the safe cast. 
// TODO: later pass runtime src tid. 

///
/// structt* p2= (struct*)p1// where p1 is int* (p1=&x, where int x)
/// then p1 is not tagged, and we do not perform type checking!!
/// only type cast between structures

   // asm("NOP");
    FRAMER_check_casts (addr, //untagged_p, 
                        destyid, 
                        //destTsize, 
                        isUnionTy,
                        maxOffset,
                        totaltycount);
  //  asm("NOP");
}

/* for mem read for union types. performs type checking */
__attribute__((__used__))
#ifndef ISOLATE_CALCULATION_OF_HEADER
__attribute__((always_inline))
#else
__attribute__((noinline))
#endif
static void *
FRAMER_type_check_at_memREAD (void * addr,
                              short destyid,
                              unsigned short MaxOffset) 
{
/*
    printf("\nHOOK LOAD (memREAD)\n");
    printf("\tAddr:\t%p\n",addr);
    printf("\tDest Tid:\t%d\n",destyid);
    printf("\tDestSize \t%d\n",destTsize);
    uintptr_t untagged_p= (uintptr_t)FRAMER_untag_ptr(addr);
    
    unsigned tag= FRAMER_extract_tagval(addr); 

  #ifdef ENABLE_STRICT_UNION_CHECKING

    // if ENABLE_STRICT_UNION_CHECKING is on, Framer pass hooks ALL mem access.
    // if it's off, Framer pass hooks only mem access whose pointer operand
    // is alias with an union-typed object.
    
    if (untagged_p==(uintptr_t)addr) {
        return (void*)untagged_p;
    }
    if (!isUnionTy) {
        return (void*)untagged_p; 
    }
*/
  
  #ifdef ENABLE_STRICT_UNION_CHECKING
  
    FRAMER_check_casts (addr, 
                        destyid, 
                        //destTsize, 
                        true, 
                        MaxOffset,
                        totaltycount);
  #else

    // If ENABLE_STRICT_UNION_CHECKING is off,
    //  this hook is inserted only for union-typed object (not subfield).
    // so just check RTT of the union-typed OBJECT is compatible with dest ty.
    
    uintptr_t untagged_p= FRAMER_untag_ptr(addr);
    unsigned tag= FRAMER_extract_tagval(addr); 
 
    HeaderT* mptr= FRAMER_get_header_addr (untagged_p, tag);
    
    short rtt= mptr->RTTunion;       
  
   
    if (rtt!=destyid) {
        printf("ERROR::: rtt!=dest tid\n");
        exit(0);
    }
  #endif  
     
    return (void*)FRAMER_untag_ptr(addr); 
}
#endif


#ifndef ENABLE_SPACEMIU
//void FRAMER_func_epilogue (void* tagged)
//__attribute__((always_inline))
//__attribute__((__used__))
static void 
FRAMER_reset_entries_for_alloca (void* tagged) 
{
  #ifndef DISABLE_ALLOCA_METADATA_UPDATE
    dbg(printf("reset entries\n"));
    if (FRAMER_supplementary_extract_flag(tagged)==FRAMER_is_smallframe) {
        return;
    }
    uintptr_t untagged_p= FRAMER_untag_ptr(tagged);
    uintptr_t tagvec= FRAMER_extract_tagvec (tagged); 

    FRAMER_empty_metadata_entry (untagged_p, tagvec);
  #endif
}
#endif

__attribute__((__used__))
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
static void
FRAMER_lazy_type_update (void * ptr, unsigned tid)
{
    if (FRAMER_extract_tagvec(ptr) == 0) {
        return;
    }
    
    uintptr_t padded_base = FRAMER_untag_ptr(ptr) - sizeof(HeaderT);

   ((HeaderT*)padded_base)->FramerTyID= tid;
}


/*__attribute__((__used__))
static void
FRAMER_create_hashtable (void* baseOf_OffsetTable,
                         short total_offset_count,
                         short max_ty_count_per_off,
                         short max_offset_val,
                         unsigned tblentrysize)   
{
//  GHashTable *hash;

  hash= g_hash_table_new(g_direct_hash, g_direct_equal);

  for (unsigned i=0; i<total_offset_count; i++) {
    // * insert values 
    
    // read {uint64_t key (tid/offset combimed)}.   
    uint64_t * tykey= (uint64_t*)(baseOf_OffsetTable + i*tblentrysize); 
    
    short * kylist= (short*)(tykey + 1);  
    
    //TODO: kylist type?? think of above/below code. maybe have to re-write. 
    
    g_hash_table_insert(hash, (GINT_TO_POINTER)(*tykey), kylist);

  }
}
*/


//__attribute__((always_inline))
__attribute__((__used__))
static void 
FRAMER_do_initializing (unsigned numStructTyCount, 
                        void* baseOf_StructTable
                   #ifdef ENABLE_SPACEMIU 
                        ,char* baseOf_OffsetTable
                        ,short total_offset_count
                        ,short max_ty_count_per_off
                        ,short max_offset_val
                        ,unsigned tblentrysize
                      #ifndef RTTABLE_VERSION_1
                        , void* SafecastTable
                      #endif
                   #endif
                        )   
{

    FRAMER_structTy_count= numStructTyCount;
    FRAMER_baseOfStructTable= (StructEntryT*)baseOf_StructTable;

#ifdef ENABLE_SPACEMIU
    FRAMER_baseOf_OffsetTable= baseOf_OffsetTable;
    FRAMER_total_offset_count= total_offset_count;
    FRAMER_max_ty_count_per_off= max_ty_count_per_off;
    FRAMER_max_offset_val= max_offset_val;

  #ifndef RTTABLE_VERSION_1
    //FRAMER_baseOfSafeCastTable= (short*)SafecastTable;
    FRAMER_baseOfSafeCastTable= (FRAMER_Bool_*)SafecastTable;
  #endif

#endif     

    FRAMER_metadata_file_size = FRAMER_metatable_count
                                *sizeof(SlotT);
    
  dbg(   
    printf("\n***** Initialising *************\n");
    printf("HeaderT size:\t%lu\n", sizeof(HeaderT));
    printf("#Struct types:\t%u\n", numStructTyCount);
    printf("StructBasicTybase:\t%p\n", baseOf_StructTable);
    printf("U_space base:\t%p\n\n", 
        (void*)FRAMER_slotbase_of_userspace_start);
  )
   
    //FRAMER_supplementary_setup_FRAMER_BasicTy_table();
    assert_dbg(assert (FRAMER_llvm_BasicTyCount+ FRAMER_extra_BasicTyCount=15=
            && "Assert failed: Framer BasicTyCounts do not fit!\n");)
    assert (FRAMER_llvm_BasicTyCount+ FRAMER_extra_BasicTyCount==15);

    environ = NULL;

    FRAMER_TABLE= (SlotT*)mmap (0, 
                                ((size_t)FRAMER_metadata_file_size),
                                PROT_READ | PROT_WRITE | PROT_NONE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, 
                                -1,//FRAMER_fd, 
                                (off_t)0);
   
    if (FRAMER_TABLE == MAP_FAILED) {
        printf ("ERROR:mmap error for metadata table. Error: %s\n", strerror(errno));
        exit(0);
    }
   
    /*FRAMER_create_hashtable(baseOf_OffsetTable, 
                            total_offset_count,
                            max_ty_count_per_off,
                            max_offset_val,
                            tblentrysize);   
    */
     
    dbg(printf("Table base:\t%p\n", FRAMER_TABLE));
    dbg(printf(" Initialising finishing..\n"));
    //printf("Table base:\t%p\n", FRAMER_TABLE);
    //printf(" Initialising finishing..\n");
}

__attribute__((__used__))
static void FRAMER_exit_main ()
{

//    printf("BIG:\t%d\n", FRAMER_BIG_FRAMED_OBJECT_COUNT);
//    printf("SMALL:\t%d\n", FRAMER_SMALL_FRAMED_OBJECT_COUNT);

//    munmap (FRAMER_TABLE, 
//            FRAMER_metadata_file_size);
//    close(FRAMER_fd);
}

/*
   VoidTyID = 0, HalfTyID,      FloatTyID,      DoubleTyID, 
   X86_FP80TyID, FP128TyID,     PPC_FP128TyID,  LabelTyID, 
   MetadataTyID, X86_MMXTyID,   TokenTyID,      IntegerTyID, 
   FunctionTyID, StructTyID,    ArrayTyID,      PointerTyID, 
   VectorTyID 
*/


__attribute__((__used__))
static void *
FRAMER_xmalloc (size_t size)
{
   void * newmem;
 
   if (size == 0) size = 1;
   newmem = malloc (size);
   
   if (!newmem) exit(0); 
   return newmem;
}

__attribute__((__used__))
static void 
FRAMER_xfree (void *p)
{

    free(p); 
} 


#define ENABLE_INTERPOSE_MALLOC_FAMILY

#endif // USERSHOOK_h_

#ifdef __cplusplus
}
#endif
