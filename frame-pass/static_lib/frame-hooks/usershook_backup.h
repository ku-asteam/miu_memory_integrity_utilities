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
#include <stdbool.h>
#include <signal.h>

#ifndef USERSHOOK_H_
#define USERSHOOK_H_

//#define DEBUG
#ifdef DEBUG
#  define dbg(x) x
#else
#  define dbg(x) 
#endif


extern unsigned FRAMER_tempGVcount;
extern unsigned FRAMER_tempstorecount;
extern unsigned FRAMER_temploadcount;

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



//extern const bool FRAMER_is_bigframe;
//extern const bool FRAMER_is_smallframe;

//extern const unsigned FRAMER_TyIDStart;

/* slot size = 2^15, but slot table is at every 2^16!! */
/*extern const uintptr_t FRAMER_log_slotsize;
extern const uintptr_t FRAMER_num_used_bits_in_ptr;
extern const uintptr_t FRAMER_slot_size;
extern const uintptr_t FRAMER_log_slottable_interval;
*/

//extern const uintptr_t FRAMER_slot_base_mask;
//extern const uintptr_t FRAMER_header_slot_base_mask;


//extern const uintptr_t FRAMER_mask_tag_out;
//extern const uintptr_t FRAMER_flagmask 0x8000000000000000 //(1ULL<<63) 
//extern const uintptr_t FRAMER_mask_only_flag_out;


/* bounds check status */
//extern const int FRAMER_is_inbound;
//extern const int FRAMER_is_outofbound;

/* for BASICType Table*/
//extern const unsigned FRAMER_llvm_BasicTyCount;
//extern const unsigned FRAMER_extra_BasicTyCount;
//extern const unsigned FRAMER_total_BasicTyCount;
//extern int FRAMER_BasicTy_table [FRAMER_llvm_BasicTyCount 
//                        + FRAMER_extra_BasicTyCount]; 
extern int FRAMER_BasicTy_table [22]; 

/* for StructType table */
extern unsigned FRAMER_structTy_count; 
extern StructEntryT* FRAMER_baseOfStructTable;

/* for Metadata table */
extern int FRAMER_fd;
extern int errno;

/*
extern const uintptr_t FRAMER_start_addr_userspace;
extern const uintptr_t FRAMER_end_addr_userspace;

extern const uintptr_t FRAMER_slotbase_of_userspace_start;
extern const uintptr_t FRAMER_slotbase_of_userspace_end;
*/
extern uintptr_t FRAMER_metatable_count;

extern uintptr_t FRAMER_metadata_file_size;

/* TABLES */
// HERE, StructTy ARRAY is inserted by llvm! 
extern HeaderT* FRAMER_PointerTy_Table; 
extern SlotT* FRAMER_TABLE;

// to resolve problem!!
extern char **environ ; 


/*__attribute__((__used__))
//__attribute__((always_inline))
static unsigned FRAMER_get_calloc_elems (unsigned n, unsigned tsize)
{
    unsigned result=0;
    while (result*tsize < sizeof(HeaderT)){
        result++;         
    }
    return result+n;
}*/

__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_determine_log_framesize (void * p, 
                                                        unsigned objsize)
{
    /// framesize only for stack and heap, that are not padded by one byte///
    /// (globals are padded by one byte unlike stack/heap obj) ///

    assert( (((uintptr_t)p <= FRAMER_end_addr_userspace) 
            && ((uintptr_t)(p + (objsize-1))) < FRAMER_end_addr_userspace)
            && "object is out of bound of FRAMER_end_addr_userspace!\n");

    uintptr_t xor_result= ((uintptr_t)p) ^ ((uintptr_t)(p+objsize));
    int myclzl = __builtin_clzl ((unsigned long)xor_result); //TODO: safe cast? 
    int N = 64 - myclzl;
    
    return (uintptr_t)N; 
}
/*
__attribute__((__used__))
//__attribute__((always_inline))
static bool FRAMER_supplementary_isStructTy (unsigned id)
{
    bool is_struct;
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
static bool FRAMER_is_N_tagged (uintptr_t tag) //not TyIDtagged!
{
    /* add assertion that flag  must be 0.*/
    bool isN= false;
    if((tag>>FRAMER_num_used_bits_in_ptr) < FRAMER_TyIDStart) {
        isN= true;
    }
    return isN;
}


__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_get_table_index (uintptr_t slotbase) 
{
    uintptr_t shadow_index = 
        ((slotbase - FRAMER_slotbase_of_userspace_start)
        /(1ULL<<FRAMER_log_slottable_interval));
    return shadow_index; 
}

__attribute__((__used__))
//__attribute__((always_inline))
static bool FRAMER_supplementary_update_entry (
        EntryT* ptr, 
        void* padded_obj_base, 
        uintptr_t N)
{
    bool entry_available = 1;
    EntryT m = *ptr;
    
    if (m.base !=0) {
        entry_available= 0;
    }
    else {
        ptr->base= (void*)padded_obj_base; //save the address of header now!
    }
    
    return entry_available; 
}

__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_get_slotbase_from_untag (uintptr_t p, uintptr_t N) 
{
    uintptr_t slotbase = p & ((~0)<<N);
    assert(N<64 && "check the result if correct..\n");
    return slotbase;   
}

__attribute__((__used__))
//__attribute__((always_inline))
static EntryT* FRAMER_supplementary_get_entry_address (uintptr_t p, uintptr_t N)
{ //p:untagged ptr
   
    //starting from getting a slot base;
    uintptr_t slotbase= FRAMER_supplementary_get_slotbase_from_untag (p, N);
    // get slot index. 
    uintptr_t shadow_index= FRAMER_supplementary_get_table_index(slotbase); 
    //get a pointer 
    SlotT* M= FRAMER_TABLE + shadow_index; 
    EntryT* m= M->slotarray;
    EntryT* myentry= m+(N-FRAMER_log_slottable_interval); 
    dbg(printf("\tslot base:\t%p,\tsizeof(slotT):%lu\n", 
        (void*)slotbase, sizeof(SlotT)));
    
    dbg(printf("\tM:\t%p",M));
    dbg(printf("\tm:\t%p, @entry:%p\n",m,m+(N-FRAMER_log_slottable_interval)));

//    assert(((uintptr_t)FRAMER_TABLE <= (uintptr_t)myentry)
//            && "address of entry is smaller than Framer_table base!\n");
 
//    assert((((uintptr_t)myentry) < 
//            (uintptr_t)(FRAMER_TABLE+(FRAMER_metatable_count*sizeof(SlotT))))
//            && "myentry address is not less than framer_table end.\n");
    return myentry; 
}

__attribute__((__used__))
//__attribute__((always_inline))
static bool FRAMER_supplementary_update_metadata_table (
            void* padded_obj_base, 
            uintptr_t N)
{
    if(N<=15 && N>64){
        printf("Wrong N at updating table. fat_base: %p, N: %" 
                PRIu64 "\n", padded_obj_base,N);
        exit(0);
    }
    
    EntryT* m= FRAMER_supplementary_get_entry_address((uintptr_t)padded_obj_base, N);
       
    // getting a pointer to the entry up to here. 
    bool entry_available = 
        FRAMER_supplementary_update_entry (
                m, 
                padded_obj_base, 
                N); 
  
    return entry_available;    
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_supplementary_update_metadata_header (
            void* padded_obj_base, //untagged 
            unsigned FramerTypeID,
            unsigned raw_object_size)
{
    HeaderT * h =   (HeaderT*)padded_obj_base; 
    dbg(printf("\tupdate HEADER @:\t%p\n", h));
    h->FramerTyID=  FramerTypeID;
    //printf("id: %d\n", h->FramerTyID);
    h->size =       raw_object_size;
    dbg(printf("\tRAW_SIZE:\t%d\n",h->size));
}

__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_cal_offset (void * p)
{
    return (((uintptr_t)p) & 0x7FFF);  
}

/* returns the base of RAW object (after header) */
__attribute__((__used__))
//__attribute__((always_inline))
static void* FRAMER_supplementary_tag_ptr (void * p, uintptr_t tag, bool flag)
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
__attribute__((always_inline))
static bool FRAMER_supplementary_extract_flag (void* p)
{
   // uintptr_t FRAMER_flagmask = ((uintptr_t)1ULL)<<63; //can make it efficient? not important tho. 
    
    if (((uintptr_t)p & FRAMER_flagmask)==FRAMER_flagmask)
    {
        return FRAMER_is_smallframe;
    }
    return FRAMER_is_bigframe; 
}

__attribute__((__used__))
//__attribute__((always_inline))
static HeaderT* FRAMER_supplementary_retrieve_from_header(uintptr_t p, 
                                                    uintptr_t tagvec)
{
    // Actually.. not retrieve from header, but get header address
    uintptr_t slotbase= p & FRAMER_header_slot_base_mask; 
    
    uintptr_t offset= (tagvec & FRAMER_mask_only_flag_out)>>FRAMER_num_used_bits_in_ptr; 
    HeaderT* hd_p = (HeaderT*)(slotbase + offset);
    
    //printf("\tp:%p, offset:%p, slotbase: %p\n", 
    //    (void*)p, (void*)offset, (void*)slotbase); 
    return hd_p;      
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_supplementary_empty_metadata_entry (uintptr_t untagged, 
                                                uintptr_t tagvec)
{
    //get corresponding slot base.
    assert(tagvec!=0 && "tagvec is empty! exiting..\n");
    uintptr_t N= tagvec>>FRAMER_num_used_bits_in_ptr;
    if (N<=15 && N>64) {
        dbg(printf("Wrong N at emptying entry. strippedp: %p, N: %" PRIu64 "\n", (void*)untagged,N);)
        exit(0);
    }
    EntryT* m= FRAMER_supplementary_get_entry_address(untagged, N); 
    //printf("empty. m: %p\n", m); 
    memset (m, 0, sizeof(EntryT)); 
}

__attribute__((__used__))
//__attribute__((always_inline))
static EntryT* FRAMER_supplementary_retrieve_from_table (uintptr_t p, uintptr_t tagvec)
{
    //get corresponding slot base.
    uintptr_t N= tagvec >>FRAMER_num_used_bits_in_ptr;
    EntryT* m= FRAMER_supplementary_get_entry_address(p, N);


    return m;
}

__attribute__((__used__))
//__attribute__((always_inline))
static int FRAMER_supplementary_check_bounds_only (uintptr_t p, 
                                            uintptr_t p_end, //addr+sizeof(type) e.g.) *((int*)p)
                                            void* base, 
                                            int size)
{
    uintptr_t end = (uintptr_t)(base+size-1); // bound.
    int status;

    if ((p >= (uintptr_t)base && p<=end)
        && (p_end >= (uintptr_t)base && p_end<=end)){ //inbound
        status= FRAMER_is_inbound; 
    }
    //else if (p==end){ // is off-by-one
    //    status= FRAMER_is_outofframe; //out-of-bound       
    //}
    else {
    dbg(printf("base addr:\t%p, size: %d\n", base,size);
        printf("p addr:\t%p\n", (void*)p);
        printf("end addr:\t%p\n", (void*)end);
        printf("p_end:\t%p\n", (void*)p_end);
    )
        status= FRAMER_is_outofbound;   
    }
    dbg(printf("\tSTATUS:\t%d\n", status);)
    return status; 
}

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_check_inframe(uintptr_t p, //untagged 
                                        uintptr_t gepbase, //untagged 
                                        uintptr_t logframesize)
{
    return (p&((~0)<<logframesize))^(gepbase &((~0)<<logframesize)); 
    // p's framebase==gepbase' framebase
}

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_extract_tagvec (void* p)
{
    return ((uintptr_t)p) & ~(FRAMER_mask_tag_out);
}

__attribute__((__used__))
__attribute__((always_inline))
static void* FRAMER_supplementary_untag_ptr (void* p)
{
    return (void*)(((uintptr_t)p) & FRAMER_mask_tag_out); 
}

__attribute__((__used__))
//__attribute__((always_inline))
static unsigned FRAMER_supplementary_get_type_size (unsigned tid, unsigned numBytes)
{ 
    assert(tid!=0 && "voidtype is deferefenced?\n");
    // FRAMER_BasicTy_table in bits 
    // numBytes as 
    unsigned tsize=0;
    //do something 
    if (tid== IntegerTyID){ //integerTy has multiple kinds of int types
                            //so, we handle intty first.
        //DOUTFUL. Framer pass is supposed to pass paddedTyID (basicID+int), and why add 6?
        dbg(printf("not supposed to enter here. check. \n");)
        exit(0);
        tsize= FRAMER_BasicTy_table[tid+6]; 
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
    assert(tsize!=0 && "Size of type is 0! Exiting...\n"); 
    dbg(if (tsize==0) {
        printf("tsize is 0 or less than 8 bits!\n"); 
        printf("tid: %u, numBytes: %u\n", tid, numBytes);
        exit(0);
    })
    return tsize/8;
}

__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_suppementary_check_mem_access (
    void * addr,
    unsigned numBytesToAccess,
    short tempinstruction)
{
    uintptr_t tag= FRAMER_supplementary_extract_tagvec (addr); //still having flag 
    if (tag==0) {
        dbg(printf("\ttagless ptr. skip.\n"));
      // find overhead bottleneck
    dbg(if (tempinstruction==tempload) {
           FRAMER_Ntempload++; 
        }
        else if (tempinstruction==tempstore) {
            FRAMER_Ntempstore++;
        }
        else if (tempinstruction==tempmem) {
            FRAMER_Ntempmem++;
        }
        else if (tempinstruction==tempset) {
            FRAMER_Ntempset++;
        }
        else if (tempinstruction==tempstrncat) {
            FRAMER_Ntempstrncat++;
        }
        else if (tempinstruction==tempstrcpy) {
            FRAMER_Ntempstrcpy++;
        }
        else if (tempinstruction==tempstrcmp) {
            FRAMER_Ntempstrcmp++;
        }
        else if (tempinstruction==tempstrncpy) {
            FRAMER_Ntempstrncpy++;
        }
        else if (tempinstruction==tempmemcmp) {
            FRAMER_Ntempmemcmp++;
        }
        else if (tempinstruction==tempmemchr) {
            FRAMER_Ntempmemchr++;
        }
        else {printf("wtf\n"); exit(0);}
    )
      //uptohere  
        
        return addr;     
    } 
    uintptr_t untagged_p= (uintptr_t)FRAMER_supplementary_untag_ptr(addr);
    if (numBytesToAccess==0) {
        return (void*)untagged_p; 
    }
    bool flag= FRAMER_supplementary_extract_flag (addr); 
    
    void* base= NULL;
    int objsize= 0;
    HeaderT* mptr= NULL;
   
    if (flag==FRAMER_is_smallframe) {
        dbg(printf("\tSmall frame\n"));
        mptr= FRAMER_supplementary_retrieve_from_header(untagged_p,tag); //tag still has flag
    }
    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged(tag)) { // big-framed object  
        dbg(printf("\tBig frame\n"));
        EntryT* m = FRAMER_supplementary_retrieve_from_table (untagged_p, tag);
        mptr= (HeaderT*)(m->base); //technically,not base but header!named in the old approach..
    }
    else { 
        /// TypeID is tagged. (flag=big_frame && ID + FRAMER_TyIDStart(100)) //
        // it's using spare bits of big-framed flagged tags 
        ///do something later
        return (void*)untagged_p;    
    }
    objsize = mptr->size;
    base = (void*)mptr + sizeof(HeaderT);

    dbg(printf("\t@hd:\t%p\n", mptr));
    dbg(printf("\tbase:\t%p\n", base));
    dbg(printf("\tsize:\t%d\n", objsize));
     
    assert(((base!=NULL)&&(objsize!=0)) && 
            "Retrieving metadata at store inst failed. \n");
    int is_inbound= 
        FRAMER_supplementary_check_bounds_only (
                untagged_p, // addr to be access
                untagged_p + numBytesToAccess-1, //addr + typesize --> p_end. problem
                base, 
                objsize);

    assert(is_inbound==FRAMER_is_inbound && "out-of-bound\n");
    dbg(if (is_inbound != FRAMER_is_inbound){ 
        printf("\nnumBytesToAccess: %d\n", numBytesToAccess);
        printf("FRAMER ERROR: out-of-bound at mem access\n"
                "\tAddr: %p.\n", (void*)untagged_p);
    })
    return (void*)untagged_p;
}

__attribute__((__used__))
//__attribute__((always_inline))
static bool FRAMER_supplementary_isBigAddr (void *p)
{
    // if upper 16 bits are already used by userprogram, return true.
    bool tagtaken=false;
    uintptr_t result= ((uintptr_t)p) & (~FRAMER_mask_tag_out); 
    if (result!=0) { // 
        tagtaken=true; 
    }
    return tagtaken; 
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_global_variable (
                                    void * taggedPtr, 
                                    unsigned FramerTypeID,  
                                    unsigned numElems, 
                                    unsigned numBytesPerElem,
                                    bool isConstant,
                                    void* mybase, void* myend, //myend not used. delete?
                                    unsigned isPLtokenbuf)
{
    dbg(printf("\nHOOK Global Variable:: \n"));
    dbg(printf("\ttaggedPtr:\t%p\n", taggedPtr));
    dbg(printf("\tnumElems:%d\n", numElems));
    dbg(printf("\tFramerTypeID:%u\n", FramerTypeID));
    
    //printf("GV_%u: %p, n/%u, id/%u, b/%p, e/%p, npe/%u\n", 
    //        FRAMER_tempGVcount, taggedPtr,numElems,FramerTypeID,mybase,myend,numBytesPerElem);
    FRAMER_tempGVcount++;
    
    //printf("\tnumBytesPerEle:\t%d\n",numBytesPerElem);
    //printf("\tmybase:\t%p\n",mybase);
    //printf("\tyend:\t%p\n",myend);
         
    unsigned raw_obj_size= numElems * numBytesPerElem; 
    unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT) + 1; 

    bool flag= FRAMER_supplementary_extract_flag (taggedPtr); 
    uintptr_t tagvec= FRAMER_supplementary_extract_tagvec (taggedPtr); 
    void* untagged_p= FRAMER_supplementary_untag_ptr(taggedPtr);
    void* hd_addr = untagged_p - sizeof(HeaderT); 
    assert(tagvec!=0LL && "Global variable pointers are not tagged!\n");
   
    uintptr_t N_or_offset= (tagvec & FRAMER_mask_only_flag_out)>>FRAMER_num_used_bits_in_ptr; 
    //p: hidden padded_obj_base. header inserted by pass.

    //printf("\tObjectSize_Raw:\t%d\n\tPadded Objsize:\t%d\n", 
    //        raw_obj_size, padded_obj_size);

    // update metadata either in the table or obj header. 
    
    if (flag==FRAMER_is_smallframe) {
        dbg(printf("\tSMALL FRAME\n"));
        dbg(printf("\tsize: %d\n", ((HeaderT*)hd_addr)->size));
    }
    else if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged(tagvec)){ //flag==0
        dbg(printf("\tBIG FRAME\n"));
        //printf("\tN:\t%"PRIuPTR"\n", N_or_offset);
        bool entry_available = 
            FRAMER_supplementary_update_metadata_table(hd_addr,N_or_offset);   
        assert (entry_available 
                &&  "corresponding entry in the table is not 0!"
                    "possibly overlapped allocation?\n"); 
    }
    else { //FramerTyID tagged.(sharing '0' flag with big-framed objects)
        ;
    }
    if (!isConstant) {
        FRAMER_supplementary_update_metadata_header (hd_addr, 
                FramerTypeID,
                raw_obj_size);
    } // Constant global's header is updated at compile time. 
    //TODO: maybe header for ALL GLOBAL can be updated at compile time?

    dbg(printf("exiting hook global\n"));
}

__attribute__((__used__))
//__attribute__((always_inline))
static void* FRAMER_forall_alloca (void * thinBase, 
                            unsigned numElems,
                            unsigned FramerTypeID, 
                            unsigned numBytesPerElem)
                            //void* locationOfFramerTyEntry)
{    
    dbg(printf ("HOOK Alloca\n"));
    dbg(printf("\tAddr Of Obj:\t%p\n", thinBase));
    dbg(printf("\t#Elems:\t%d\n", numElems));
    dbg(printf("\tTypeID:\t%d\n", FramerTypeID));

    if (FRAMER_supplementary_isBigAddr(thinBase)){
        dbg(printf("ALLOCA isBigAddr: %p\n", thinBase);)
        exit(0);
    } 
    void* tagged_p= NULL;    
    void* fatbase= thinBase - sizeof(HeaderT); //header address
    
    dbg(printf("\theader addr:\t%p, size: %d\n", fatbase));
    
    unsigned raw_obj_size = numElems*numBytesPerElem;
    unsigned padded_obj_size = sizeof(HeaderT)+raw_obj_size;
    
    //printf("\traw size:\t%d\n", raw_obj_size);
    //printf("\tHeader addr:\t%p\n", p);

    uintptr_t N= FRAMER_supplementary_determine_log_framesize (fatbase, padded_obj_size);  
    uintptr_t tag=0;
    bool whichframe;
    dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));

    // update metadata in the obj header, but for big-framed obj, update entry also.(@header) 
    if (N > FRAMER_log_slotsize) {
        dbg(printf("\tbig frame\n"));

        bool entry_available = 
            FRAMER_supplementary_update_metadata_table (fatbase, N);   
        
        assert (entry_available 
                && "corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n"); 
        tag= N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        dbg(printf("\tsmall\n"));
        
        tag= FRAMER_supplementary_cal_offset(fatbase);
        whichframe= FRAMER_is_smallframe; 
    }
    FRAMER_supplementary_update_metadata_header(fatbase, 
                                                FramerTypeID,
                                                raw_obj_size);
    tagged_p = FRAMER_supplementary_tag_ptr(fatbase, 
                                            tag, 
                                            whichframe);     
    
    tagged_p= tagged_p + sizeof(HeaderT);

    //dbg(printf("exiting alloca. tagged: %p\n", tagged_p));
    return tagged_p;
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_getelementptr (void * GEP, 
                                    void * baseOfGEP, 
                                    unsigned srcFramerTyID, 
                                    unsigned resultFramerTyID)
{
    dbg(printf("\nHOOK GEP\n"));
    dbg(printf("\tGEP:\t%p\n",    GEP)); 
    dbg(printf("\tbaseP:\t%p\n",  baseOfGEP)); 
  /*  
    printf("\tsrcFramerTid:\t%d\n",     srcFramerTyID); 
    printf("\tresultFramerTid:\t%d\n",  resultFramerTyID); 
  */ 
    uintptr_t tagvec= FRAMER_supplementary_extract_tagvec (GEP); 
    if (tagvec==0) {
        return;
    }
   
    bool flag= FRAMER_supplementary_extract_flag (GEP); 
    uintptr_t untagged_p= (uintptr_t)FRAMER_supplementary_untag_ptr(GEP);
    uintptr_t untagged_gepbase= (uintptr_t)FRAMER_supplementary_untag_ptr(baseOfGEP); 
         
    uintptr_t logframesize=0;
    
    if (flag==FRAMER_is_bigframe && FRAMER_is_N_tagged(tagvec)){ //n>15
       logframesize= tagvec>>FRAMER_num_used_bits_in_ptr;
    }
    else if(flag==FRAMER_is_smallframe){
        logframesize= FRAMER_log_slotsize;
    }
    else { //tag is just typeID (flag==is_bigframe)
        return;
    }
    uintptr_t is_inframe= FRAMER_supplementary_check_inframe (untagged_p, 
                                                        untagged_gepbase, 
                                                        logframesize);
    assert(is_inframe==0 && "out of frame\n");
/*    if (is_inframe!=0) { 
        printf("A pointer get beyond its frame by pointer arithmetic.\n"); 
        printf("  GEP: %p, untaggedbase: %p, framesize: %"PRIu64 "\n", 
            (void*)GEP, (void*)untagged_gepbase, logframesize);
        HeaderT* mptr= FRAMER_supplementary_retrieve_from_header (untagged_gepbase, tagvec);
        printf("   objsize: %u\n", mptr->size); 
        exit(0); 
    } */
}

__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_store ( 
                        void * addr, //destAddress, 
                        unsigned FramerTypeID, //enum BASICType ValueTy,
                        unsigned numBytesOfSrcTy,
                        unsigned isTheFunc) //S_study_chunk 
{
    dbg(printf ("\nHOOK STORE\n"));
    dbg(printf("\tDest Addr:\t%p\n", addr)); 
    dbg(printf("\tFramerTypeID:\t%u\n", FramerTypeID));
    FRAMER_tempstorecount++;
    unsigned numBytes= 
        FRAMER_supplementary_get_type_size(FramerTypeID, numBytesOfSrcTy); 
    
    assert(numBytes!=0 && "store. numBytes is 0\n"); 
    dbg(printf("\tFramerTySIZE:\t%u\n", numBytes));
    
    dbg(if (numBytes==0) {
        printf("STORE: numbytes 0\n"); 
        printf("addr: %p, FramerTyID: %u, numBytesOfSrcTy: %u\n", 
                addr, FramerTypeID, numBytesOfSrcTy);
        exit(0);
    })
    return FRAMER_suppementary_check_mem_access(addr, numBytes, tempstore);
}

__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_load (void * addr, 
                        unsigned FramerTypeID, 
                        unsigned numBytesOfLoadedContent)
                          /*when we meet p_content = load <pointerty> p, 
                            p must be pointer, and p_contenr may be or not.
                            addrToBeloaded: p , resultTy: a type of p_content */ 
{
    dbg(printf("\nHOOK LOAD\n"));
    dbg(printf("\taddr:\t%p,\n", addr));
   
    //printf("<L,%p,%u, %u>\n",addr,FramerTypeID, numBytesOfLoadedContent);
    FRAMER_temploadcount++; 
    unsigned numBytes= 
        FRAMER_supplementary_get_type_size(FramerTypeID, numBytesOfLoadedContent); 

    assert(numBytes!=0 && "load. numBytes is 0\n"); 
    dbg(if (numBytes==0) {
        printf("LOAD: numbytes 0. \n"); 
        printf("addr: %p, FramerTyID: %u, numBytes: %u\n", 
                addr, FramerTypeID, numBytesOfLoadedContent);
        exit(0);
    })
    return FRAMER_suppementary_check_mem_access(addr, numBytes, tempload); 
}

__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_llvm_memtransfer (

    void * addr, 
    uint64_t numBytesToCopy, 
    unsigned numAlign, 
    _Bool isVolatile )
{
    //assert(numAlign<=16 && "FRAMER assumes alignment is <=16!\n"); 
    //assert(numBytesToCopy!=0 && "FRAMER ERROR: 0 bytes to transfer!"); 

    return FRAMER_suppementary_check_mem_access (
        addr, numBytesToCopy, tempmem); 
}

/*
__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_strlentemp (void * addr)
{ 
    char* mystr= (char*)FRAMER_supplementary_untag_ptr(addr);
    return FRAMER_supplementary_untag_ptr(addr);
}
__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_strchr (void * addr, int mychar)
{ 
    return FRAMER_supplementary_untag_ptr(addr);
}*/
//perlbench

/*
__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_strn___ (void * addr, uint64_t numBytes)
{ 
    // memchr
    if (numBytes==0) {
        return FRAMER_supplementary_untag_ptr(addr); 
    }
    dbg(printf ("HOOK strn___ generic!\n"));
    return FRAMER_suppementary_check_mem_access(addr, numBytes); 
}*/

__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_llvm_memset(void * addr,
                                    signed char val,
                                    uint64_t numBytesToCopy, 
                                    unsigned numAlign, 
                                    _Bool isVolatile )
{
    dbg(printf("HOOK MEM SET \n"));
   //printf("HOOK MEM SET \n");
    
    assert(numAlign <= 16 && "FRAMER assumes memset alignment is <=16!\n"); 
    assert((numBytesToCopy!=0) && "FRAMER ERROR: 0 bytes to memset!"); 
  //  if (numBytesToCopy==0) {
  //      return FRAMER_supplementary_untag_ptr(addr); 
  //  }
    return FRAMER_suppementary_check_mem_access (
            addr, numBytesToCopy, tempset); 
}

/*
__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_forall_call_strcpy (void * dest, void * src) 
{
    // 1. get objsize (dest) strlen(src) 
    // 2. check dest + strlen(str) (+1?) < dest_end
    // then return untagged_dest. (untagging src is handled in untag hook)
    
   //printf("HOOK strcpy. addr: %p\n", src); 
    size_t srclen= strlen((const char*)FRAMER_supplementary_untag_ptr(src)); // +1?; 
    
    printf("strcpy. dest: %p\n",dest);
    printf("  src: %p, srclen: %" PRIu64 "\n", src, srclen);
    printf("  src str: %s\n", (char*)FRAMER_supplementary_untag_ptr(src));
    
    assert(srclen!=0 && "FRAMER ERROR: srclen is 0!"); 
    
    return FRAMER_suppementary_check_mem_access (
            dest, srclen); 
}*/



/*
/////////////from here. do check
__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_lshr ( int64_t operand_0, 
                        int64_t operand_1, 
                        int64_t numBytesOfIntType)
{
    dbg(printf("HOOK lshr hook.\n"));
}
*/
/*
__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_ptrtoint (void *   ptrToBeConvertedToInt, 
        unsigned addressSpaceOfPtr, 
        unsigned numBytesOfDestType, 
        uint64_t resultOfPtrToInt)
{
    dbg(printf("HOOK Ptr To Int \n"));
    dbg(printf("\tptrToBeConvertedToInt: %p\n", ptrToBeConvertedToInt));
    dbg(printf("\tnumBytesOfDestType: %d\n", numBytesOfDestType));
    dbg(printf("\tresultOfPtrToInt: %" PRIu64 "\n", resultOfPtrToInt));

}

__attribute__((__used__))
//__attribute__((always_inline))
static uint64_t FRAMER_forall_inttoptr ( uint64_t intToBeConvertedToPtr, 
        //unsigned numBytesOfInt, 
        unsigned addresSpaceOfPtr, 
        void *   resultOfIntToPtr)
{
   dbg(printf("HOOK Int To Ptr\n"));
   //dbg(printf("\tintToBeConvertedToPtr: %" PRIu64 "\n", intToBeConvertedToPtr));
   //dbg(printf("\tresultOfIntToPtr: %p\n", resultOfIntToPtr));

    return intToBeConvertedToPtr;
}
//////////// upto here

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_bitcast (unsigned sourceTypeID, 
                            unsigned targetTypeID, 
                            unsigned numBytes)// , 
                           // void * addressBitCasted)
{
    dbg(printf("HOOK bitcast. do nothing..\n"));
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_addop (int64_t operand_0, 
                        int64_t operand_1) 
                       // int64_t numBytesOfIntType)
{
    //printf("  Op0: %" PRIi64 ", op0(uint): %" PRIu64 "\n", operand_0,(uint64_t)operand_0);
    //printf("  Op1: %" PRIi64 ", op1(uint): %" PRIu64 "\n", operand_1,(uint64_t)operand_1);
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_subop (int64_t operand_0, 
                        int64_t operand_1, 
                        int64_t numBytesOfIntType)
{
    //printf("Sub\n");
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_forall_mulop (int64_t operand_0, 
                        int64_t operand_1, 
                        int64_t numBytesOfIntType)
{
    //printf("Mul\n");
}
*/

/* not used
__attribute__((__used__))
//__attribute__((always_inline))
static uintptr_t  FRAMER_supplementary_subtract(uintptr_t x, uintptr_t y)
{
    // Iterate till there is no carry
    while (y != 0)
    {
        // borrow contains common set bits of y and unset
        // bits of x
        uintptr_t borrow = (~x) & y;

        // Subtraction of bits of x and y where at least
        // one of the bits is not set
        x = x ^ y;

        // Borrow is shifted by one so that subtracting it from
        // x gives the required sum
        y = borrow << 1;
    }
    return x;
}
*/

//void FRAMER_func_epilogue (void* tagged)
//__attribute__((always_inline))
__attribute__((__used__))
static void FRAMER_reset_entries_for_alloca (void* tagged) 
{
    dbg(printf("reset entries\n"));
    if (FRAMER_supplementary_extract_flag(tagged)==FRAMER_is_smallframe) {
        return;
    }
    
    uintptr_t untagged_p= (uintptr_t)FRAMER_supplementary_untag_ptr(tagged);
    uintptr_t tagvec= FRAMER_supplementary_extract_tagvec (tagged); 

    FRAMER_supplementary_empty_metadata_entry (untagged_p, tagvec);
}

/*
__attribute__((__used__))
//__attribute__((always_inline))
static void * FRAMER_allocAddressSpace (size_t mysize)
{
    void * ptr= mmap (0, 
                     mysize, 
                     PROT_NONE,
                     MAP_PRIVATE | MAP_ANONYMOUS, 
                     -1,//FRAMER_fd, 
                     (off_t)0);
    if (ptr == MAP_FAILED) {
        printf ("ERROR: %s. (mmap error for metadata table.)\n", strerror(errno));
        exit(0);
    }
    msync(ptr, mysize, MS_SYNC|MS_INVALIDATE);
    return ptr;
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_commitMemory() 
{
    printf("In commitMemory..\n");
    size_t page_size= sysconf(_SC_PAGE_SIZE);
    FRAMER_TABLE= mmap (FRAMER_TABLE, 
                        page_size, 
                        PROT_READ|PROT_WRITE, 
                        MAP_FIXED|MAP_SHARED|MAP_ANON, 
                        -1, 
                        0);
    msync(FRAMER_TABLE, page_size, MS_SYNC|MS_INVALIDATE);
}
__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_decommitMemory()
{
    // instead of unmapping the address, we're just gonna trick 
    // the TLB to mark this as a new mapped area which, due to 
    // demand paging, will not be committed until used.
    printf("inside DecommitMemory..\n");
    mmap(FRAMER_TABLE, 
        FRAMER_metadata_file_size, 
        PROT_NONE, 
        MAP_FIXED|MAP_PRIVATE|MAP_ANON, 
        -1, 
        0);
    msync (FRAMER_TABLE, 
          sysconf(_SC_PAGE_SIZE), 
          MS_SYNC|MS_INVALIDATE);
}

__attribute__((__used__))
//__attribute__((always_inline))
static void FRAMER_freeAddressSpace()
{
    printf ("inside FreeAddressSpace..\n");
    msync(FRAMER_TABLE, FRAMER_metadata_file_size, MS_SYNC);
    munmap(FRAMER_TABLE, FRAMER_metadata_file_size);
}
*/

//__attribute__((always_inline))
__attribute__((__used__))
static void FRAMER_do_initializing(unsigned numStructTyCount, 
                    void* baseOf_StructTable)
{
    /*int ret= signal(SIGBUS, FRAMER_myPageFaultHandler);
    if(ret == SIG_ERR) {
        printf("Error: unable to set FRAMER_myPageFaultHandler.\n");
        exit(0);
    }*/

    FRAMER_structTy_count= numStructTyCount;
    FRAMER_baseOfStructTable= baseOf_StructTable; 
    FRAMER_metadata_file_size = FRAMER_metatable_count
                                *sizeof(SlotT);
                                //*FRAMER_each_metaTable_entry_count
    //printf("\n***** Initialising *************\n");
    dbg(printf("\n***** Initialising *************\n"));
    dbg(printf("HeaderT size:\t%d\n", sizeof(HeaderT)));
    dbg(printf("#Struct types:\t%u\n", numStructTyCount));
    dbg(printf("StructBasicTybase:\t%p\n", baseOf_StructTable));
    dbg(printf("U_space base:\t%p\n", 
        FRAMER_slotbase_of_userspace_start));
     
    //FRAMER_supplementary_setup_FRAMER_BasicTy_table();
    assert (FRAMER_llvm_BasicTyCount+ FRAMER_extra_BasicTyCount==23
            && "Assert failed: Framer BasicTyCounts do not fit!\n");

    //size_t page_size= sysconf(_SC_PAGE_SIZE); 
    environ = NULL;
     
    // void * ptr = mmap((void*)0, size, PROT_NONE, MAP_PRIVATE|MAP_ANON, -1, 0);
    FRAMER_TABLE= (SlotT*)mmap (0, 
                                ((size_t)FRAMER_metadata_file_size),
                                PROT_READ | PROT_WRITE | PROT_NONE,
                                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, 
                                -1,//FRAMER_fd, 
                                (off_t)0);
   // FRAMER_TABLE= (SlotT*)FRAMER_allocAddressSpace(FRAMER_metadata_file_size); 
     
    if (FRAMER_TABLE == MAP_FAILED) {
        printf ("ERROR:mmap error for metadata table. Error: %s\n", strerror(errno));
        exit(0);
    }
    
    dbg(printf("Table base:\t%p\n", FRAMER_TABLE));
    dbg(printf("FRAMER_metatable_count: %"PRIuPTR"\n", FRAMER_metatable_count));
    dbg(printf(" Initialising finishing..\n"));
   // printf("Table base:\t%p\n", FRAMER_TABLE);
   // printf("Table + FRAMER_metatable_count:\t%p\n", FRAMER_TABLE+FRAMER_metatable_count);
    //printf(" Initialising finishing..\n");
    
}
/*
__attribute__((__used__))
static void FRAMER_exit_main ()
{
    munmap (FRAMER_TABLE, 
            FRAMER_metadata_file_size);
    close(FRAMER_fd);
}*/

__attribute__((__used__))
static void FRAMER_exit_main ()
{
    munmap (FRAMER_TABLE, 
            FRAMER_metadata_file_size);
    close(FRAMER_fd);
}

/*
   VoidTyID = 0, HalfTyID,      FloatTyID,      DoubleTyID, 
   X86_FP80TyID, FP128TyID,     PPC_FP128TyID,  LabelTyID, 
   MetadataTyID, X86_MMXTyID,   TokenTyID,      IntegerTyID, 
   FunctionTyID, StructTyID,    ArrayTyID,      PointerTyID, 
   VectorTyID 
*/

#endif // USERSHOOK_h_

