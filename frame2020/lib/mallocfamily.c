//#define CPP

#ifdef __cplusplus
extern "C"
{
#endif


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "./framertypes.h"
//#include "malloc.h"

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
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

//#define DISABLE_ALL_CHECKS

//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
//%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

extern void FRAMER_update_header (
        void* padded_obj_base, 
        int FramerTypeID,
        unsigned raw_object_size
    #ifdef ENABLE_SPACEMIU
    
      #ifdef ENABLE_TRACK_ARRAYS
        ,unsigned numBytesPerElem
      #endif
        ,FRAMER_Bool_ isUnionTy
    #endif
        );

extern unsigned FRAMER_decide_log_framesize (
        void * p, 
        unsigned objsize);

extern FRAMER_Bool_ FRAMER_update_table (
        void* padded_obj_base, 
        unsigned N);

#ifndef ENABLE_SPACEMIU
extern void * FRAMER_check_mem_access (
        void * addr,
        unsigned numBytesToAccess); 

extern uintptr_t 
FRAMER_supplementary_check_inframe(uintptr_t p, //untagged 
                                   uintptr_t gepbase, //untagged 
                                   unsigned logframesize);
#endif

extern void* FRAMER_supplementary_tag_ptr (
        void * p, 
        uintptr_t tag, 
        FRAMER_Bool_ flag);

extern uint64_t FRAMER_untag_ptr (void * p);

extern uintptr_t FRAMER_extract_tagvec (void* p); 

extern uintptr_t FRAMER_supplementary_cal_offset (void * p);

extern FRAMER_Bool_ FRAMER_supplementary_extract_flag (void* p);


#ifndef ENABLE_SPACEMIU
extern void FRAMER_empty_metadata_entry (
            uintptr_t untagged, uintptr_t tagvec);
#endif

dbg(extern FRAMER_Bool_ FRAMER_supplementary_isBigAddr (void *p);)
// up to here



__attribute__((__used__))
static unsigned 
FRAMER_get_calloc_elems (unsigned n, 
                         unsigned tsize)
{
    unsigned result=0;
    while (result*tsize < sizeof(HeaderT)){
        result++;         
    }
    return result+n;
}

////
/// This malloc wrapper is interposed at compiler preprocessor.
/// currently FRAMER_forall_malloc in usershook.h in action.
////
/*
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
void * FRAMER_malloc (size_t allocatedSizeInBytes)
{
#ifdef DISABLE_ALL_CHECKS
 
    return malloc(allocatedSizeInBytes);
 
#else  

    dbg(
      printf("\nHOOK Malloc\n");
    )

    unsigned raw_obj_size = (unsigned) allocatedSizeInBytes; 
    assert_dbg(assert ((size_t)raw_obj_size == allocatedSizeInBytes
            && "The size of malloc should be type-upgraded!\n");) 
    assert ((size_t)raw_obj_size == allocatedSizeInBytes);
    unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT); 
    //allocating
    void * p = malloc(padded_obj_size);
    assert (p!=NULL);
   
    dbg(if (FRAMER_supplementary_isBigAddr(p)){
        printf("Malloc isBigAddr: %p\n", p);
        exit(0);
    })

    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, raw_obj_size, padded_obj_size));
    
    // initialising buffer 
//    memset (p, 0, padded_obj_size); 
    
    unsigned N = FRAMER_decide_log_framesize (p, padded_obj_size);  
    dbg(printf("\tLog(Frame):\t%d\n", N));

    uintptr_t tag=0;
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
        } )
        
        assert (entry_available); 
        
        tag= (uintptr_t)N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
    
  #ifdef ENABLE_SPACEMIU    
    int heapTID= FRAMER_is_heap_obj; 
//    if (raw_obj_size == 1) {
//        heapTID= FRAMER_IS_CHAR_TYPE;  
//    }
//
    FRAMER_update_header(p, heapTID, raw_obj_size, 

    #ifdef ENABLE_TRACK_ARRAYS
      raw_obj_size, 
    #endif
    
    false); 
  
  #else    
 
    FRAMER_update_header(p, VoidTyID, raw_obj_size);

  #endif    
    
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
 
    assert(tagged_p != 0);
     
    return ((char*)tagged_p + sizeof(HeaderT));
#endif 
}
*/

void *
FRAMER_malloc_array(size_t ty, size_t elem)
{
    printf("HOOK FRAMER MALLOC ARRAY\n");
    printf("\tty size: %lu\n", ty);
    printf("\telemNum: %lu\n", elem);
    return malloc (ty*elem);
}

/*
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
//__attribute__((always_inline))
void FRAMER_free (void* obj_base)
{
    // e.g) free (mymalloc)  
    // get entry location (if N>16) 
    //check entry

  #ifdef DISABLE_ALL_CHECKS
    free(obj_base);
  #else  

    dbg(printf("\nHOOK Free\n"));
    dbg(printf("\tthin_p: %p\n", obj_base));
    
    if (obj_base==0) {
        
        return;
    }
    FRAMER_Bool_ flag= FRAMER_supplementary_extract_flag (obj_base); 
    uintptr_t untagged_p= 
    //    FRAMER_untag_ptr_int((uintptr_t)obj_base);
        FRAMER_untag_ptr(obj_base);
    
    
    uintptr_t tagvec= FRAMER_extract_tagvec(obj_base);
    uintptr_t hidden_actual_base = untagged_p - sizeof(HeaderT);
   
    if (tagvec==0){ 
        
        free((void*)obj_base);
        return; 
    }

    //printf("\ttagged obj_base:\t%p\n", obj_base);
    //printf("\ttagged hidden_base:\t%p\n", hidden_actual_base);

    #ifndef ENABLE_SPACEMIU
      if (flag==FRAMER_is_bigframe){ 
        FRAMER_empty_metadata_entry (hidden_actual_base, tagvec);
      }
      assert_dbg(assert((HeaderT*)hidden_actual_base!=NULL 
              && "Header is NULL at free! Double free?\n");)
    #endif

    assert((HeaderT*)hidden_actual_base!=NULL);
    dbg(printf("\tpadded_p: %p\n", (void*)hidden_actual_base));
    
    free((void*)hidden_actual_base);
  
  #endif
}
*/

/*
/// commented out for spacemiu interposing realloc with framer pass
///
#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
void * FRAMER_realloc(void* thin_base, size_t size)
{

#ifdef DISABLE_ALL_CHECKS
    return realloc(thin_base, size);
#else  

    dbg(printf("\nHOOK realloc\n"));
    //printf("\nHOOK realloc\n");
    
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
    
    assert(tagvec!=0);
      
    dbg(if (tagvec==0) {
        printf("\tError: Not tagged. CHECK. thin_base: %p\n", thin_base);
        exit(0);
    })
    // 1.get hidden base
    FRAMER_Bool_ flag= FRAMER_supplementary_extract_flag (thin_base); 
    uintptr_t untagged_p= 
        //FRAMER_untag_ptr_int((uintptr_t)thin_base);
        FRAMER_untag_ptr(thin_base);
    uintptr_t padded_base = untagged_p - sizeof(HeaderT);
    // get padded_size 
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
   // memset (p, 0, padded_obj_size); 
     
    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%lu\n", 
        p, size, padded_obj_size));
    //printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        //p, size, padded_obj_size);
    // 3. do the rest like malloc with returned ptr, and return ptr to the beginning of actual object.
    
    uintptr_t N = (uintptr_t)FRAMER_decide_log_framesize (p, padded_obj_size);  
    //dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));
    
    uintptr_t tag=0;
    FRAMER_Bool_ whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    
    if (N > FRAMER_log_slotsize) {
        //dbg(printf("BIG FRAME. realloc\n"));
        
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
    int heapTID= FRAMER_is_heap_obj; 
//    if (size == 1) {
//        heapTID= FRAMER_IS_CHAR_TYPE;  
//    }
//
    FRAMER_update_header(p, heapTID, size, 

 #ifdef ENABLE_TRACK_ARRAYS
    size, 
 #endif
    
    false);
#else
    FRAMER_update_header(p, VoidTyID, size);
#endif

    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
    assert(tagged_p!=0);
     
    //printf("Realloc. thin_b:%p, fat_b: %p\n", (void*)tagged_p+sizeof(HeaderT),p);
    
    return ((char*)tagged_p+sizeof(HeaderT)); 

    // 4. change the option for linker (add wrap realloc)
    // 5. add checking if there's calloc (What else) call in framer.cpp
  #endif
}
*/

#ifdef ISOLATE_CALCULATION_OF_HEADER
__attribute__((noinline))
#endif
void *FRAMER_calloc(size_t elems, size_t elemsize)
{

#ifdef DISABLE_ALL_CHECKS
  return calloc(elems, elemsize);
#else  

  #ifndef ENABLE_TRACK_ARRAYS
    return calloc(elems, elemsize);
  #else 

    unsigned raw_obj_size = (unsigned) elems*elemsize; 
    //unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT); 
    unsigned pad_elems= FRAMER_get_calloc_elems(elems,elemsize);
    dbg(printf("n: %u, tsize: %u, new_n: %u, HeaderT: %u\n", 
            elems, elemsize, pad_elems, sizeof(HeaderT));) 
    unsigned padded_obj_size=pad_elems*elemsize; 
    
    //allocating
    void * p = calloc(pad_elems, elemsize);
    assert_dbg(assert ((p!=NULL) && "Null returned from calloc. Exiting...\n");)
    assert (p!=NULL);
    
    assert_dbg(assert (!FRAMER_supplementary_isBigAddr(p) 
                && "calloc isBigAddr\n");)
    dbg(if (FRAMER_supplementary_isBigAddr(p)){
        printf("calloc isBigAddr: %p\n", p);
        exit(0);
    })

    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, raw_obj_size, padded_obj_size));
    
    // initialising buffer 
    memset (p, 0, padded_obj_size); 
    
    uintptr_t N = (uintptr_t)FRAMER_decide_log_framesize (p, padded_obj_size);  
    //dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));

    uintptr_t tag=0;
    FRAMER_Bool_ whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    if (N > FRAMER_log_slotsize) {
 
        FRAMER_Bool_ entry_available = 
            FRAMER_update_table (p, N); 
        assert_dbg(assert (entry_available 
                && "malloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n");) 
        assert (entry_available); 
        
        tag= N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }

////////////// ODD!  
  #ifdef ENABLE_SPACEMIU
    int heapTID= FRAMER_is_heap_obj; 
    
/*    if (raw_obj_size == 1) {
        heapTID= FRAMER_IS_CHAR_TYPE;  
    } 
*/
    FRAMER_update_header(p, FRAMER_is_heap_obj, raw_obj_size, false);
  #else
    FRAMER_update_header(p, VoidTyID, raw_obj_size);
  #endif
//////////////////

    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
    
    dbg(printf("\tthin_p:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));

    return ((char*)tagged_p + sizeof(HeaderT));
  
  #endif // of ifndef ENABLE_TRACK_ARRAYS

#endif //DISABLE_ALL_CHECKS 

}



#ifdef __cplusplus
} // extern "C"
#endif
