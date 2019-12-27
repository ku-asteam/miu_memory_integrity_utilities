//#define CPP

#ifdef CPP 
extern "C" {
#endif


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "./framertypes.h"

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

/* heap allocation functions */
/*
void *__real_malloc(size_t size);
void __real_free(void *ptr);
void *__real_realloc(void *ptr, size_t size);
void *__real_calloc(size_t elems, size_t elemsize);
*/

/* string functions */
char * __real_strcpy (char * dest, char *src);
int __real_strcmp   (char * str1, char * str2);
int __real_strncmp  (char *str1, char *str2, size_t n);
char *__real_strncpy    (char * dest,char * src,size_t n);
int __real_memcmp       (void *str1, void *str2, size_t n);
void * __real_memchr    (void *str, int c, size_t n);
char * __real_strchr    (char *str, int c);
char * __real_strncat   (char *dest, char *src, size_t n); 
long int __real_strtol  (const char *str, char **endptr, int base); 


// hooks.h
//extern const uintptr_t FRAMER_header_slot_base_mask; 
//extern const uintptr_t FRAMER_mask_tag_out;

//extern const bool FRAMER_is_bigframe;
//extern const bool FRAMER_is_smallframe;

//extern const uintptr_t FRAMER_log_slotsize;

/*
extern void FRAMER_update_header (
        void* padded_obj_base, 
        int FramerTypeID,
        unsigned raw_object_size
    #ifdef ENABLE_SPACEMIU
    
      #ifdef ENABLE_TRACK_ARRAYS
        ,unsigned numBytesPerElem
      #endif

        ,bool isUnionTy
    #endif
        );

extern unsigned FRAMER_decide_log_framesize (
        void * p, 
        unsigned objsize);

extern bool FRAMER_update_table (
        void* padded_obj_base, 
        unsigned N);
*/

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
        bool flag);

extern uint64_t FRAMER_untag_ptr (void * p);

extern uintptr_t FRAMER_extract_tagvec (void* p); 

extern uintptr_t FRAMER_supplementary_cal_offset (void * p);

extern bool FRAMER_supplementary_extract_flag (void* p);

#ifndef ENABLE_SPACEMIU
extern void FRAMER_empty_metadata_entry (
            uintptr_t untagged, uintptr_t tagvec);
#endif

dbg(extern bool FRAMER_supplementary_isBigAddr (void *p);)
// up to here



__attribute__((__used__))
//__attribute__((always_inline))
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

/*
void *__wrap_malloc(size_t allocatedSizeInBytes)
{
#ifdef DISABLE_ALL_CHECKS
 
    return  __real_malloc(allocatedSizeInBytes);
 
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
    void * p = __real_malloc(padded_obj_size);
    assert (p!=NULL);
   
    dbg(if (FRAMER_supplementary_isBigAddr(p)){
        printf("Malloc isBigAddr: %p\n", p);
        exit(0);
    })

    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, raw_obj_size, padded_obj_size));
    
    // initialising buffer 
    memset (p, 0, padded_obj_size); 
    
    unsigned N = FRAMER_decide_log_framesize (p, padded_obj_size);  
    dbg(printf("\tLog(Frame):\t%d\n", N));

    uintptr_t tag=0;
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;

    if (N > FRAMER_log_slotsize) {
 
        bool entry_available = 
            FRAMER_update_table (p, N); 
        assert_dbg(assert (entry_available 
                && "malloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n");) 
        
        if (entry_available==0) {
            printf(">> N: %d, p: %p\n", N, p);           
        }
        
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
     
    dbg(printf("\tthin_p:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));

    return ((char*)tagged_p + sizeof(HeaderT));
#endif 
}


//__attribute__((always_inline))
void __wrap_free (void* obj_base)
{
    // e.g) free (mymalloc)  
    // get entry location (if N>16) 
    //check entry

  #ifdef DISABLE_ALL_CHECKS
    __real_free(obj_base);
  #else  

    dbg(printf("\nHOOK Free\n"));
    dbg(printf("\tthin_p: %p\n", obj_base));
    if (obj_base==0) {
        return;
    }
    bool flag= FRAMER_supplementary_extract_flag (obj_base); 
    uintptr_t untagged_p= 
    //    FRAMER_untag_ptr_int((uintptr_t)obj_base);
        FRAMER_untag_ptr(obj_base);
    
    
    uintptr_t tagvec= FRAMER_extract_tagvec(obj_base);
    uintptr_t hidden_actual_base = untagged_p - sizeof(HeaderT);
   
    if (tagvec==0){ 
        //__real_free((void*)hidden_actual_base);
        __real_free((void*)obj_base);
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
    
    __real_free((void*)hidden_actual_base);
  
  #endif
}



void *__wrap_realloc(void* thin_base, size_t size)
{

#ifdef DISABLE_ALL_CHECKS
    return __real_realloc(thin_base, size);
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
        return __real_realloc(thin_base, size);
      }
    #endif
  
  #endif
    
    assert(tagvec!=0);
      
    dbg(if (tagvec==0) {
        printf("\tError: Not tagged. CHECK. thin_base: %p\n", thin_base);
        exit(0);
    })
    // 1.get hidden base
    bool flag= FRAMER_supplementary_extract_flag (thin_base); 
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
    void * p = __real_realloc((void*)padded_base, padded_obj_size);
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
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    
    if (N > FRAMER_log_slotsize) {
        //dbg(printf("BIG FRAME. realloc\n"));
        
        bool entry_available = 
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
     
    dbg(printf("\tnew thin_b:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));
    
    //printf("Realloc. thin_b:%p, fat_b: %p\n", (void*)tagged_p+sizeof(HeaderT),p);
    
    return ((char*)tagged_p+sizeof(HeaderT)); 

    // 4. change the option for linker (add wrap realloc)
    // 5. add checking if there's calloc (What else) call in framer.cpp
  #endif
}

void *__wrap_calloc(size_t elems, size_t elemsize)
{

#ifdef DISABLE_ALL_CHECKS
  return __real_calloc(elems, elemsize);
#else  

  #ifndef ENABLE_TRACK_ARRAYS
    return __real_calloc(elems, elemsize);
  #else 

    unsigned raw_obj_size = (unsigned) elems*elemsize; 
    //unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT); 
    unsigned pad_elems= FRAMER_get_calloc_elems(elems,elemsize);
    dbg(printf("n: %u, tsize: %u, new_n: %u, HeaderT: %u\n", 
            elems, elemsize, pad_elems, sizeof(HeaderT));) 
    unsigned padded_obj_size=pad_elems*elemsize; 
    
    //allocating
    void * p = __real_calloc(pad_elems, elemsize);
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
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    if (N > FRAMER_log_slotsize) {
 
        bool entry_available = 
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
    
//    if (raw_obj_size == 1) {
//        heapTID= FRAMER_IS_CHAR_TYPE;  
//    } 
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

*/

char *__wrap_strcpy(char * dest, char * src)
{
    // 1. get objsize (dest) strlen(src) 
    // 2. check dest + strlen(str) (+1?) < dest_end
    // then return untagged_dest. (untagging src is handled in untag hook)

  #ifndef ENABLE_SPACEMIU

    char * untagsrc= (char*)FRAMER_untag_ptr(src); 
    size_t srclen= strlen(untagsrc); // +1?; 
     
    __real_strcpy ((char*)FRAMER_check_mem_access(dest, srclen), 
                   untagsrc);
   // return dest; 

  #else
     
    char * untagged_dest= (char*)FRAMER_untag_ptr(dest);
    __real_strcpy (untagged_dest, 
                  (char*)FRAMER_untag_ptr(src));
    //return untagged_dest;

  #endif
   
    return dest;

}

int __wrap_strcmp(char * str1, char * str2)
{
    char * untagstr1= (char*)FRAMER_untag_ptr(str1); 
    char * untagstr2= (char*)FRAMER_untag_ptr(str2); 
    
    return __real_strcmp (untagstr1, untagstr2); 
}

int __wrap_strncmp(char *str1, char *str2, size_t n)
{

#ifndef ENABLE_SPACEMIU

    char * untagstr1= (char*)FRAMER_check_mem_access(str1, n);
    char * untagstr2= (char*)FRAMER_check_mem_access(str2, n);

#else
    
    char * untagstr1= (char*)FRAMER_untag_ptr(str1);
    char * untagstr2= (char*)FRAMER_untag_ptr(str2);

#endif    
    return __real_strncmp(untagstr1, untagstr2, n);
}

char *__wrap_strncpy(char * dest,char * src,size_t n)
{

#ifndef ENABLE_SPACEMIU

    __real_strncpy((char*)FRAMER_check_mem_access((void*)dest,n),
                   (char*)FRAMER_check_mem_access((void*)src,n), n); 
    
    //return dest; 

#else
    
    char * untagged_dest= (char*)FRAMER_untag_ptr((void*)dest);

    __real_strncpy (untagged_dest,
                   (char*)FRAMER_untag_ptr((void*)src),n); 
    
    //return untagged_dest;
     
#endif
    return dest; 
    
}

int __wrap_memcmp(void *str1, void *str2, size_t n)
{
    return __real_memcmp ((void*)FRAMER_untag_ptr(str1), 
                          (void*)FRAMER_untag_ptr(str2),n);
}

void * __wrap_memchr(void *str, int c, size_t n) 
{
  /*#ifndef ENABLE_SPACEMIU

    void * result= __real_memchr(FRAMER_check_mem_access(str,n),c,n); 
 
    if (result!=NULL){
        uintptr_t tag= (uintptr_t)str & (uintptr_t)(~FRAMER_mask_tag_out); 
        result= (char*)(tag|(uintptr_t)result); 
    }

  #else
    
    void * result= __real_memchr(FRAMER_untag_ptr(str),c,n); 

  #endif

    return result; 
    */

  #ifndef ENABLE_SPACEMIU
    void * result= __real_memchr(FRAMER_check_mem_access(str,n),c,n); 
  #else
    void * result= __real_memchr((void*)FRAMER_untag_ptr(str),c,n); 
  #endif
 
    if (result != NULL){
        uintptr_t tag= (uintptr_t)str & (uintptr_t)(~FRAMER_mask_tag_out); 
        result= (char*)(tag|(uintptr_t)result); 
    }

    return result; 
}

char * __wrap_strchr (char *str, int c)
{
    char* result= __real_strchr((char*)FRAMER_untag_ptr(str),c);

    if (result!=NULL){
        uintptr_t tag= (uintptr_t)str & (uintptr_t)(~FRAMER_mask_tag_out); 
        result= (char*)(tag|(uintptr_t)result); 
    }
    
    return result; 
}

char * 
__wrap_strncat (char *dest, char *src, size_t n)
{

#ifndef ENABLE_SPACEMIU

    size_t srclen= strlen((char*)FRAMER_untag_ptr(src));  
    size_t destlen= strlen((char*)FRAMER_untag_ptr(dest));  
    
    assert_dbg(assert((srclen<n)
                &&"FRAMER ERROR at strncat: strlen <= n\n");) 
    assert(srclen<n);
    
    if (srclen>=n){
      dbg(
        printf("Framer error(strncat).destlen: %"PRIu64", srclen: %"PRIu64", n: %"PRIu64"\n",
        destlen,srclen,n);)
      #ifndef MEASURE_RUNTIME
        exit(0);
      #else
        asm("nop");
      #endif
    }
    __real_strncat ((char*)FRAMER_check_mem_access(dest,destlen+srclen),
                    (char*)FRAMER_untag_ptr(src), n);
    
#else
    __real_strncat ((char*)FRAMER_untag_ptr(dest),
                    (char*)FRAMER_untag_ptr(src), n);

#endif

    return dest; 

}

long int __wrap_strtol (char *str, char **endptr, int base)
{
    long int result= 
        __real_strtol((char*)FRAMER_untag_ptr(str), 
                      (char**)FRAMER_untag_ptr(endptr), 
                      base);
    return result; 
}

#ifdef CPP 
}

#endif


