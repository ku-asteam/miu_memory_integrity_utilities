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

/* heap allocation functions */
void *__real_malloc(size_t size);
void __real_free(void *ptr);
void *__real_realloc(void *ptr, size_t size);
void *__real_calloc(size_t elems, size_t elemsize);

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

extern void FRAMER_supplementary_update_metadata_header (
        void* p, 
        unsigned FramerTypeID,
        unsigned raw_object_size);

extern uintptr_t FRAMER_supplementary_determine_log_framesize (
        void * p, 
        unsigned objsize);

extern bool FRAMER_supplementary_update_metadata_table (
        void* padded_obj_base, 
        //unsigned FramerTypeID, 
        //unsigned raw_object_size, 
        uintptr_t N);
extern void * FRAMER_suppementary_check_mem_access (
        void * addr,
        unsigned numBytesToAccess,
        short tempinstruction);

extern void* FRAMER_supplementary_tag_ptr (
        void * p, 
        uintptr_t tag, 
        bool flag);

extern void* FRAMER_supplementary_untag_ptr (void* p);
extern uintptr_t FRAMER_supplementary_extract_tagvec (void* p); 
extern uintptr_t FRAMER_supplementary_cal_offset (void * p);
extern bool FRAMER_supplementary_extract_flag (void* p);
extern void FRAMER_supplementary_empty_metadata_entry (
            uintptr_t untagged, uintptr_t tagvec);
extern bool FRAMER_supplementary_isBigAddr (void *p);
// up to here
extern uintptr_t FRAMER_supplementary_check_inframe(uintptr_t p, //untagged 
                                        uintptr_t gepbase, //untagged 
                                        uintptr_t logframesize);


__attribute__((__used__))
//__attribute__((always_inline))
static unsigned FRAMER_get_calloc_elems (unsigned n, unsigned tsize)
{
    unsigned result=0;
    while (result*tsize < sizeof(HeaderT)){
        result++;         
    }
    return result+n;
}

void *__wrap_malloc(size_t allocatedSizeInBytes)
{
    dbg(printf("\nHOOK Malloc\n"));
    //printf("\tFramerTyID:\t%d\n",FramerTypeID);

    unsigned raw_obj_size = (unsigned) allocatedSizeInBytes; 
    assert ((size_t)raw_obj_size == allocatedSizeInBytes
            && "The size of malloc should be type-upgraded!\n"); 
    unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT); 
    
    //allocating
    void * p = __real_malloc(padded_obj_size);
    assert ((p!=NULL) && "Null returned from malloc. Exiting...\n");
    
    assert(!FRAMER_supplementary_isBigAddr(p) && "malloc isbigaddr\n");
    dbg(if (FRAMER_supplementary_isBigAddr(p)){
        printf("Malloc isBigAddr: %p\n", p);
        exit(0);
    })

    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, raw_obj_size, padded_obj_size));
    
    // initialising buffer 
    memset (p, 0, padded_obj_size); 
   
    
    uintptr_t N = FRAMER_supplementary_determine_log_framesize (p, padded_obj_size);  
    dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));

    uintptr_t tag=0;
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    if (N > FRAMER_log_slotsize) {
 
        bool entry_available = 
            FRAMER_supplementary_update_metadata_table (p, N); 
        assert (entry_available 
                && "malloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n"); 
        tag= N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
    dbg(printf("updated entry\n"));
    
    FRAMER_supplementary_update_metadata_header(p, VoidTyID, raw_obj_size);
    dbg(printf("taggin ptr\n"));
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
    
    dbg(printf("\tthin_p:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));

    return (tagged_p + sizeof(HeaderT)); 
}


//__attribute__((always_inline))
void __wrap_free (void* obj_base)
{
    // e.g) free (mymalloc)  
    // get entry location (if N>16) 
    //check entry
    dbg(printf("\nHOOK Free\n"));
    dbg(printf("\tthin_p: %p\n", obj_base));
    
    bool flag= FRAMER_supplementary_extract_flag (obj_base); 
    uintptr_t untagged_p= (uintptr_t)FRAMER_supplementary_untag_ptr(obj_base);
    uintptr_t tagvec= FRAMER_supplementary_extract_tagvec(obj_base);
    uintptr_t hidden_actual_base = untagged_p - sizeof(HeaderT);
   
    if (tagvec==0){ 
        __real_free((void*)hidden_actual_base);
        return; 
    }

    //printf("\ttagged obj_base:\t%p\n", obj_base);
    //printf("\ttagged hidden_base:\t%p\n", hidden_actual_base);
    
    if (flag==FRAMER_is_bigframe){ 
        FRAMER_supplementary_empty_metadata_entry (hidden_actual_base, tagvec);
    }
    assert((HeaderT*)hidden_actual_base!=NULL 
            && "Header is NULL at free! Double free?\n");
    dbg(printf("\tpadded_p: %p\n", (void*)hidden_actual_base));
    __real_free((void*)hidden_actual_base);

}

void *__wrap_realloc(void* thin_base, size_t size)
{
    dbg(printf("\nHOOK realloc\n"));
    //printf("\nHOOK realloc\n");
    
    uintptr_t tagvec= FRAMER_supplementary_extract_tagvec (thin_base); 
    // check if it's tagged  
    assert(tagvec!=0 && " Not tagged.");
    dbg(if (tagvec==0) {
        printf("\tError: Not tagged. CHECK. thin_base: %p\n", thin_base);
        exit(0);
    })
    // 1.get hidden base
    bool flag= FRAMER_supplementary_extract_flag (thin_base); 
    uintptr_t untagged_p= (uintptr_t)FRAMER_supplementary_untag_ptr(thin_base);
    uintptr_t padded_base = untagged_p - sizeof(HeaderT);
    // get padded_size 
    unsigned padded_obj_size= size + sizeof(HeaderT);  
    
    //1.1. reset metatable entry, if it's big frame.
     if (flag==FRAMER_is_bigframe){ 
        FRAMER_supplementary_empty_metadata_entry (padded_base, tagvec);
    }
    assert((HeaderT*)padded_base!=NULL 
             && "Hook realloc: Header is NULL at free! Double free?\n");

    dbg(printf("\told thin_base:\t%p\n", thin_base));
    
    // 2.call realloc and pass untagged hidden base and new size (padded)
    void * p = __real_realloc((void*)padded_base, padded_obj_size);
    assert(p!=NULL && "realloc returned NULL"); 
    dbg(if (p==NULL) {
        printf("realloc returned NULL. exiting..\n");
        exit(0);
    })
   // memset (p, 0, padded_obj_size); 
     
    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, size, padded_obj_size));
    //printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        //p, size, padded_obj_size);
    // 3. do the rest like malloc with returned ptr, and return ptr to the beginning of actual object.
    
    uintptr_t N = FRAMER_supplementary_determine_log_framesize (p, padded_obj_size);  
    //dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));
    
    uintptr_t tag=0;
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    if (N > FRAMER_log_slotsize) {
        //dbg(printf("BIG FRAME. realloc\n"));
        
        bool entry_available = 
            FRAMER_supplementary_update_metadata_table (p, 
                                                        N);   
        assert (entry_available 
                && "realloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n"); 
        tag= N;
        whichframe= FRAMER_is_bigframe;
       //printf("\ttagged_p:\t%p\n", tagged_p);
    }
    else {
        //dbg(printf("\trealloc. small frame\n")); 
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
    FRAMER_supplementary_update_metadata_header(p, 
            VoidTyID, 
            size);
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
    
    dbg(printf("\tnew thin_b:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));
    
    //printf("Realloc. thin_b:%p, fat_b: %p\n", (void*)tagged_p+sizeof(HeaderT),p);
    
    return (tagged_p+sizeof(HeaderT)); 

    // 4. change the option for linker (add wrap realloc)
    // 5. add checking if there's calloc (What else) call in framer.cpp
}

void *__wrap_calloc(size_t elems, size_t elemsize)
{
    unsigned raw_obj_size = (unsigned) elems*elemsize; 
    //unsigned padded_obj_size= raw_obj_size + sizeof(HeaderT); 
    unsigned pad_elems= FRAMER_get_calloc_elems(elems,elemsize);
    dbg(printf("n: %u, tsize: %u, new_n: %u, HeaderT: %u\n", 
            elems, elemsize, pad_elems, sizeof(HeaderT));) 
    unsigned padded_obj_size=pad_elems*elemsize; 
    
    //allocating
    void * p = __real_calloc(pad_elems, elemsize);
    assert ((p!=NULL) && "Null returned from calloc. Exiting...\n");
    
    assert (!FRAMER_supplementary_isBigAddr(p) && "calloc isBigAddr\n");
    dbg(if (FRAMER_supplementary_isBigAddr(p)){
        printf("calloc isBigAddr: %p\n", p);
        exit(0);
    })

    dbg(printf("\tpadded_P:\t%p\n\tObjectSize_Raw:\t%u\n\tPadded Objsize:\t%u\n", 
        p, raw_obj_size, padded_obj_size));
    
    // initialising buffer 
    memset (p, 0, padded_obj_size); 
    
    uintptr_t N = FRAMER_supplementary_determine_log_framesize (p, padded_obj_size);  
    //dbg(printf("\tLog(Frame):\t%"PRIuPTR"\n", N));

    uintptr_t tag=0;
    bool whichframe;

    // update metadata in the header. for big framed one, save entry also. 
    void* tagged_p = NULL;
    if (N > FRAMER_log_slotsize) {
 
        bool entry_available = 
            FRAMER_supplementary_update_metadata_table (p, N); 
        assert (entry_available 
                && "malloc:corresponding entry in the table is not 0!"
                "possibly overlapped allocation?\n"); 
        tag= N;
        whichframe= FRAMER_is_bigframe;
    }
    else {
        tag= FRAMER_supplementary_cal_offset(p); 
        whichframe= FRAMER_is_smallframe;
    }
    FRAMER_supplementary_update_metadata_header(p, VoidTyID, raw_obj_size);
    tagged_p = FRAMER_supplementary_tag_ptr (p, tag, whichframe);     
    
    dbg(printf("\tthin_p:\t%p\n", (void*)tagged_p+sizeof(HeaderT)));

    return (tagged_p + sizeof(HeaderT)); 
}


char *__wrap_strcpy(char * dest, char * src)
{
     // 1. get objsize (dest) strlen(src) 
    // 2. check dest + strlen(str) (+1?) < dest_end
    // then return untagged_dest. (untagging src is handled in untag hook)
    char * untagsrc= (char*)FRAMER_supplementary_untag_ptr(src); 
    size_t srclen= strlen(untagsrc); // +1?; 
     
    __real_strcpy((char*)FRAMER_suppementary_check_mem_access(dest, srclen, tempstrcpy), untagsrc);
    return dest; 
}

int __wrap_strcmp(char * str1, char * str2)
{
    char * untagstr1= (char*)FRAMER_supplementary_untag_ptr((void*)str1); 
    char * untagstr2= (char*)FRAMER_supplementary_untag_ptr((void*)str2); 
    
    return __real_strcmp (untagstr1, untagstr2); 
}

int __wrap_strncmp(char *str1, char *str2, size_t n)
{
    char * untagstr1= (char*)FRAMER_suppementary_check_mem_access(str1, n, tempstrcmp);
    char * untagstr2= (char*)FRAMER_suppementary_check_mem_access(str2, n, tempstrcmp);
    
    return __real_strncmp(untagstr1, untagstr2,n);
    //if (((uintptr_t)result^(uintptr_t)untagstr1)==0) {
    //    return str1;
    //}
    //return str2;
}

char *__wrap_strncpy(char * dest,char * src,size_t n)
{
    char* untagsrc= (char*)FRAMER_supplementary_untag_ptr(src);
    assert ((n < strlen(untagsrc)) &&
            "Framer strncpy error: strlen(src)>n\n"); // +1?; 

    __real_strncpy((char*)FRAMER_suppementary_check_mem_access(dest,n, tempstrncpy),untagsrc,n); 
    return dest; 
}

int __wrap_memcmp(void *str1, void *str2, size_t n)
{
    return __real_memcmp(FRAMER_suppementary_check_mem_access(str1, n, tempmemcmp), 
                        FRAMER_suppementary_check_mem_access(str2, n, tempmemcmp),n);
}

void * __wrap_memchr(void *str, int c, size_t n) 
{
    void * result= __real_memchr(FRAMER_suppementary_check_mem_access(str,n, tempmemchr),c,n); 
    if (result!=NULL){
        uintptr_t tag= (uintptr_t)str & (uintptr_t)(~FRAMER_mask_tag_out); 
        result= (char*)(tag|(uintptr_t)result); 
    }
    return result; 
}

char * __wrap_strchr (char *str, int c)
{
    char* result= __real_strchr((char*)FRAMER_supplementary_untag_ptr((void*)str),c);
    if (result!=NULL){
        uintptr_t tag= (uintptr_t)str & (uintptr_t)(~FRAMER_mask_tag_out); 
        result= (char*)(tag|(uintptr_t)result); 
    }
    return result; 
}
char * __wrap_strncat (char *dest, char *src, size_t n)
{
    //srclen < n
    //destsize >= destlen+n
    size_t srclen= strlen((char*)FRAMER_supplementary_untag_ptr(src));  
    size_t destlen= strlen((char*)FRAMER_supplementary_untag_ptr(dest));  
    
    assert((srclen<n)&&"FRAMER ERROR at strncat: strlen <= n\n");
    if (srclen>=n){
        dbg(printf("Framer error(strncat).destlen: %"PRIu64", srclen: %"PRIu64", n: %"PRIu64"\n",
                destlen,srclen,n);)
        exit(0);
    }
    __real_strncat ((char*)FRAMER_suppementary_check_mem_access(dest,destlen+srclen, tempstrncat),
                    (char*)FRAMER_supplementary_untag_ptr(src), n);
    return dest; 
}

long int __wrap_strtol (char *str, char **endptr, int base)
{
    //printf("strtol str: %s\n", (char*)FRAMER_supplementary_untag_ptr(str));
    long int result= 
        __real_strtol((char*)FRAMER_supplementary_untag_ptr(str), 
                      (char*)FRAMER_supplementary_untag_ptr(endptr), 
                      base);
    //printf("  result: %lu\n",result);
    return result; 
}
