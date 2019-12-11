#define EMABLE_INTERPOSE_MALLOC

#ifdef EMABLE_INTERPOSE_MALLOC
#define malloc(size)        FRAMER_malloc(size) 
#define realloc(ptr, size)  FRAMER_realloc(ptr, size) 
#define calloc(elems, elemsize) FRAMER_calloc(elems, elemsize) 
#define free(ptr)           FRAMER_free(ptr) 
void *FRAMER_malloc(size_t size); 
void *FRAMER_realloc(void * ptr, size_t size); 
void *FRAMER_calloc(size_t elems, size_t elemsize); 
void FRAMER_free (void* ptr);

#endif
