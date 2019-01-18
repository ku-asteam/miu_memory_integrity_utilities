#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <assert.h>
#include <stdbool.h>
#include <errno.h>
//#include <glib.h>

#ifndef FRAMERTYPES_H_
#define FRAMERTYPES_H_

///// converted const GVs to macro
#define FRAMER_is_bigframe 0
#define FRAMER_is_smallframe 1

/* for pointer typecast checking */
// assigned when allocated by malloc family
//#define FRAMER_is_heap_not_Init -2 
// typeID -1 assigned if it is used as a byte array 
#define FRAMER_is_heap_obj -1

/* slot size = 2^15, but slot table is every 2^16!! */
#define FRAMER_log_slotsize 15
#define FRAMER_num_used_bits_in_ptr 48
#define FRAMER_slot_size (1ULL<<FRAMER_log_slotsize)
#define FRAMER_log_slottable_interval (FRAMER_log_slotsize+1)

#define FRAMER_num_of_entries_per_slot 48

#define FRAMER_slot_base_mask (~(0xFFFF)) 
#define FRAMER_header_slot_base_mask (~(0x7FFF)) 

#define FRAMER_mask_tag_out 0xFFFFFFFFFFFF 
#define FRAMER_mask_content_out 0xFFFF000000000000 
#define FRAMER_flagmask 0x8000000000000000 //(1ULL<<63)
#define FRAMER_mask_only_flag_out (~FRAMER_flagmask) 

/* bounds check status */
#define FRAMER_is_inbound 1
#define FRAMER_is_outofbound 0  


/* for BASICType Table*/
#define FRAMER_llvm_BasicTyCount 17
#define FRAMER_extra_BasicTyCount 8 // int1, int48, int24 are added!!
#define FRAMER_total_BasicTyCount (FRAMER_llvm_BasicTyCount+FRAMER_extra_BasicTyCount)

/* FramerTypeId tag for store instruction */
#define FRAMER_TyIDStart 100

#define FRAMER_start_addr_userspace 0x000000000000 //0x10f14c060
#define FRAMER_end_addr_userspace   0x8FFFFFFFFFFF //0x7fff59f26a10
#define FRAMER_slotbase_of_userspace_start (FRAMER_start_addr_userspace & FRAMER_slot_base_mask) 
#define FRAMER_slotbase_of_userspace_end (FRAMER_end_addr_userspace & FRAMER_slot_base_mask)
//slotarray count 
//#define FRAMER_metatable_count (FRAMER_slotbase_of_userspace_end- FRAMER_slotbase_of_userspace_start)>>FRAMER_log_slottable_interval

#define tempload    0
#define tempstore   1
#define tempmem     2
#define tempset     3
#define tempstrncat 4
#define tempstrcpy  5
#define tempstrcmp  6
#define tempstrncpy 7
#define tempmemcmp  8
#define tempmemchr  9
/// define upto here

#define ENABLE_TYPECAST_CHECK

/* This funcion is inserted at every global variable or static variable */
enum BASICType {
    VoidTyID,       //0  
    HalfTyID,        
    FloatTyID,       	
    DoubleTyID,      	
    X86_FP80TyID,     	
    FP128TyID,      //5   	
    PPC_FP128TyID,   	
    LabelTyID,       	
    MetadataTyID,    	
    X86_MMXTyID,
    TokenTyID,      //10	
    IntegerTyID,     	
    FunctionTyID,    	
    StructTyID,      	
    ArrayTyID,       	
    PointerTyID,    //15  	
    VectorTyID      	
};

typedef struct FRAMER_BASICTypes {
    unsigned tysize; 
} BasicTypeT;

typedef struct  __attribute__((packed)) FRAMER_Headers {
    unsigned FramerTyID; // FramerTypeID of elem. 
    unsigned size;  // the raw obj size

  #ifdef ENABLE_TYPECAST_CHECK
    unsigned elemsize;  // elem size for an array.(for struct, size==elemsize) 
    unsigned padding; 
  #else
    uint64_t padding; //padding for 16-alignment.can be used for something else.
  #endif
} HeaderT;  
 
typedef struct FRAMER_StructTableEntries {
    unsigned tysize;
    unsigned* fields; 
} StructEntryT;

typedef struct FRAMER_SafeCastTableEntries {
    short* tyids;    
}SafeCastEntryT;

typedef struct FRAMER_Entries {
    //unsigned FramerTyID; --> move to header!
    //unsigned size; // size of a raw object. --> move to header! 
    void * base; // base address of a raw object. --> now header address!! 
} EntryT; 

typedef struct FRAMER_ShadowTableEntries {
    EntryT slotarray[48]; 
} SlotT;

#endif  //header endif
