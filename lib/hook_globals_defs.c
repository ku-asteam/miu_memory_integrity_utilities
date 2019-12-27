#include <stdio.h>
#include <inttypes.h>
#include <assert.h>
#include <stdbool.h>

#include "./framertypes.h"
//#include "./usershook.h"

/*
unsigned FRAMER_tempGVcount=0;
unsigned FRAMER_tempstorecount=0;
unsigned FRAMER_temploadcount=0;
 
unsigned FRAMER_Ntempload =0   ;
unsigned FRAMER_Ntempstore =0  ;
unsigned FRAMER_Ntempmem   =0  ;
unsigned FRAMER_Ntempset   =0  ;
unsigned FRAMER_Ntempstrncat =0;
unsigned FRAMER_Ntempstrcpy =0 ;
unsigned FRAMER_Ntempstrcmp =0 ;
unsigned FRAMER_Ntempstrncpy=0 ;
unsigned FRAMER_Ntempmemcmp =0 ;
unsigned FRAMER_Ntempmemchr =0 ;
*/

//const bool FRAMER_is_bigframe = 0;
//const bool FRAMER_is_smallframe = 1;


/* slot size = 2^15, but slot table is every 2^16!! */
//const uintptr_t FRAMER_log_slotsize= 15;
//const uintptr_t FRAMER_num_used_bits_in_ptr= 48;
//const uintptr_t FRAMER_slot_size= 1ULL<<FRAMER_log_slotsize;
//const uintptr_t FRAMER_log_slottable_interval= FRAMER_log_slotsize+1; 

//const uintptr_t FRAMER_slot_base_mask= ~(0xFFFF); 
//const uintptr_t FRAMER_header_slot_base_mask= ~(0x7FFF); 

//const uintptr_t FRAMER_mask_tag_out= 0xFFFFFFFFFFFF; 
//const uintptr_t FRAMER_mask_only_flag_out= (~(1ULL<<63)); 

/* bounds check status */
//const int FRAMER_is_inbound=    1;
//const int FRAMER_is_outofbound= 0;  


/* for BASICType Table*/
//const unsigned FRAMER_llvm_BasicTyCount= 17;
//const unsigned FRAMER_extra_BasicTyCount= 8; // int1, int48, int24 are added!!
//const unsigned FRAMER_total_BasicTyCount= 
//            FRAMER_llvm_BasicTyCount+FRAMER_extra_BasicTyCount;

/* FramerTypeId tag for store instruction */
//const unsigned FRAMER_TyIDStart=100;

#ifdef __cplusplus
extern "C" {
#endif

int FRAMER_BasicTy_table[]=
    {0, 16, 32, 64, 80, // 
     128,128,0, 0,  64, 
     0, 0,  0,  0,  0,
     64, 0,             // LLVM Basic types upto here. 
     8,  16, 32,  
     64, 128, 1, 48, 24}; //integer sizes (IntegerTyID: 11)

/*
    FRAMER_BasicTy_table[VoidTyID]=     0;  //0
    FRAMER_BasicTy_table[HalfTyID]=     16;
    FRAMER_BasicTy_table[FloatTyID]=    32;
    FRAMER_BasicTy_table[DoubleTyID]=   64;
    FRAMER_BasicTy_table[X86_FP80TyID]= 80; //4 
    FRAMER_BasicTy_table[FP128TyID]=    128;
    FRAMER_BasicTy_table[PPC_FP128TyID]=128; 
    FRAMER_BasicTy_table[LabelTyID]=    0;
    FRAMER_BasicTy_table[MetadataTyID]= 0; 
    FRAMER_BasicTy_table[X86_MMXTyID]=  64; //9
    FRAMER_BasicTy_table[TokenTyID]=    0;  
    FRAMER_BasicTy_table[IntegerTyID]=  0; 
    FRAMER_BasicTy_table[FunctionTyID]= 0; 
    FRAMER_BasicTy_table[StructTyID]=   0;
    FRAMER_BasicTy_table[ArrayTyID]=    0;  //15
    FRAMER_BasicTy_table[PointerTyID]=  64;
    FRAMER_BasicTy_table[VectorTyID]=   0; //16 
    FRAMER_BasicTy_table[IntegerTyID+6]=8; //17 
    FRAMER_BasicTy_table[IntegerTyID+7]=16;  
    FRAMER_BasicTy_table[IntegerTyID+8]=32;  
    FRAMER_BasicTy_table[IntegerTyID+9]=64;  
    FRAMER_BasicTy_table[IntegerTyID+10]=128; //21
    FRAMER_BasicTy_table[IntegerTyID+11]=1; 
    FRAMER_BasicTy_table[IntegerTyID+12]=48; 
    FRAMER_BasicTy_table[IntegerTyID+13]=24; 
     
*/

/* for StructType table */

unsigned FRAMER_structTy_count; 
StructEntryT* FRAMER_baseOfStructTable;
//SafeCastEntryT * FRAMER_baseOfSafeCastTable;
short * FRAMER_baseOfSafeCastTable;

void * FRAMER_baseOf_OffsetTable;

short FRAMER_total_offset_count;
short FRAMER_max_ty_count_per_off;
short FRAMER_max_offset_val;

unsigned FRAMER_safecast_col_num;
unsigned FRAMER_safecast_row_num;

/* for Metadata table */
int FRAMER_fd;

//const uintptr_t FRAMER_start_addr_userspace= 0x000000000000; //0x10f14c060
//const uintptr_t FRAMER_end_addr_userspace  = 0x8FFFFFFFFFFF; //0x7fff59f26a10
//const uintptr_t FRAMER_slotbase_of_userspace_start =
//                                FRAMER_start_addr_userspace 
//                                & FRAMER_slot_base_mask;
//const uintptr_t FRAMER_slotbase_of_userspace_end =
//                                FRAMER_end_addr_userspace 
//                                & FRAMER_slot_base_mask;
uintptr_t FRAMER_metatable_count =  //slotarray count 
                        (FRAMER_slotbase_of_userspace_end
                        - FRAMER_slotbase_of_userspace_start)
                        >>FRAMER_log_slottable_interval;

uintptr_t FRAMER_metadata_file_size;

/* TABLES */
// HERE, StructTy ARRAY is inserted by llvm! 
HeaderT* FRAMER_PointerTy_Table [1]; // temporary assignment!! 

//SlotT FRAMER_TABLE[34359734271];
#ifdef ENABLE_TYPECAST_CHECK
  EntryT* FRAMER_TABLE;
#else
  SlotT* FRAMER_TABLE;
#endif

//////////////////////////////////
///// MEASURE_OVERHEADS  /////////

#ifdef COUNT_BIG_SMALL_OBJECTS
  volatile unsigned FRAMER_BIG_FRAMED_OBJECT_COUNT;
  volatile unsigned FRAMER_SMALL_FRAMED_OBJECT_COUNT;
#endif

///// MEASURE_OVERHEADS  /////////
//////////////////////////////////

//GHashTable *hash;

#ifdef __cplusplus
}
#endif

extern int errno;

