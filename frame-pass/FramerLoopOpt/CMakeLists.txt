add_llvm_library(LLVMFramerLoopOptPass
  FramerLoopOpt.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/FramerLoopOpt 
  #${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms 
   
#    PLUGIN_TOOL
#     opt
DEPENDS
  intrinsics_gen
)
