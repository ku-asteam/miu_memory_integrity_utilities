#add_library(LLVMFramerPass MemfisPass.cpp)
#add_llvm_loadable_module(LLVMFramerPass
add_llvm_library(LLVMFramerPass
  Framer.cpp
#  frame-pass.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/frame-pass 
  #${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms 
   
#    PLUGIN_TOOL
#     opt
DEPENDS
  intrinsics_gen
)
