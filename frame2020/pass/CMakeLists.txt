#add_library(LLVMFramerPass MemfisPass.cpp)
#add_llvm_loadable_module(LLVMFramerPass
#add_llvm_library(LLVMFramerPass
add_llvm_component_library(LLVMFramerPass
  Framer.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/miu 
   
DEPENDS
  intrinsics_gen
)
