add_llvm_loadable_module(LLVMObfuscationPass
  Obfuscation.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/Obfuscation 
   
DEPENDS
  intrinsics_gen
)
