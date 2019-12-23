# FRAMER: Software-based Capability Model
 
aSTEAM Project https://asteam.korea.ac.kr

FRAMER is software-based Capability Model, a part of MIU:Memory Integrity Utilities.
This is implemented as LLVM Link Time Optimization (LTO) Pass.

This takes C/C++ SRC codes, performs program transformation/analysis 
on LLVM intermediate representation, and produces a instrumented executable.
This consists of FRAMER's program transformation pass,
compiler optimization passes, and static and binary libraries.

## Requirements and Dependencies

(1) An UNIX-like Operating System
(2) clang/llvm version 4.0.0 or newer.

## Instructions

1. Configure LLVM with cmake

`
./llvm_build/
CC=/usr/bin/gcc \
CXX=/usr/bin/g++  \
cmake -G "Unix Makefiles" \
-DCMAKE_INSTALL_PREFIX=/path/to/installation/dir/ \
DCMAKE_CXX_LINK_FLAGS=-L/usr/lib64 \
-Wl,-rpath,/usr/lib64 \
-DLLVM_BUILD_LLVM_DYLIB=ON \
-DLLVM_LINK_LLVM_DYLIB=ON \
/path/to/llvm/src/dir/
`

2. Build Gold plugin with this option:

`-DLLVM_BINUTILS_INCDIR=/path/to/llvm/binutils/binutils/include/ \`

Reference: https://llvm.org/docs/GoldPlugin.html

3. Build Framer with Framer.cpp in /llvmSRC/lib/Transforms/frame-pass,
and Framer.h in /llvmSRC/include/llvm/Transforms/frame-pass
with modification of 
    PassManagerBuilder.cpp, 
    LTOCodeGenerator.cpp, 
    InitializePasses.h,

4. set PATH for usage:
    for ar, ranlib, ld-new under binutils.
    for LLVMGold.so, libLTO.so, libLLVM.so 


