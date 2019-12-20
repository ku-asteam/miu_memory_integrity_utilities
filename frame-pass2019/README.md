#FRAMER: A Tagged-pointer Capability Model
#spaceMIU: A Run-time Type Confusion Checker for C/C++
 
aSTEAM Project https://asteam.korea.ac.kr

FRAMER is software-based Capability Model, a part of MIU:Memory Integrity Utilities.
This is implemented as LLVM Link Time Optimization (LTO) Pass.

This takes C/C++ SRC codes, performs program transformation/analysis 
on LLVM intermediate representation, and produces a instrumented executable.
This consists of FRAMER's program transformation pass,
compiler optimization passes, and static and binary libraries.

SpaceMiu is a run-time typecast checker for C (this will be extended
to C++). The majority of typecasts in C/C++ programs are either
upcasts (conversion from a descendant type to its ancestor type) or
downcasts (in the opposite direction). This run-time type confusion
checker implements physical sub-typing for C and pointer-to-type
mapping, and detects unsafe downcasts at run-time using FRAMER’s 
per-object metadata storage and two type descriptors - 
a type layout table and type relation table.
 
# Requirements and Dependencies

(1) An UNIX-like Operating System
(2) clang/llvm version 4.0.0 or newer.

# Instructions

1. Configure LLVM with cmake

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

2. Build Gold plugin
with this option:
-DLLVM_BINUTILS_INCDIR=/path/to/llvm/binutils/binutils/include/ \

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


5. Choice of two modes: bounds checking and type confusion checking
    Requires SRC code modification (framertypes.h and Framer.cpp)
    Enable ENABLE_SPACEMIU to run on type checking mode.
    
