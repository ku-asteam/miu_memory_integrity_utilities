# README #

### Code Obfuscation Using Opaque Predicates ###

This provides program transformation for opaque 
predicates obfuscation.

There are two parts to this implementation: a LLVM transformation 
pass and static library (testlib.h). The target C source code 
and hooks’ functions in the static lib are first compiled to LLVM
intermediate representation (IR) and the obfuscation pass works on 
the LLVM IR. This __module__ pass performs program transformation and
generate the transformed IR. 

### Quick Start ###

The pass part is composed of three files: Obfuscation.cpp, 
Obfuscation.h, and CMakeLists.txt. Obfuscation.cpp and CMakeLists.txt
are placed in the same directory under LLVM source directory (e.g.
/LLVMSRC/lib/Transforms/Obfuscation) and Obfuscation.h in
/LLVMSRC/include/llvm/Transforms/Obfuscation.
In addition, please add the following line to CMakeLists.txt in the 
directory /LLVMSRC/lib/Transforms.

    add_subdirectory(Obfuscation)

Compile the file and you will get a shared object file "LLVMObfuscationPass.so".

To compile each C source file, the following style of
command can be used:

    clang -emit-llvm sample.c -include /PATH_TO_LIB/testlib.h -c -o sample.bc

(currently testlib.h file has only one function: 
\_\_HOOK\_opaque(int n). 
The transformation pass inserts a call to this function.)

One can run the bitcode file (sample.bc) for the program through our transformation as follows: 

    opt -o opted.bc -load ../../lib/LLVMObfuscationPass.so -obfuscation < toy.bc > /dev/null

If necessary, one can use llvm-link to link multiple LLVM bitcode files.   

**Note: please link to <math.h> using -lm with gcc e.g. **

    gcc -o toy.native toy.s -lm


