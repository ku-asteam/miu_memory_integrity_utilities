# SpaceMIU: A Run-time Type Confusion Checker for C/C++

> FRAMER: A Tagged-pointer Capability Model
 
aSTEAM Project https://asteam.korea.ac.kr

SpaceMIU is a run-time typecast checker for C (this will be extended
to C++). The majority of typecasts in C/C++ programs are either
upcasts (conversion from a descendant type to its ancestor type) or
downcasts (in the opposite direction). This run-time type confusion
checker implements physical sub-typing for C and pointer-to-type
mapping, and detects unsafe downcasts at run-time using FRAMER’s 
per-object metadata storage and two type descriptors - 
a type layout table and type relation table.

There are three main parts to our implementation: 
LLVM passes (/miu_memory_integrity_utilities/frame-pass2019/), 
and the static library (lib), and the binary lib in this directory. 
The target C source code and our hooks’ functions in the static lib 
are first compiled to LLVM intermediate representation (IR). 
Our main transformation pass (/miu_memory_integrity_utilities/frame-pass2019/transformation)
instruments memory allocation/release, access, 
or type cast in the target code in IR. 
The third part is wrappers around malloc family routines and string functions. 
Currently malloc,realloc,calloc,free (defined in mallocfamily.c) are 
interposed at compiler time,
but interposition at link-time is also possible 
(see wrappers_version2.c and lntpreprocess.sh).


## Requirements and Dependencies

(1) An UNIX-like Operating System
(2) clang/llvm version 4.0.0 or newer.

## Instructions

1. There are two modes of run-time checking: (1) bounds checking and 
   (2) type confusion checking. Changing modes requires SRC code
    modification (see ./framertypes.h and /frame-pass2019/trasformation/Framer.cpp). 
    Enable ENABLE_SPACEMIU to run on type checking mode.
2. Modify (if necessary) and execute a script, lntpreprocess.sh.
3. Modify (if necessary) and execute a script, spec.sh to build/run spaceMIU 
   e.g. with SPEC2000 benchmarks.

    

