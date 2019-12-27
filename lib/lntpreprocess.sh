#!/bin/bash

echo "clang -emit-llvm hook_globals_defs.c -c -o hook_globals_defs.o"
clang -emit-llvm hook_globals_defs.c -c -o hook_globals_defs.o 
echo "rm libhook_globals_defs.a"
rm libhook_globals_defs.a
echo "llvm-ar q  libhook_globals_defs.a hook_globals_defs.o" 
llvm-ar q  libhook_globals_defs.a hook_globals_defs.o
echo "clang -include ./usershook.h wrappers_version2.c -c -o wrappers.o" 
clang -include ./usershook.h wrappers_version2.c -c -o wrappers.o
clang -include ./usershook.h -c mallocfamily.c
