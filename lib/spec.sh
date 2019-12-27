#!/bin/bash

lnt runtest test-suite \
--sandbox /tmp/BAR \
--cc /var/nam/tools/llvm/lto_modified_build/myexamples/smalltests/lnt_fwd.sh \
--cflags "-O2 -fuse-ld=/usr/bin/ld.gold" \
--cflags "-Xclang -include -Xclang /var/nam/tools/llvm/lto_modified_build/myexamples/smalltests/usershook.h" \
--cflags "-Xclang -include -Xclang /var/nam/tools/llvm/lto_modified_build/myexamples/smalltests/malloc.h" \
--cflags "-Wl,-wrap,strcpy -Wl,-wrap,strcmp -Wl,-wrap,strncpy -Wl,-wrap,strncmp -Wl,-wrap,memcmp -Wl,-wrap,memchr -Wl,-wrap,strchr -Wl,-wrap,strncat -Wl,-wrap,strtol /var/nam/tools/llvm/lto_modified_build/myexamples/smalltests/wrappers.o" \
--cflags "-Xlinker -L/var/nam/tools/llvm/lto_modified_build/myexamples/smalltests -Xlinker -lhook_globals_defs " \
--cflags "-Xlinker /var/nam/tools/llvm/lto_modified_build/myexamples/smalltests/mallocfamily.o " \
--cflags "-Xlinker -lm" \
--cflags "-Xlinker -plugin -Xlinker /var/nam/.local/lto_modified_llvm/lib/LLVMgold.so" \
--cxx /var/nam/.local/llvm/bin/clang++ \
--test-suite /var/nam/tools/llvm/src/llvm-4.0.0.src/test-suite-4.0.0.src \
--test-externals /var/nam/SPEC/ \
--use-cmake=/var/nam/tools/cmake3.8.2/cmake-3.9.0/bin/cmake \
--use-lit=/var/nam/tools/llvm/src/llvm-4.0.0.src/utils/lit/lit.py \
--benchmarking-only \
--only-test External/SPEC/CINT2006 \
--use-perf=all \
--cmake-cache Debug \
-j 10

