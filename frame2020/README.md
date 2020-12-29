# SpaceMIU: A Run-time Type Confusion Checker for C/C++

# Updates
   
1. Clang version 4.0.0 to 12.0.0
2. The effective types for heap allocations are now detected at compile time, 
while the previous version (consider ../frame2019/) detects them at run time.
Due to the limitation of static analysis, there may be heap allocations that are dropped from tracking, but frame2020 provides better performance.
Source code-level analysis can improve detection of effective types for heap allocations via malloc family.
3. frame2020 handles C++, but handling class type hierarchy is in progress.
4. spaceMiu handles unions. LLVM-clang does not support unions; 
In LLVM-clang, a union is treated as a piece of memory 
that is being accessed using different implicit pointer casts. 
More precisely, it converts a union to a structure with the right size 
that meets alignment requirement. 
spaceMiu defines physical sub-typing rules for unions, 
that agrees with LLVM IR, and implements typecast checking for unions.

## Requirements and Dependencies

(1) An UNIX-like Operating System
(2) clang version 11.0.0 or newer, cmake version 3.18.2


