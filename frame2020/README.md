# SpaceMIU: A Run-time Type Confusion Checker for C/C++

# Updates
   
1. Clang version 4.0.0 to 12.0.0
2. Types for heap allocations are now detected at compile time, while the previous version (consider ../frame2019/) detects them at run time.
Due to the limitation of static analysis, there may be heap allocations that are dropped from tracking,
but frame2020 provides better performance.
3. frame2020 handles C++, but handling class type hierarchy is in progress.

## Requirements and Dependencies

(1) An UNIX-like Operating System
(2) clang version 11.0.0 or newer, cmake version 3.18.2


