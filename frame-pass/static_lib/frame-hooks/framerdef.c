#include <stdio.h>

#include "./framertypes.h"

__attribute__((__used__))
__attribute__((always_inline))
static uintptr_t FRAMER_supplementary_check_inframe(uintptr_t p, //untagged 
                                        uintptr_t gepbase, //untagged 
                                        uintptr_t logframesize)
{
    return (p&((~0)<<logframesize))^(gepbase &((~0)<<logframesize)); 
    //p's framebase==gepbase' framebase
}


