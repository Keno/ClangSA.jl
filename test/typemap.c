// RUN: %clang --analyze -Xanalyzer -analyzer-output=text -Xclang -load -Xclang %gc_plugin -I%julia_home/src -I%julia_home/src/support -I%julia_home/usr/include -Xclang -analyzer-checker=core,julia.GCChecker --analyzer-no-default-checks -Xclang -verify -Xclang -verify-ignore-unexpected=note -x c %s
#include "julia.h"
#include "julia_internal.h"

extern jl_typemap_level_t *jl_new_typemap_level(void);
void assoc_exact_ok(jl_value_t **args, size_t n, int8_t offs, size_t world) {
    jl_typemap_level_t *cache = jl_new_typemap_level();
    JL_GC_PUSH1(&cache);
    jl_typemap_assoc_exact(cache->any, args, n, offs, world);
    JL_GC_POP();
}

void assoc_exact_broken(jl_value_t **args, size_t n, int8_t offs, size_t world) {
    jl_typemap_level_t *cache = jl_new_typemap_level();
    jl_typemap_assoc_exact(cache->any, args, n, offs, world); //expected-warning{{Passing non-rooted value as argument to function that may GC}}
}
