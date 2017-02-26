// RUN: %clang_cc1 -analyze -analyzer-checker=core,julia.gcpushpop -verify -x c++ %s

#include "julia.h"

void unrooted_argument() {
    jl_(jl_svec1(NULL)); // expected-warning{{Passing non-rooted value as argument to function}}
                         // expected-note@-1{{Passing non-rooted value as argument to function}}
};

void simple_svec() {
    // This is ok, because jl_svecref is non-allocating
    jl_value_t *val = jl_svec1(NULL);
    assert(jl_svecref(val, 0) == NULL);
}

jl_value_t *simple_missing_root() {
    jl_ptls_t ptls = jl_get_ptls_states();
    jl_value_t *val = jl_svec1(NULL);
    // This is a GC safepoint, so the above value could have been freed
    jl_gc_safepoint_(ptls);
    return jl_svecref(val, 0);
};
