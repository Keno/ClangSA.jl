// RUN: %clang_cc1 -analyze -analyzer-checker=core,julia.gcpushpop -verify -x c++ %s

#include "julia.h"

void missingPop() {
  jl_value_t *x = NULL;
  JL_GC_PUSH1(&x); // expected-note{{GC frame changed here}}
} // expected-warning{{Non-popped GC frame present at end of function}}
  // expected-note@-1{{Non-popped GC frame present at end of function}}


void missingPop2() {
  jl_value_t **x;
  JL_GC_PUSHARGS(x, 2); // expected-note{{GC frame changed here}}
} // expected-warning{{Non-popped GC frame present at end of function}}
  // expected-note@-1{{Non-popped GC frame present at end of function}}

void superflousPop() {
  JL_GC_POP(); // expected-warning{{JL_GC_POP without corresponding push}}
}              // expected-note@-1{{JL_GC_POP without corresponding push}}
