// RUN: %clang_cc1 -analyze -analyzer-checker=core,julia.gcpushpop -verify -x c++ %s

#include "julia.h"
#include "julia_internal.h"

void unrooted_argument() {
    jl_(jl_svec1(NULL)); // expected-warning{{Passing non-rooted value as argument to function}}
                         // expected-note@-1{{Passing non-rooted value as argument to function}}
};

void simple_svec() {
    // This is ok, because jl_svecref is non-allocating
    jl_value_t *val = jl_svec1(NULL);
    assert(jl_svecref(val, 0) == NULL);
}

extern void jl_gc_safepoint();
jl_value_t *simple_missing_root() {
    jl_value_t *val = jl_svec1(NULL);
    // This is a GC safepoint, so the above value could have been freed
    jl_gc_safepoint(); // expected-note {{Value may have been GCed here}}
    return jl_svecref(val, 0); // expected-warning{{Argument value may have been GCed}}
                               // expected-note@-1{{Argument value may have been GCed}}
};

jl_value_t *root_value() {
    jl_value_t *val = jl_svec2(NULL, NULL);
    JL_GC_PUSH1(&val);
    jl_gc_safepoint();
    jl_value_t *ret = jl_svecref(val, 0);
    JL_GC_POP();
    return ret;
};

jl_value_t *existing_root() {
    jl_value_t *val = NULL;
    JL_GC_PUSH1(&val);
    val = jl_svec1(NULL);
    jl_gc_safepoint();
    jl_value_t *ret = jl_svecref(val, 0);
    JL_GC_POP();
    return ret;
};

jl_value_t *late_root() {
    jl_value_t *val = NULL;
    val = jl_svec1(NULL);
    jl_gc_safepoint(); // expected-note {{Value may have been GCed here}}
    JL_GC_PUSH1(&val); // expected-warning{{Trying to root value which may have been GCed}}
                       // expected-note@-1{{Trying to root value which may have been GCed}}
    jl_value_t *ret = jl_svecref(val, 0);
    JL_GC_POP();
    return ret;
};

jl_value_t *late_root2() {
    jl_value_t *val = NULL;
    jl_value_t *val2 = NULL;
    JL_GC_PUSH1(&val);
    val2 = jl_svec1(NULL);
    jl_gc_safepoint(); // expected-note {{Value may have been GCed here}}
    val = val2; // expected-warning{{Trying to root value which may have been GCed}}
                // expected-note@-1{{Trying to root value which may have been GCed}}
    jl_value_t *ret = jl_svecref(val, 0);
    JL_GC_POP();
    return ret;
};

jl_value_t *already_freed() {
    jl_value_t *val = NULL;
    JL_GC_PUSH1(&val);
    val = jl_svec1(NULL); // expected-note {{Value was rooted here}}
    JL_GC_POP(); // exptected-noted {{Root was released here}}
    jl_gc_safepoint(); // expected-note {{Value may have been GCed here}}
    jl_value_t *ret = jl_svecref(val, 0); // expected-warning{{warning: Argument value may have been GCed}}
                                          // expected-note@-1{{warning: Argument value may have been GCed}}
    return ret;
};

int field_access() {
    jl_svec_t *val = jl_svec1(NULL); 
    jl_gc_safepoint(); // expected-note{{Value may have been GCed here}}
    return val->length == 1; // expected-warning{{Trying to access value which may have been GCed}}
                             // expected-note@-1{{Trying to access value which may have been GCed}}
}  

int pushargs_roots() {
  jl_value_t **margs;
  jl_svec_t *val = jl_svec1(NULL);;
  JL_GC_PUSHARGS(margs, 2);
  margs[1] = val;
  jl_gc_safepoint();
  JL_GC_POP();
  return val->length == 1;
}

int pushargs_roots_freed() {
  jl_value_t **margs;
  jl_svec_t *val = jl_svec1(NULL);;
  JL_GC_PUSHARGS(margs, 1);
  margs[0] = val; // expected-note{{Value was rooted here}}
  JL_GC_POP(); // expected-noted{{Root was released here}}
  jl_gc_safepoint(); // expected-note{{Value may have been GCed here}}
  return val->length == 1; // expected-warning{{Trying to access value which may have been GCed}}
                           // expected-note@-1{{Trying to access value which may have been GCed}}
}

extern void process_unrooted(jl_value_t *maybe_unrooted MAYBE_UNROOTED);
int unrooted() {
  jl_svec_t *val = jl_svec1(NULL);
  // This is ok
  process_unrooted(val); // expected-note{{Value may have been GCed here}}
  // This is not
  return val->length == 1; // expected-warning{{Trying to access value which may have been GCed}}
                           // expected-note@-1{{Trying to access value which may have been GCed}}
}

extern jl_value_t *global_value GLOBALLY_ROOTED; 
extern void look_at_value(jl_value_t *v);
void globally_rooted() {
  jl_value_t *val = global_value;
  jl_gc_safepoint();
  look_at_value(val);
  JL_GC_PUSH1(&val);
  jl_gc_safepoint();
  look_at_value(val);
  JL_GC_POP();
  jl_gc_safepoint();
  look_at_value(val);
}

extern jl_value_t *first_array_elem(jl_array_t *a PROPAGATES_ROOT);
void root_propagation(jl_expr_t *expr) {
  jl_value_t *val = first_array_elem(expr->args);
  jl_gc_safepoint();
  look_at_value(val);
}

void argument_propagation(jl_value_t *a) {
  jl_svec_t *types = jl_svec2(NULL, NULL);
  JL_GC_PUSH1(&types);
  jl_value_t *val = jl_svecset(types, 0, jl_typeof(a));
  jl_gc_safepoint();
  look_at_value(val);
  jl_svecset(types, 1, jl_typeof(a));
  JL_GC_POP();
}

// New value creation via []
void arg_array(jl_value_t **args) {
  jl_gc_safepoint();
  jl_value_t *val = args[1];
  look_at_value(val);
  jl_value_t *val2 = NULL;
  JL_GC_PUSH1(&val2);
  val2 = val;
  JL_GC_POP();
}

// New value creation via ->
void member_expr(jl_expr_t *e) {
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = e->args;
  JL_GC_POP();
}

void member_expr2(jl_typemap_entry_t *tm) {
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = tm->func.linfo;
  JL_GC_POP();
}

static inline void look_at_args(jl_value_t **args) {
  look_at_value(args[1]);
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = args[2];
  JL_GC_POP();
}

void pushargs_as_args()
{
  jl_value_t **args;
  JL_GC_PUSHARGS(args, 5);
  look_at_args(args);
  JL_GC_POP();
}

static jl_typemap_entry_t *call_cache[10] GLOBALLY_ROOTED;
void global_array2() {
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = call_cache[1]->func.linfo;
  JL_GC_POP();
}

void global_array3() {
  jl_value_t *val = NULL;
  jl_typemap_entry_t *tm = NULL;
  tm = call_cache[1];
  val = tm->func.linfo;
  look_at_value(val);
}

static inline look_at_value2(jl_value_t *v) {
  look_at_value(v);
}
void mtable(jl_value_t *f) {
  look_at_value2(jl_gf_mtable(f));
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = jl_gf_mtable(f);
  JL_GC_POP();
}

void mtable2(jl_value_t **v) {
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = jl_gf_mtable(v[2]);
  JL_GC_POP();
}

void tparam0(jl_value_t *atype) {
   look_at_value(jl_tparam0(atype));
}

extern jl_value_t *global_atype GLOBALLY_ROOTED;
void tparam0_global() {
   look_at_value(jl_tparam0(global_atype));
}

static jl_value_t *some_global GLOBALLY_ROOTED;
void global_copy() {
    jl_value_t *local = NULL;
    jl_gc_safepoint();
    JL_GC_PUSH1(&local);
    local = some_global;
    some_global = NULL;
    jl_gc_safepoint();
    look_at_value(some_global);
    JL_GC_POP();
}

// Check that rooting the same value twice uses to oldest scope
void scopes() {
    jl_value_t *val = jl_svec1(NULL);
    JL_GC_PUSH1(&val);
    jl_value_t *val2 = val;    
    JL_GC_PUSH1(&val2);
    JL_GC_POP();
    jl_gc_safepoint();
    look_at_value(val);
    JL_GC_POP();
}

jl_module_t *propagation(jl_module_t *m PROPAGATES_ROOT);
void module_member(jl_module_t *m)
{
    for(int i=(int)m->usings.len-1; i >= 0; --i) {
      jl_module_t *imp = (jl_module_t*)m->usings.items[i];
      jl_gc_safepoint();
      look_at_value(imp);
      jl_module_t *prop = propagation(imp);
      look_at_value(prop);
      JL_GC_PUSH1(&imp);
      jl_gc_safepoint();
      look_at_value(imp);
      JL_GC_POP();
    }
}

extern jl_typemap_level_t *jl_new_typemap_level(void);
static jl_typemap_level_t *jl_method_convert_list_to_cache(jl_typemap_entry_t *ml, jl_value_t *key, int8_t offs,
                                                           const struct jl_typemap_info *tparams)
{
    jl_typemap_level_t *cache = jl_new_typemap_level();
    cache->key = key;
    jl_typemap_entry_t *next = NULL;
    JL_GC_PUSH3(&cache, &next, &ml);
    while (ml != (void*)jl_nothing) {
        next = ml->next;
        ml->next = (jl_typemap_entry_t*)jl_nothing;
        jl_typemap_level_insert_(cache, ml, offs, tparams);
        ml = next;
    }
    JL_GC_POP();
    return cache;
}

int type_type(jl_value_t *v) {
    return jl_is_type_type(jl_typeof(v));
}

void assoc_exact_broken(jl_value_t **args, size_t n, int8_t offs, size_t world) {
    jl_typemap_level_t *cache = jl_new_typemap_level();
    jl_typemap_assoc_exact(cache->any, args, n, offs, world); //expected-warning{{Passing non-rooted value as argument to function that may GC}}
}

extern jl_typemap_level_t *jl_new_typemap_level(void);
void assoc_exact_ok(jl_value_t **args, size_t n, int8_t offs, size_t world) {
    jl_typemap_level_t *cache = jl_new_typemap_level();
    JL_GC_PUSH1(&cache);
    jl_typemap_assoc_exact(cache->any, args, n, offs, world);
    JL_GC_POP();
}
