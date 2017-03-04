#include "julia.h"
#include "julia_internal.h"

void member_expr2(jl_typemap_entry_t *tm) {
  jl_value_t *val = NULL;
  JL_GC_PUSH1(&val);
  val = tm->func.linfo;
  JL_GC_POP();
}

void clang_analyzer_explain(void *) NOTSAFEPOINT;
extern void look_at_value(jl_value_t *v);

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

extern jl_value_t *first_array_elem(jl_array_t *a PROPAGATES_ROOT);
void root_propagation(jl_expr_t *expr) {
  jl_value_t *val = first_array_elem(expr->args);
  jl_gc_safepoint();
  look_at_value(val);
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