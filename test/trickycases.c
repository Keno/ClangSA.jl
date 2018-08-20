// RUN: %clang --analyze -Xanalyzer -analyzer-output=text -Xclang -load -Xclang %gc_plugin -I%julia_home/src -I%julia_home/src/support -I%julia_home/usr/include -Xclang -analyzer-checker=core,julia.GCChecker --analyzer-no-default-checks -Xclang -verify -Xclang -verify-ignore-unexpected=note -x c %s
// expected-no-diagnostics
#include "julia.h"
#include "julia_internal.h"

extern void look_at_value(jl_value_t *v);
extern void jl_gc_safepoint();

// this is the general entry point for looking up a type in the cache
// as a subtype, or with type_equal
jl_typemap_entry_t *jl_typemap_assoc_by_type(union jl_typemap_t ml_or_cache, jl_value_t *types, jl_svec_t **penv,
                                             int8_t subtype, int8_t offs, size_t world, size_t max_world_mask)
{
    if (jl_typeof(ml_or_cache.unknown) == (jl_value_t*)jl_typemap_level_type) {
        jl_typemap_level_t *cache = ml_or_cache.node;
        // called object is the primary key for constructors, otherwise first argument
        jl_value_t *ty = NULL;
        jl_value_t *ttypes = jl_unwrap_unionall((jl_value_t*)types);
        assert(jl_is_datatype(ttypes));
        size_t l = jl_field_count(ttypes);
        int isva = 0;
        // compute the type at offset `offs` into `types`, which may be a Vararg
        if (l <= offs + 1) {
            ty = jl_tparam(ttypes, l - 1);
            if (jl_is_vararg_type(ty)) {
                ty = jl_unwrap_vararg(ty);
                isva = 1;
            }
            else if (l <= offs) {
                ty = NULL;
            }
        }
        else if (l > offs) {
            ty = jl_tparam(ttypes, offs);
        }
        // If there is a type at offs, look in the optimized caches
        if (!subtype) {
            if (ty && jl_is_any(ty))
                return jl_typemap_assoc_by_type(cache->any, types, penv, subtype, offs + 1, world, max_world_mask);
            if (isva) // in lookup mode, want to match Vararg exactly, not as a subtype
                ty = NULL;
        }
        if (ty) {
            if (jl_is_type_type(ty)) {
                jl_value_t *a0 = jl_tparam0(ty);
                if (cache->targ.values != (void*)jl_nothing && jl_is_datatype(a0)) {
                    union jl_typemap_t ml = mtcache_hash_lookup(&cache->targ, a0, 1, offs);
                    if (ml.unknown != jl_nothing) {
                        jl_typemap_entry_t *li =
                            jl_typemap_assoc_by_type(ml, types, penv, subtype, offs + 1, world, max_world_mask);
                        if (li) return li;
                    }
                }
                if (!subtype && is_cache_leaf(a0)) return NULL;
            }
            if (cache->arg1.values != (void*)jl_nothing && jl_is_datatype(ty)) {
                union jl_typemap_t ml = mtcache_hash_lookup(&cache->arg1, ty, 0, offs);
                if (ml.unknown != jl_nothing) {
                    jl_typemap_entry_t *li =
                        jl_typemap_assoc_by_type(ml, types, penv, subtype, offs + 1, world, max_world_mask);
                    if (li) return li;
                }
            }
            if (!subtype && is_cache_leaf(ty)) return NULL;
        }
        // Always check the list (since offs doesn't always start at 0)
        if (subtype) {
            jl_typemap_entry_t *li = jl_typemap_assoc_by_type_(cache->linear, types, penv, world, max_world_mask);
            if (li) return li;
            return jl_typemap_assoc_by_type(cache->any, types, penv, subtype, offs + 1, world, max_world_mask);
        }
        else {
            return jl_typemap_lookup_by_type_(cache->linear, types, world, max_world_mask);
        }
    }
    else {
        return subtype ?
            jl_typemap_assoc_by_type_(ml_or_cache.leaf, types, penv, world, max_world_mask) :
            jl_typemap_lookup_by_type_(ml_or_cache.leaf, types, world, max_world_mask);
    }
}

jl_typemap_entry_t *jl_typemap_insert(union jl_typemap_t *cache, jl_value_t *parent,
                                      jl_tupletype_t *type,
                                      jl_tupletype_t *simpletype, jl_svec_t *guardsigs,
                                      jl_value_t *newvalue, int8_t offs,
                                      const struct jl_typemap_info *tparams,
                                      size_t min_world, size_t max_world,
                                      jl_value_t **overwritten)
{
    jl_ptls_t ptls = jl_get_ptls_states();
    assert(min_world > 0 && max_world > 0);
    if (!simpletype)
        simpletype = (jl_tupletype_t*)jl_nothing;
    jl_value_t *ttype = jl_unwrap_unionall((jl_value_t*)type);

    if ((jl_value_t*)simpletype == jl_nothing) {
        jl_typemap_entry_t *ml = jl_typemap_assoc_by_type(*cache, (jl_value_t*)type, NULL, 0, offs, min_world, 0);
        if (ml && ml->simplesig == (void*)jl_nothing) {
            if (overwritten != NULL)
                *overwritten = ml->func.value;
            if (newvalue == ml->func.value) // no change. TODO: involve world in computation!
                return ml;
            if (newvalue == NULL)  // don't overwrite with guard entries
                return ml;
            ml->max_world = min_world - 1;
        }
    }
}
