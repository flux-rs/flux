// Lean compiler output
// Module: Surface.LocalQual00.Flux.Struct.Pair
// Imports: public import Init public import Surface.LocalQual00.Flux.Prelude
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t lp_lean__bench__all_F_instInhabitedPair_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean__bench__all_F_instInhabitedPair_default___closed__0;
static lean_once_cell_t lp_lean__bench__all_F_instInhabitedPair_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean__bench__all_F_instInhabitedPair_default___closed__1;
LEAN_EXPORT lean_object* lp_lean__bench__all_F_instInhabitedPair_default;
LEAN_EXPORT lean_object* lp_lean__bench__all_F_instInhabitedPair;
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPair_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPair_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_lean__bench__all_F_instInhabitedPair_default___closed__0, &lp_lean__bench__all_F_instInhabitedPair_default___closed__0_once, _init_lp_lean__bench__all_F_instInhabitedPair_default___closed__0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPair_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_lean__bench__all_F_instInhabitedPair_default___closed__1, &lp_lean__bench__all_F_instInhabitedPair_default___closed__1_once, _init_lp_lean__bench__all_F_instInhabitedPair_default___closed__1);
return x_1;
}
}
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPair(void) {
_start:
{
lean_object* x_1; 
x_1 = lp_lean__bench__all_F_instInhabitedPair_default;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_LocalQual00_Flux_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_LocalQual00_Flux_Struct_Pair(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_LocalQual00_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean__bench__all_F_instInhabitedPair_default = _init_lp_lean__bench__all_F_instInhabitedPair_default();
lean_mark_persistent(lp_lean__bench__all_F_instInhabitedPair_default);
lp_lean__bench__all_F_instInhabitedPair = _init_lp_lean__bench__all_F_instInhabitedPair();
lean_mark_persistent(lp_lean__bench__all_F_instInhabitedPair);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
