// Lean compiler output
// Module: ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl5BITS
// Imports: public import Init public import ExternSpecs.FluxCoreNum00.Flux.Prelude
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
static lean_once_cell_t lp_lean__bench__all_F_num__impl__5__BITS___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_lean__bench__all_F_num__impl__5__BITS___closed__0;
LEAN_EXPORT lean_object* lp_lean__bench__all_F_num__impl__5__BITS;
static lean_object* _init_lp_lean__bench__all_F_num__impl__5__BITS___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_lean__bench__all_F_num__impl__5__BITS(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_lean__bench__all_F_num__impl__5__BITS___closed__0, &lp_lean__bench__all_F_num__impl__5__BITS___closed__0_once, _init_lp_lean__bench__all_F_num__impl__5__BITS___closed__0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum00_Flux_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum00_Flux_Fun_NumImpl5BITS(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum00_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean__bench__all_F_num__impl__5__BITS = _init_lp_lean__bench__all_F_num__impl__5__BITS();
lean_mark_persistent(lp_lean__bench__all_F_num__impl__5__BITS);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
