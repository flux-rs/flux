// Lean compiler output
// Module: Enums.Pred00.Flux.Struct.Pred
// Imports: public import Init public import Enums.Pred00.Flux.Prelude
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
LEAN_EXPORT lean_object* lp_lean__bench__all_F_instInhabitedPred_default;
LEAN_EXPORT lean_object* lp_lean__bench__all_F_instInhabitedPred;
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPred_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_lean__bench__all_F_instInhabitedPred(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Pred00_Flux_Prelude(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Enums_Pred00_Flux_Struct_Pred(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Pred00_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_lean__bench__all_F_instInhabitedPred_default = _init_lp_lean__bench__all_F_instInhabitedPred_default();
lean_mark_persistent(lp_lean__bench__all_F_instInhabitedPred_default);
lp_lean__bench__all_F_instInhabitedPred = _init_lp_lean__bench__all_F_instInhabitedPred();
lean_mark_persistent(lp_lean__bench__all_F_instInhabitedPred);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
