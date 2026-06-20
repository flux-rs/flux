// Lean compiler output
// Module: Surface.Simplex.Basic
// Imports: public import Init public import Surface.Simplex.Flux.Checking.IsNeg public import Surface.Simplex.Flux.Checking.Unb1 public import Surface.Simplex.Flux.Checking.EnterVar public import Surface.Simplex.Flux.Checking.DepartVar public import Surface.Simplex.Flux.Checking.InitRatioI public import Surface.Simplex.Flux.Checking.InitRatioC public import Surface.Simplex.Flux.Checking.RowOp public import Surface.Simplex.Flux.Checking.Simplex
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_IsNeg(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_Unb1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_EnterVar(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_DepartVar(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_InitRatioI(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_InitRatioC(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_RowOp(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Simplex_Flux_Checking_Simplex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Simplex_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_IsNeg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_Unb1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_EnterVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_DepartVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_InitRatioI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_InitRatioC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_RowOp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Simplex_Flux_Checking_Simplex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
