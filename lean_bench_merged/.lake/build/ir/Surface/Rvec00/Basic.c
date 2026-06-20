// Lean compiler output
// Module: Surface.Rvec00.Basic
// Imports: public import Init public import Surface.Rvec00.Flux.Checking.Test3 public import Surface.Rvec00.Flux.Checking.RvecImpl__3__Index public import Surface.Rvec00.Flux.Checking.RvecImpl__4__IndexMut public import Surface.Rvec00.Flux.Checking.Test0 public import Surface.Rvec00.Flux.Checking.Test1 public import Surface.Rvec00.Flux.Checking.Test2
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
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test3(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_RvecImpl____3____Index(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_RvecImpl____4____IndexMut(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test0(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Rvec00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_RvecImpl____3____Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_RvecImpl____4____IndexMut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test0(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Rvec00_Flux_Checking_Test2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
