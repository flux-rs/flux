// Lean compiler output
// Module: Surface.BvOrd.Basic
// Imports: public import Init public import Surface.BvOrd.Flux.Checking.TrivialLe public import Surface.BvOrd.Flux.Checking.TrivialLt public import Surface.BvOrd.Flux.Checking.TrivialGe public import Surface.BvOrd.Flux.Checking.TrivialGt public import Surface.BvOrd.Flux.Checking.RealExample public import Surface.BvOrd.Flux.Checking.LtImp public import Surface.BvOrd.Flux.Checking.LeImp public import Surface.BvOrd.Flux.Checking.GtImp public import Surface.BvOrd.Flux.Checking.GeImp
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
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialLe(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialLt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialGe(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialGt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_RealExample(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_LtImp(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_LeImp(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_GtImp(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_GeImp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_BvOrd_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialLe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialLt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialGe(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_TrivialGt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_RealExample(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_LtImp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_LeImp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_GtImp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_BvOrd_Flux_Checking_GeImp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
