// Lean compiler output
// Module: Surface.StaticSpec00.Basic
// Imports: public import Init public import Surface.StaticSpec00.Flux.Checking.BLAH public import Surface.StaticSpec00.Flux.Checking.TestBlah public import Surface.StaticSpec00.Flux.Checking.FROG public import Surface.StaticSpec00.Flux.Checking.TestFrog public import Surface.StaticSpec00.Flux.Checking.HOG public import Surface.StaticSpec00.Flux.Checking.TestHog
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
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_BLAH(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestBlah(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_FROG(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestFrog(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_HOG(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestHog(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_StaticSpec00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_BLAH(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestBlah(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_FROG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestFrog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_HOG(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_StaticSpec00_Flux_Checking_TestHog(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
