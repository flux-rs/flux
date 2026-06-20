// Lean compiler output
// Module: Surface.ToInt01.Basic
// Imports: public import Init public import Surface.ToInt01.Flux.Checking.TestIntToInt public import Surface.ToInt01.Flux.Checking.TestCharToInt public import Surface.ToInt01.Flux.Checking.TestCharToIntMax public import Surface.ToInt01.Flux.Checking.TestBoolToInt public import Surface.ToInt01.Flux.Checking.TestBoolToIntWithIf public import Surface.ToInt01.Flux.Checking.TestUsizeToFloat public import Surface.ToInt01.Flux.Checking.Foo
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
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestIntToInt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestCharToInt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestCharToIntMax(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestBoolToInt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestBoolToIntWithIf(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestUsizeToFloat(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_Foo(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_ToInt01_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestIntToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestCharToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestCharToIntMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestBoolToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestBoolToIntWithIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_TestUsizeToFloat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_ToInt01_Flux_Checking_Foo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
