// Lean compiler output
// Module: Surface.Operators.Basic
// Imports: public import Init public import Surface.Operators.Flux.Checking.TestNeg01 public import Surface.Operators.Flux.Checking.TestNeq01 public import Surface.Operators.Flux.Checking.TestNot01 public import Surface.Operators.Flux.Checking.TestNot03 public import Surface.Operators.Flux.Checking.TestNeg00 public import Surface.Operators.Flux.Checking.TestDiv public import Surface.Operators.Flux.Checking.TestNeq00 public import Surface.Operators.Flux.Checking.TestNot00 public import Surface.Operators.Flux.Checking.TestNot02
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
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeg01(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeq01(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot01(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot03(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeg00(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestDiv(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeq00(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot00(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot02(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Operators_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeg01(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeq01(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot01(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot03(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeg00(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestDiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNeq00(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot00(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Operators_Flux_Checking_TestNot02(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
