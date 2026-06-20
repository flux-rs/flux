// Lean compiler output
// Module: Enums.Option00.Basic
// Imports: public import Init public import Enums.Option00.Flux.Checking.Test1 public import Enums.Option00.Flux.Checking.Test3 public import Enums.Option00.Flux.Checking.TestOptSpecs public import Enums.Option00.Flux.Checking.TestSafeDiv public import Enums.Option00.Flux.Checking.MyUnwrap public import Enums.Option00.Flux.Checking.MySome public import Enums.Option00.Flux.Checking.SafeDiv
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
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_Test1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_Test3(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_TestOptSpecs(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_TestSafeDiv(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_MyUnwrap(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_MySome(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_Option00_Flux_Checking_SafeDiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Enums_Option00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_Test1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_Test3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_TestOptSpecs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_TestSafeDiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_MyUnwrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_MySome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_Option00_Flux_Checking_SafeDiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
