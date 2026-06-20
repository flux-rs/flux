// Lean compiler output
// Module: Detached.DetachImpl02.Basic
// Imports: public import Init public import Detached.DetachImpl02.Flux.Checking.Impl__0__Zero public import Detached.DetachImpl02.Flux.Checking.Impl__0__Succ public import Detached.DetachImpl02.Flux.Checking.Impl__1__From public import Detached.DetachImpl02.Flux.Checking.Impl__2__From public import Detached.DetachImpl02.Flux.Checking.TestA public import Detached.DetachImpl02.Flux.Checking.TestB public import Detached.DetachImpl02.Flux.Checking.TestC
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
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____0____Zero(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____0____Succ(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____1____From(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____2____From(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestA(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestB(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestC(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Detached_DetachImpl02_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____0____Zero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____0____Succ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____1____From(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_Impl____2____From(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachImpl02_Flux_Checking_TestC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
