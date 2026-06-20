// Lean compiler output
// Module: Detached.DetachStatic00.Basic
// Imports: public import Init public import Detached.DetachStatic00.Flux.Checking.BobBOB public import Detached.DetachStatic00.Flux.Checking.BobTest1 public import Detached.DetachStatic00.Flux.Checking.BobARR public import Detached.DetachStatic00.Flux.Checking.BobTest2
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
lean_object* initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobBOB(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobTest1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobARR(uint8_t builtin);
lean_object* initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobTest2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Detached_DetachStatic00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobBOB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobTest1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobARR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Detached_DetachStatic00_Flux_Checking_BobTest2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
