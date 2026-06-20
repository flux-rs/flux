// Lean compiler output
// Module: Array.Array04.User.Proof.TestRepeatReturnPosProof
// Imports: public import Init public import LeanFixpoint public import Array.Array04.Flux.Prelude public import Array.Array04.Flux.VC.TestRepeatReturnPos
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
lean_object* initialize_LeanFixpoint_LeanFixpoint(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Prelude(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_VC_TestRepeatReturnPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Array_Array04_User_Proof_TestRepeatReturnPosProof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanFixpoint_LeanFixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_VC_TestRepeatReturnPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
