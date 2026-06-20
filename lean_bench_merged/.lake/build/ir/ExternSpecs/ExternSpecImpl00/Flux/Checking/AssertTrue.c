// Lean compiler output
// Module: ExternSpecs.ExternSpecImpl00.Flux.Checking.AssertTrue
// Imports: public import Init public import ExternSpecs.ExternSpecImpl00.Flux.VC.AssertTrue public import ExternSpecs.ExternSpecImpl00.User.Proof.AssertTrueProof
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
lean_object* initialize_lean__bench__all_ExternSpecs_ExternSpecImpl00_Flux_VC_AssertTrue(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_ExternSpecImpl00_User_Proof_AssertTrueProof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_ExternSpecImpl00_Flux_Checking_AssertTrue(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_ExternSpecImpl00_Flux_VC_AssertTrue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_ExternSpecImpl00_User_Proof_AssertTrueProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
