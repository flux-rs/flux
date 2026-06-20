// Lean compiler output
// Module: TraitObject.Dyn00.Flux.Checking.Impl__0__Noise
// Imports: public import Init public import TraitObject.Dyn00.Flux.VC.Impl__0__Noise public import TraitObject.Dyn00.User.Proof.Impl__0__NoiseProof
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
lean_object* initialize_lean__bench__all_TraitObject_Dyn00_Flux_VC_Impl____0____Noise(uint8_t builtin);
lean_object* initialize_lean__bench__all_TraitObject_Dyn00_User_Proof_Impl____0____NoiseProof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_TraitObject_Dyn00_Flux_Checking_Impl____0____Noise(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_TraitObject_Dyn00_Flux_VC_Impl____0____Noise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_TraitObject_Dyn00_User_Proof_Impl____0____NoiseProof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
