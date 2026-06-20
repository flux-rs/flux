// Lean compiler output
// Module: ExternSpecs.FluxCorePtr00.User.Proof.WriteIxI32Proof
// Imports: public import Init public import LeanFixpoint public import ExternSpecs.FluxCorePtr00.Flux.Prelude public import ExternSpecs.FluxCorePtr00.Flux.VC.WriteIxI32
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
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCorePtr00_Flux_Prelude(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCorePtr00_Flux_VC_WriteIxI32(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCorePtr00_User_Proof_WriteIxI32Proof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanFixpoint_LeanFixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCorePtr00_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCorePtr00_Flux_VC_WriteIxI32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
