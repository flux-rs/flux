// Lean compiler output
// Module: Structs.Issue156.User.Proof.RvecImpl__4__IndexMutProof
// Imports: public import Init public import LeanFixpoint public import Structs.Issue156.Flux.Prelude public import Structs.Issue156.Flux.VC.RvecImpl__4__IndexMut
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
lean_object* initialize_lean__bench__all_Structs_Issue156_Flux_Prelude(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Issue156_Flux_VC_RvecImpl____4____IndexMut(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Structs_Issue156_User_Proof_RvecImpl____4____IndexMutProof(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LeanFixpoint_LeanFixpoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Issue156_Flux_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Issue156_Flux_VC_RvecImpl____4____IndexMut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
