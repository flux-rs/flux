// Lean compiler output
// Module: Surface.RefinedFnInTrait02.Flux.Checking.Impl__0__Foo2
// Imports: public import Init public import Surface.RefinedFnInTrait02.Flux.VC.Impl__0__Foo2 public import Surface.RefinedFnInTrait02.User.Proof.Impl__0__Foo2Proof
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
lean_object* initialize_lean__bench__all_Surface_RefinedFnInTrait02_Flux_VC_Impl____0____Foo2(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RefinedFnInTrait02_User_Proof_Impl____0____Foo2Proof(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_RefinedFnInTrait02_Flux_Checking_Impl____0____Foo2(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RefinedFnInTrait02_Flux_VC_Impl____0____Foo2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RefinedFnInTrait02_User_Proof_Impl____0____Foo2Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
