// Lean compiler output
// Module: FoldUnfold.Test00.Basic
// Imports: public import Init public import FoldUnfold.Test00.Flux.Checking.TakeShrRef public import FoldUnfold.Test00.Flux.Checking.TakeMutRef public import FoldUnfold.Test00.Flux.Checking.TestShrRef public import FoldUnfold.Test00.Flux.Checking.TestMutRef public import FoldUnfold.Test00.Flux.Checking.TestStrgRef
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
lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TakeShrRef(uint8_t builtin);
lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TakeMutRef(uint8_t builtin);
lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestShrRef(uint8_t builtin);
lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestMutRef(uint8_t builtin);
lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestStrgRef(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_FoldUnfold_Test00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TakeShrRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TakeMutRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestShrRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestMutRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_FoldUnfold_Test00_Flux_Checking_TestStrgRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
