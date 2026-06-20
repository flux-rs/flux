// Lean compiler output
// Module: Enums.List00.Basic
// Imports: public import Init public import Enums.List00.Flux.Checking.Never public import Enums.List00.Flux.Checking.Empty public import Enums.List00.Flux.Checking.Len public import Enums.List00.Flux.Checking.Head public import Enums.List00.Flux.Checking.Tail public import Enums.List00.Flux.Checking.Clone public import Enums.List00.Flux.Checking.Append public import Enums.List00.Flux.Checking.Mappend public import Enums.List00.Flux.Checking.GetNth
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
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Never(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Empty(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Len(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Head(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Tail(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Clone(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Append(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_Mappend(uint8_t builtin);
lean_object* initialize_lean__bench__all_Enums_List00_Flux_Checking_GetNth(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Enums_List00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Never(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Len(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Head(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Tail(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Clone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Append(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_Mappend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Enums_List00_Flux_Checking_GetNth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
