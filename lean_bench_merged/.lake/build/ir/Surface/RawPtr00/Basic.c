// Lean compiler output
// Module: Surface.RawPtr00.Basic
// Imports: public import Init public import Surface.RawPtr00.Flux.Checking.ConstSingle public import Surface.RawPtr00.Flux.Checking.MutSingle public import Surface.RawPtr00.Flux.Checking.ConstParts public import Surface.RawPtr00.Flux.Checking.MutParts public import Surface.RawPtr00.Flux.Checking.ConstPartsConstrained public import Surface.RawPtr00.Flux.Checking.MutPartsConstrained public import Surface.RawPtr00.Flux.Checking.ConstFieldProjections public import Surface.RawPtr00.Flux.Checking.MutFieldProjections public import Surface.RawPtr00.Flux.Checking.ConstShortFieldProjections public import Surface.RawPtr00.Flux.Checking.MutShortFieldProjections
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
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstSingle(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutSingle(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstParts(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutParts(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstPartsConstrained(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutPartsConstrained(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstFieldProjections(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutFieldProjections(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstShortFieldProjections(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutShortFieldProjections(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_RawPtr00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstSingle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutSingle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutParts(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstPartsConstrained(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutPartsConstrained(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstFieldProjections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutFieldProjections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_ConstShortFieldProjections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_RawPtr00_Flux_Checking_MutShortFieldProjections(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
