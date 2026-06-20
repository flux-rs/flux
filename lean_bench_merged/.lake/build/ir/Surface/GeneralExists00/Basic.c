// Lean compiler output
// Module: Surface.GeneralExists00.Basic
// Imports: public import Init public import Surface.GeneralExists00.Flux.Checking.Test00 public import Surface.GeneralExists00.Flux.Checking.Test01 public import Surface.GeneralExists00.Flux.Checking.Test02 public import Surface.GeneralExists00.Flux.Checking.Test03 public import Surface.GeneralExists00.Flux.Checking.Test04 public import Surface.GeneralExists00.Flux.Checking.Test05 public import Surface.GeneralExists00.Flux.Checking.Test00F public import Surface.GeneralExists00.Flux.Checking.Test01F public import Surface.GeneralExists00.Flux.Checking.Test02F public import Surface.GeneralExists00.Flux.Checking.Test03F public import Surface.GeneralExists00.Flux.Checking.Test04F public import Surface.GeneralExists00.Flux.Checking.Test05F
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
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test00(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test01(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test02(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test03(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test04(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test05(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test00F(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test01F(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test02F(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test03F(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test04F(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test05F(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_GeneralExists00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test00(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test01(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test02(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test03(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test04(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test05(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test00F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test01F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test02F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test03F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test04F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_GeneralExists00_Flux_Checking_Test05F(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
