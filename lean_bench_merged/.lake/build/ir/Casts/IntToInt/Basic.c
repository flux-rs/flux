// Lean compiler output
// Module: Casts.IntToInt.Basic
// Imports: public import Init public import Casts.IntToInt.Flux.Checking.BoolInt public import Casts.IntToInt.Flux.Checking.BoolUint public import Casts.IntToInt.Flux.Checking.UintUintLossless public import Casts.IntToInt.Flux.Checking.IntIntLossless public import Casts.IntToInt.Flux.Checking.UintIntLossless public import Casts.IntToInt.Flux.Checking.UnsignedToUsize public import Casts.IntToInt.Flux.Checking.UintUintLossy public import Casts.IntToInt.Flux.Checking.UintUintLossless2 public import Casts.IntToInt.Flux.Checking.Test64 public import Casts.IntToInt.Flux.Checking.Test32
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
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_BoolInt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_BoolUint(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossless(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_IntIntLossless(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintIntLossless(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UnsignedToUsize(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossy(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossless2(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_Test64(uint8_t builtin);
lean_object* initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_Test32(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Casts_IntToInt_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_BoolInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_BoolUint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossless(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_IntIntLossless(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintIntLossless(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UnsignedToUsize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_UintUintLossless2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_Test64(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Casts_IntToInt_Flux_Checking_Test32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
