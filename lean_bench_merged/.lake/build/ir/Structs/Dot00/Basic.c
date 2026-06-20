// Lean compiler output
// Module: Structs.Dot00.Basic
// Imports: public import Init public import Structs.Dot00.Flux.Checking.SumPair public import Structs.Dot00.Flux.Checking.SumPair2 public import Structs.Dot00.Flux.Checking.Fst public import Structs.Dot00.Flux.Checking.MkPair1 public import Structs.Dot00.Flux.Checking.MkPair2 public import Structs.Dot00.Flux.Checking.MkPairWithFirst public import Structs.Dot00.Flux.Checking.MkPairWithPos public import Structs.Dot00.Flux.Checking.MkPairWithBound
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
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_SumPair(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_SumPair2(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_Fst(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPair1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPair2(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithFirst(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithPos(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithBound(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Structs_Dot00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_SumPair(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_SumPair2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_Fst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPair1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPair2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithFirst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Dot00_Flux_Checking_MkPairWithBound(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
