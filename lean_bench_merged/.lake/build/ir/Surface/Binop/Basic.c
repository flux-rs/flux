// Lean compiler output
// Module: Surface.Binop.Basic
// Imports: public import Init public import Surface.Binop.Flux.Checking.UintShr public import Surface.Binop.Flux.Checking.Test1 public import Surface.Binop.Flux.Checking.Test2 public import Surface.Binop.Flux.Checking.Test3 public import Surface.Binop.Flux.Checking.BitwiseOr public import Surface.Binop.Flux.Checking.BitwiseShlI32I32 public import Surface.Binop.Flux.Checking.BitwiseShlI32U32 public import Surface.Binop.Flux.Checking.BitwiseShlU32I32 public import Surface.Binop.Flux.Checking.BitwiseShlU32U32 public import Surface.Binop.Flux.Checking.BitwiseShrI32I32 public import Surface.Binop.Flux.Checking.BitwiseShrI32U32 public import Surface.Binop.Flux.Checking.BitwiseShrU32I32 public import Surface.Binop.Flux.Checking.BitwiseShrU32U32 public import Surface.Binop.Flux.Checking.BitwiseNotU32 public import Surface.Binop.Flux.Checking.BitwiseNotI32 public import Surface.Binop.Flux.Checking.LogicalOr public import Surface.Binop.Flux.Checking.LogicalOrFt public import Surface.Binop.Flux.Checking.LogicalOrFf public import Surface.Binop.Flux.Checking.LogicalNotT public import Surface.Binop.Flux.Checking.LogicalNotF public import Surface.Binop.Flux.Checking.NegateF32 public import Surface.Binop.Flux.Checking.MultiplyF32 public import Surface.Binop.Flux.Checking.SubtractF32 public import Surface.Binop.Flux.Checking.DivideF32
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
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_UintShr(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test1(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test2(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test3(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseOr(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlI32I32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlI32U32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlU32I32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlU32U32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrI32I32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrI32U32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrU32I32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrU32U32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseNotU32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseNotI32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOr(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOrFt(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOrFf(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalNotT(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalNotF(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_NegateF32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_MultiplyF32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_SubtractF32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Binop_Flux_Checking_DivideF32(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Binop_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_UintShr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_Test3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseOr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlI32I32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlI32U32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlU32I32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShlU32U32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrI32I32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrI32U32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrU32I32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseShrU32U32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseNotU32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_BitwiseNotI32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOrFt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalOrFf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalNotT(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_LogicalNotF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_NegateF32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_MultiplyF32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_SubtractF32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Binop_Flux_Checking_DivideF32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
