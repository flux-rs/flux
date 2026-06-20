// Lean compiler output
// Module: Array.Array04.Basic
// Imports: public import Init public import Array.Array04.Flux.Checking.TestRepeatArrayAssignment public import Array.Array04.Flux.Checking.TestRepeatArrayIndexRead public import Array.Array04.Flux.Checking.TestRepeatWriteThenRead public import Array.Array04.Flux.Checking.TestRepeatReturnGeqZero public import Array.Array04.Flux.Checking.TestRepeatReturnPos
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
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatArrayAssignment(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatArrayIndexRead(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatWriteThenRead(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatReturnGeqZero(uint8_t builtin);
lean_object* initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatReturnPos(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Array_Array04_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatArrayAssignment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatArrayIndexRead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatWriteThenRead(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatReturnGeqZero(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Array_Array04_Flux_Checking_TestRepeatReturnPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
