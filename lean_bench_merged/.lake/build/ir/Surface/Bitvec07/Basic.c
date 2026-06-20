// Lean compiler output
// Module: Surface.Bitvec07.Basic
// Imports: public import Init public import Surface.Bitvec07.Flux.Checking.TestShl8 public import Surface.Bitvec07.Flux.Checking.TestShl32 public import Surface.Bitvec07.Flux.Checking.TestShr8 public import Surface.Bitvec07.Flux.Checking.TestShr32 public import Surface.Bitvec07.Flux.Checking.TestOr8 public import Surface.Bitvec07.Flux.Checking.TestOr32 public import Surface.Bitvec07.Flux.Checking.TestAnd8 public import Surface.Bitvec07.Flux.Checking.TestAnd32
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
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShl8(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShl32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShr8(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShr32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestOr8(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestOr32(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestAnd8(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestAnd32(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Bitvec07_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShl8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShl32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShr8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestShr32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestOr8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestOr32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestAnd8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec07_Flux_Checking_TestAnd32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
