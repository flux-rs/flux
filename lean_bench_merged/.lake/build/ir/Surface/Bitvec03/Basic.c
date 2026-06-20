// Lean compiler output
// Module: Surface.Bitvec03.Basic
// Imports: public import Init public import Surface.Bitvec03.Flux.Checking.TestShlA public import Surface.Bitvec03.Flux.Checking.TestShlB public import Surface.Bitvec03.Flux.Checking.TestShrA public import Surface.Bitvec03.Flux.Checking.TestShrB public import Surface.Bitvec03.Flux.Checking.TestOrA public import Surface.Bitvec03.Flux.Checking.TestOrB public import Surface.Bitvec03.Flux.Checking.TestAndA public import Surface.Bitvec03.Flux.Checking.TestAndB
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
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShlA(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShlB(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShrA(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShrB(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestOrA(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestOrB(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestAndA(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestAndB(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Bitvec03_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShlA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShlB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShrA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestShrB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestOrA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestOrB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestAndA(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Bitvec03_Flux_Checking_TestAndB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
