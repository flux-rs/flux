// Lean compiler output
// Module: Surface.Heapsort.Basic
// Imports: public import Init public import Surface.Heapsort.Flux.Checking.RvecImpl__3__Index public import Surface.Heapsort.Flux.Checking.RvecImpl__4__IndexMut public import Surface.Heapsort.Flux.Checking.HeapSort public import Surface.Heapsort.Flux.Checking.ShiftDown
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
lean_object* initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_RvecImpl____3____Index(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_RvecImpl____4____IndexMut(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_HeapSort(uint8_t builtin);
lean_object* initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_ShiftDown(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_Heapsort_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_RvecImpl____3____Index(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_RvecImpl____4____IndexMut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_HeapSort(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Surface_Heapsort_Flux_Checking_ShiftDown(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
