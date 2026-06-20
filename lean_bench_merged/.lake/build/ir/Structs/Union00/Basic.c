// Lean compiler output
// Module: Structs.Union00.Basic
// Imports: public import Init public import Structs.Union00.Flux.Checking.Bob public import Structs.Union00.Flux.Checking.Glob public import Structs.Union00.Flux.Checking.NewThis public import Structs.Union00.Flux.Checking.NewThat
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
lean_object* initialize_lean__bench__all_Structs_Union00_Flux_Checking_Bob(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Union00_Flux_Checking_Glob(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Union00_Flux_Checking_NewThis(uint8_t builtin);
lean_object* initialize_lean__bench__all_Structs_Union00_Flux_Checking_NewThat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Structs_Union00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Union00_Flux_Checking_Bob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Union00_Flux_Checking_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Union00_Flux_Checking_NewThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_Structs_Union00_Flux_Checking_NewThat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
