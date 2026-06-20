// Lean compiler output
// Module: ExternSpecs.FluxCoreResult00.Basic
// Imports: public import Init public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestIsOkErr public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestIsOkAfterBranch public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestOk public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestErr public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestOkErrBranch public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestAsRef public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestAsMut public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestMap public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestMapPreservesOk public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestMapErr public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestMapErrPreservesOk public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestExpect public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestUnwrap public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestUnwrapErr public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestUnwrapAfterCheck public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestExpectErr public import ExternSpecs.FluxCoreResult00.Flux.Checking.TestExpectErrAfterCheck
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
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestIsOkErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestIsOkAfterBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestOkErrBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestAsRef(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestAsMut(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMap(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapPreservesOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapErrPreservesOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpect(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrap(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrapErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrapAfterCheck(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpectErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpectErrAfterCheck(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestIsOkErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestIsOkAfterBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestOkErrBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestAsRef(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestAsMut(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapPreservesOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestMapErrPreservesOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrapErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestUnwrapAfterCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpectErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreResult00_Flux_Checking_TestExpectErrAfterCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
