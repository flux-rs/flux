// Lean compiler output
// Module: ExternSpecs.FluxCoreOption00.Basic
// Imports: public import Init public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestExpect public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestExpectAfterCheck public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestUnwrapOr public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestUnwrapOrElse public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestAndNoneLeft public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestAndNoneRight public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestAndBothSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOrSomeLeft public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOrSomeRight public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOrBothNone public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestMapPreservesSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestMapPreservesNone public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestMapBranch public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestMapOrBranch public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestTakeSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestTakeNone public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestTakeReturnMatchesOriginal public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestReplaceLeavesSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestReplaceReturnsOldNone public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestReplaceReturnsOldSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestReplaceReturnMatchesOriginal public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOkOrSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOkOrNone public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOkOrBranch public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOkOrElseSome public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestOkOrElseBranch public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestAndThenNonePropagates public import ExternSpecs.FluxCoreOption00.Flux.Checking.TestAndThenNoneInput
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
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestExpect(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestExpectAfterCheck(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestUnwrapOr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestUnwrapOrElse(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndNoneLeft(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndNoneRight(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndBothSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrSomeLeft(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrSomeRight(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrBothNone(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapPreservesSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapPreservesNone(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapOrBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeNone(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeReturnMatchesOriginal(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceLeavesSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnsOldNone(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnsOldSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnMatchesOriginal(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrNone(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrElseSome(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrElseBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndThenNonePropagates(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndThenNoneInput(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestExpect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestExpectAfterCheck(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestUnwrapOr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestUnwrapOrElse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndNoneLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndNoneRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndBothSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrSomeLeft(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrSomeRight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOrBothNone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapPreservesSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapPreservesNone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestMapOrBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeNone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestTakeReturnMatchesOriginal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceLeavesSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnsOldNone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnsOldSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestReplaceReturnMatchesOriginal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrNone(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrElseSome(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestOkOrElseBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndThenNonePropagates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreOption00_Flux_Checking_TestAndThenNoneInput(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
