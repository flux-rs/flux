// Lean compiler output
// Module: ExternSpecs.FluxCoreSlice00.Basic
// Imports: public import Init public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestIndexAfterLen public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestIndexAfterIsEmpty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestFirstBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestIterAsSliceLen public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestFirstMutEmpty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestFirstMutNonempty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestFirstMutBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestLastMutBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestLastConcrete public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestLastEmpty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestLastBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestGetInBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestGetOutOfBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestGetConcrete public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitFirstEmpty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitFirstNonempty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitFirstBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitFirstTailLen public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitLastEmpty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitLastNonempty public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitLastBranch public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitLastInitLen public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestGetMutInBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestGetMutOutOfBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtMutLengths public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtMutCheckedInBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtMutCheckedLengths public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtCheckedInBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtCheckedOutOfBounds public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestSplitAtCheckedLengths public import ExternSpecs.FluxCoreSlice00.Flux.Checking.TestRangeIndexInBounds
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
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIndexAfterLen(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIndexAfterIsEmpty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIterAsSliceLen(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutEmpty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutNonempty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastMutBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastEmpty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetInBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetOutOfBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstEmpty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstNonempty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstTailLen(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastEmpty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastNonempty(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastBranch(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastInitLen(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetMutInBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetMutOutOfBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutLengths(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutCheckedInBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutCheckedLengths(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedInBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedOutOfBounds(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedLengths(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestRangeIndexInBounds(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIndexAfterLen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIndexAfterIsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestIterAsSliceLen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutNonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestFirstMutBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastMutBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestLastBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetInBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetOutOfBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstNonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitFirstTailLen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastNonempty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastBranch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitLastInitLen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetMutInBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestGetMutOutOfBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutCheckedInBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtMutCheckedLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedInBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedOutOfBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestSplitAtCheckedLengths(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreSlice00_Flux_Checking_TestRangeIndexInBounds(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
