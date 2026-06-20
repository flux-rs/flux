// Lean compiler output
// Module: ExternSpecs.FluxCoreNum01.Basic
// Imports: public import Init public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedErrLow public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedErrHigh public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedConcrete public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedSuOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedSuErrNeg public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestBothBoundedSuErrHigh public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestUpperBoundedUOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestUpperBoundedUErr public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestUpperBoundedUConcrete public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestUpperBoundedUsOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestUpperBoundedUsErr public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestLowerBoundedOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestLowerBoundedErr public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestLowerBoundedConcrete public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoBothBoundedOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoBothBoundedErrLow public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoBothBoundedErrHigh public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoBothBoundedConcrete public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoUpperBoundedOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoUpperBoundedErr public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoLowerBoundedOk public import ExternSpecs.FluxCoreNum01.Flux.Checking.TestIntoLowerBoundedErr
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
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedErrLow(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedErrHigh(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuErrNeg(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuErrHigh(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUsOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUsErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedErrLow(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedErrHigh(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedConcrete(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoUpperBoundedOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoUpperBoundedErr(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoLowerBoundedOk(uint8_t builtin);
lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoLowerBoundedErr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedErrLow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedErrHigh(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuErrNeg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestBothBoundedSuErrHigh(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUsOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestUpperBoundedUsErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestLowerBoundedConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedErrLow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedErrHigh(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoBothBoundedConcrete(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoUpperBoundedOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoUpperBoundedErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoLowerBoundedOk(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_lean__bench__all_ExternSpecs_FluxCoreNum01_Flux_Checking_TestIntoLowerBoundedErr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
