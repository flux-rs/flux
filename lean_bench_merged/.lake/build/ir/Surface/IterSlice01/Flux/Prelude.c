// Lean compiler output
// Module: Surface.IterSlice01.Flux.Prelude
// Imports: public import Init
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
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__shiftLeft___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sshiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sshiftRight___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__uge___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__uge___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__uge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__uge___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_BitVec_slt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__sge(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sge___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__ugt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ugt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__ugt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ugt___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_BitVec_sle(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__sgt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sgt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__zeroExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__zeroExtend___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_signExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__signExtend(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__signExtend___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__shiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_shiftLeft(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__shiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_lean__bench__all_BitVec__shiftLeft(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_nat_shiftr(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_lean__bench__all_BitVec__ushiftRight___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_nat_shiftr(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ushiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_lean__bench__all_BitVec__ushiftRight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sshiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_BitVec_sshiftRight(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sshiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_lean__bench__all_BitVec__sshiftRight(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__uge___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__uge___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_lean__bench__all_BitVec__uge___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__uge(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__uge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_lean__bench__all_BitVec__uge(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__sge(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_BitVec_slt(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sge___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_lean__bench__all_BitVec__sge(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__ugt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ugt___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lp_lean__bench__all_BitVec__ugt___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__ugt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_le(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__ugt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_lean__bench__all_BitVec__ugt(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_lean__bench__all_BitVec__sgt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_BitVec_sle(x_1, x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__sgt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lp_lean__bench__all_BitVec__sgt(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__zeroExtend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_add(x_1, x_2);
x_5 = l_BitVec_setWidth(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__zeroExtend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_lean__bench__all_BitVec__zeroExtend(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__signExtend(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_nat_add(x_1, x_2);
x_5 = l_BitVec_signExtend(x_1, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_BitVec__signExtend___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_lean__bench__all_BitVec__signExtend(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_lean__bench__all_SmtMap__default___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__default___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_lean__bench__all_SmtMap__default(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
lean_inc(x_5);
x_6 = lean_apply_2(x_1, x_5, x_3);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_apply_1(x_2, x_5);
return x_8;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
lean_inc(x_4);
return x_4;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_lean__bench__all_SmtMap__store___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
lean_inc(x_9);
x_10 = lean_apply_2(x_4, x_9, x_7);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_apply_1(x_6, x_9);
return x_12;
}
else
{
lean_dec(x_9);
lean_dec(x_6);
lean_inc(x_8);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__store___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lp_lean__bench__all_SmtMap__store(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_1(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_lean__bench__all_SmtMap__select___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lp_lean__bench__all_SmtMap__select(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_lean__bench__all_Surface_IterSlice01_Flux_Prelude(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
