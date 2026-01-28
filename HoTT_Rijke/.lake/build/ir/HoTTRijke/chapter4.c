// Lean compiler output
// Module: HoTTRijke.chapter4
// Imports: Init HoTTRijke.chapter3
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
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list___rarg(lean_object*);
static lean_object* l_chapter4__lists_l___closed__5;
lean_object* l_chapter3__integers_predZ(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_map__list___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_prod__list___boxed(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_list__length(lean_object*);
static lean_object* l_chapter4__lists_l2___closed__3;
LEAN_EXPORT lean_object* l_chapter4__lists_l2;
static lean_object* l_chapter4__lists_l___closed__1;
LEAN_EXPORT lean_object* l_chapter4__integers_subtractNaturalFromZ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_subtractNaturalFromZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_sum__list___boxed(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_addNaturalToZ___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_myAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_map__list(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_l___closed__4;
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_multNaturalWithZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_multNaturalWithZ___boxed(lean_object*, lean_object*);
extern lean_object* l_chapter3__integers_Zzero;
LEAN_EXPORT lean_object* l_chapter4__integers_myMult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_l2___closed__2;
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list___rarg(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_l___closed__2;
lean_object* l_chapter3__integers_negative(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_addNaturalToZ(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_ll;
LEAN_EXPORT lean_object* l_chapter4__lists_list__string(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_list__length___rarg(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_list__string___closed__1;
LEAN_EXPORT lean_object* l_chapter4__integers_myAdd___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list(lean_object*);
static lean_object* l_chapter4__lists_l2___closed__1;
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list___rarg(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_ll___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_ll___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_chapter4__lists_l___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_prod__list(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_reverse__list(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__integers_myMult___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_reverse__list___rarg(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_l;
LEAN_EXPORT lean_object* l_chapter4__lists_sum__list(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_list__length___rarg___boxed(lean_object*);
lean_object* l_chapter3__integers_succZ(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_chapter4__lists_list__string___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_list__string(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_chapter4__lists_list__string___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_chapter4__lists_list__string(x_4);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
}
static lean_object* _init_l_chapter4__lists_l___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_chapter4__lists_l___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_chapter4__lists_l___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = l_chapter4__lists_l___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l_chapter4__lists_l___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l() {
_start:
{
lean_object* x_1; 
x_1 = l_chapter4__lists_l___closed__5;
return x_1;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_list__length___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_chapter4__lists_list__length___rarg(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_list__length(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_chapter4__lists_list__length___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_list__length___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_chapter4__lists_list__length___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
lean_inc(x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_chapter4__lists_nth__list___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_nth__list___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__lists_nth__list___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_chapter4__lists_fold__list___rarg(x_1, x_2, x_5);
x_7 = lean_apply_2(x_1, x_4, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_chapter4__lists_fold__list___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_fold__list___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_chapter4__lists_fold__list___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_map__list___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_apply_1(x_1, x_5);
x_8 = l_chapter4__lists_map__list___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_apply_1(x_1, x_9);
x_12 = l_chapter4__lists_map__list___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_map__list(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_chapter4__lists_map__list___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_sum__list(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_chapter4__lists_sum__list(x_4);
x_6 = lean_nat_add(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_sum__list___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_chapter4__lists_sum__list(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_prod__list(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_chapter4__lists_prod__list(x_4);
x_6 = lean_nat_mul(x_3, x_5);
lean_dec(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_prod__list___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_chapter4__lists_prod__list(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_chapter4__lists_concat__list___rarg(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = l_chapter4__lists_concat__list___rarg(x_1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_chapter4__lists_concat__list___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_concat__list___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__lists_concat__list___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = l_chapter4__lists_l2___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = l_chapter4__lists_l2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_l2() {
_start:
{
lean_object* x_1; 
x_1 = l_chapter4__lists_l2___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_chapter4__lists_flatten__list___rarg(x_4);
x_6 = l_chapter4__lists_concat__list___rarg(x_3, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_chapter4__lists_flatten__list___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_flatten__list___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_chapter4__lists_flatten__list___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_chapter4__lists_ll___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_chapter4__lists_l;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_ll___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_chapter4__lists_l2;
x_2 = l_chapter4__lists_ll___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_chapter4__lists_ll() {
_start:
{
lean_object* x_1; 
x_1 = l_chapter4__lists_ll___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_reverse__list___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
lean_ctor_set(x_1, 1, x_5);
x_6 = l_chapter4__lists_reverse__list___rarg(x_4);
x_7 = l_chapter4__lists_concat__list___rarg(x_1, x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_chapter4__lists_reverse__list___rarg(x_9);
x_13 = l_chapter4__lists_concat__list___rarg(x_11, x_12);
lean_dec(x_11);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__lists_reverse__list(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_chapter4__lists_reverse__list___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_addNaturalToZ(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_chapter3__integers_succZ(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_chapter3__integers_succZ(x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_addNaturalToZ___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__integers_addNaturalToZ(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_subtractNaturalFromZ(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_chapter3__integers_predZ(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_chapter3__integers_predZ(x_2);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_subtractNaturalFromZ___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__integers_subtractNaturalFromZ(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_myAdd(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_chapter4__integers_subtractNaturalFromZ(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = l_chapter4__integers_addNaturalToZ(x_6, x_1);
return x_7;
}
else
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_myAdd___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__integers_myAdd(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_multNaturalWithZ(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_4 = l_chapter4__integers_multNaturalWithZ(x_1, x_3);
x_5 = l_chapter4__integers_myAdd(x_1, x_4);
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_multNaturalWithZ___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__integers_multNaturalWithZ(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_myMult(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_chapter4__integers_multNaturalWithZ(x_1, x_3);
x_5 = l_chapter3__integers_negative(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = l_chapter4__integers_multNaturalWithZ(x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_chapter3__integers_Zzero;
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_chapter4__integers_myMult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_chapter4__integers_myMult(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HoTTRijke_chapter3(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HoTTRijke_chapter4(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HoTTRijke_chapter3(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_chapter4__lists_list__string___closed__1 = _init_l_chapter4__lists_list__string___closed__1();
lean_mark_persistent(l_chapter4__lists_list__string___closed__1);
l_chapter4__lists_l___closed__1 = _init_l_chapter4__lists_l___closed__1();
lean_mark_persistent(l_chapter4__lists_l___closed__1);
l_chapter4__lists_l___closed__2 = _init_l_chapter4__lists_l___closed__2();
lean_mark_persistent(l_chapter4__lists_l___closed__2);
l_chapter4__lists_l___closed__3 = _init_l_chapter4__lists_l___closed__3();
lean_mark_persistent(l_chapter4__lists_l___closed__3);
l_chapter4__lists_l___closed__4 = _init_l_chapter4__lists_l___closed__4();
lean_mark_persistent(l_chapter4__lists_l___closed__4);
l_chapter4__lists_l___closed__5 = _init_l_chapter4__lists_l___closed__5();
lean_mark_persistent(l_chapter4__lists_l___closed__5);
l_chapter4__lists_l = _init_l_chapter4__lists_l();
lean_mark_persistent(l_chapter4__lists_l);
l_chapter4__lists_l2___closed__1 = _init_l_chapter4__lists_l2___closed__1();
lean_mark_persistent(l_chapter4__lists_l2___closed__1);
l_chapter4__lists_l2___closed__2 = _init_l_chapter4__lists_l2___closed__2();
lean_mark_persistent(l_chapter4__lists_l2___closed__2);
l_chapter4__lists_l2___closed__3 = _init_l_chapter4__lists_l2___closed__3();
lean_mark_persistent(l_chapter4__lists_l2___closed__3);
l_chapter4__lists_l2 = _init_l_chapter4__lists_l2();
lean_mark_persistent(l_chapter4__lists_l2);
l_chapter4__lists_ll___closed__1 = _init_l_chapter4__lists_ll___closed__1();
lean_mark_persistent(l_chapter4__lists_ll___closed__1);
l_chapter4__lists_ll___closed__2 = _init_l_chapter4__lists_ll___closed__2();
lean_mark_persistent(l_chapter4__lists_ll___closed__2);
l_chapter4__lists_ll = _init_l_chapter4__lists_ll();
lean_mark_persistent(l_chapter4__lists_ll);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
