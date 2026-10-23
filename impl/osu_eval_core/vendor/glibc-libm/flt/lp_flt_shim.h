/* lazerproof shim: replaces the glibc-internal headers (math_private.h,
   math-barriers.h, math-narrow-eval.h, math-underflow.h, libm-alias-*.h,
   nan-high-order-bit.h) so these glibc 2.39 sources build standalone with
   gcc and clang.  Exports are renamed to lp_<name>f; every other external
   symbol is prefixed lp_flt_.  Nothing here changes a returned value.  */
#ifndef LP_FLT_SHIM_H
#define LP_FLT_SHIM_H

#include <errno.h>
#include <float.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>

/* Exported names (plain C ABI).  */
#define SINF lp_sinf
#define COSF lp_cosf
#define __tanf lp_tanf
#define __ieee754_asinf lp_asinf
#define __ieee754_acosf lp_acosf
#define __atanf lp_atanf
#define __expf lp_expf
#define __logf lp_logf
#define __ieee754_atan2f lp_atan2f
#define __powf lp_powf

/* Internal non-static symbols.  */
#define __kernel_tanf lp_flt_kernel_tanf
#define __sincosf_table lp_flt_sincosf_table
#define __inv_pio4 lp_flt_inv_pio4
#define __exp2f_data lp_flt_exp2f_data
#define __logf_data lp_flt_logf_data
#define __log2f_data lp_flt_log2f_data
#define __powf_log2_data lp_flt_powf_log2_data
#define __math_oflowf lp_flt_math_oflowf
#define __math_uflowf lp_flt_math_uflowf
#define __math_may_uflowf lp_flt_math_may_uflowf
#define __math_divzerof lp_flt_math_divzerof
#define __math_invalidf lp_flt_math_invalidf
#define __math_edomf lp_flt_math_edomf

float lp_sinf (float);
float lp_cosf (float);
float lp_tanf (float);
float lp_asinf (float);
float lp_acosf (float);
float lp_atanf (float);
float lp_expf (float);
float lp_logf (float);
float lp_atan2f (float, float);
float lp_powf (float, float);
float lp_flt_kernel_tanf (float, float, int);

/* glibc build-system macros.  */
#define attribute_hidden
#define hidden_def(x)
#define libm_hidden_proto(x)
#define strong_alias(a, b)
#define versioned_symbol(lib, a, b, v)
#define libm_alias_float(a, b)
#define libm_alias_float_other(a, b)
#define libm_alias_finite(a, b)
#undef __glibc_likely
#undef __glibc_unlikely
#define __glibc_likely(c) (c)
#define __glibc_unlikely(c) (c)
#define NOINLINE __attribute__ ((noinline))
/* float argument only (powf).  */
#define issignaling(x) issignalingf_inline (x)
#define __set_errno(e) (errno = (e))
#define HIGH_ORDER_BIT_IS_SET_FOR_SNAN 0

/* -fno-builtin turns these into libm calls; use the (correctly rounded,
   exact) builtins instead.  */
#undef sqrtf
#undef fabsf
#define sqrtf(x) __builtin_sqrtf (x)
#define fabsf(x) __builtin_fabsf (x)

/* Multiply-add.  glibc's x86-64 ifunc picks builds made with -mfma -mavx2
   for sinf/cosf/expf/logf/powf, where GCC contracts a*b+c into one fused
   operation.  Those sites are written as LP_FMA (a, b, c); a TU that
   reproduces the FMA variant defines LP_FLT_FMA_VARIANT before including
   this header.  Everything is built with -ffp-contract=off.  */
#ifdef LP_FLT_FMA_VARIANT
# define LP_FMA(a, b, c) __builtin_fma ((a), (b), (c))
#else
# define LP_FMA(a, b, c) ((a) * (b) + (c))
#endif

/* Barriers: plain volatile code, no asm.  On x86-64 (SSE, FLT_EVAL_METHOD 0)
   math_narrow_eval is the identity.  */
static inline float lp_flt_opt_barrier_f (float x) { volatile float v = x; return v; }
static inline double lp_flt_opt_barrier_d (double x) { volatile double v = x; return v; }
static inline void lp_flt_force_eval_f (float x) { volatile float v = x; (void) v; }
static inline void lp_flt_force_eval_d (double x) { volatile double v = x; (void) v; }
#define math_opt_barrier(x) \
  _Generic ((x), float: lp_flt_opt_barrier_f, default: lp_flt_opt_barrier_d) (x)
#define math_force_eval(x) \
  _Generic ((x), float: lp_flt_force_eval_f, default: lp_flt_force_eval_d) (x)
#define math_narrow_eval(x) (x)
/* Only raises the underflow exception in glibc; result unaffected.  */
#define math_check_force_underflow(x) \
  do { float lp_t_ = (x); if (__builtin_fabsf (lp_t_) < FLT_MIN) math_force_eval (lp_t_ * lp_t_); } while (0)

/* NaN results are computed explicitly, as glibc 2.39 on x86-64 (SSE) produces
   them, instead of relying on the hardware: x86 generates the default NaN
   0xffc00000 (aarch64: 0x7fc00000), and for a binary op with two NaN operands
   SSE returns the first operand quieted, while compilers may commute a+b.  */
static inline float lp_flt_quiet (float x)
{ union { float f; uint32_t i; } u = { x }; u.i |= 0x00400000; return u.f; }
static inline float lp_flt_x86_default_nan (void)
{ union { uint32_t i; float f; } u = { 0xffc00000 }; return u.f; }
/* Result of a + b (or a - b) on SSE when at least one operand is NaN.  */
static inline float lp_flt_nan2 (float a, float b)
{ return lp_flt_quiet (isnan (a) ? a : b); }

/* math_private.h word access.  */
typedef union { float value; uint32_t word; } lp_flt_ieee_float_shape_type;
#define GET_FLOAT_WORD(i, d) \
  do { lp_flt_ieee_float_shape_type gf_u; gf_u.value = (d); (i) = gf_u.word; } while (0)
#define SET_FLOAT_WORD(d, i) \
  do { lp_flt_ieee_float_shape_type sf_u; sf_u.word = (i); (d) = sf_u.value; } while (0)

#endif
