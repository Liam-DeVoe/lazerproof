/* Minimal standalone shim replacing glibc's math_config.h / math_private.h /
   math-barriers.h for the vendored glibc 2.39 dbl-64 exp/log/log10/pow/cbrt/fmod.
   Derived from glibc 2.39 sysdeps/ieee754/dbl-64/math_config.h (LGPL-2.1+).

   Differences from glibc (value-preserving; only errno / FP-exception side
   effects are dropped):
   - errno is never set (WANT_ERRNO's only effect is errno).
   - math_opt_barrier / math_force_eval use volatile instead of inline asm.
   - math_narrow_eval is the identity (FLT_EVAL_METHOD == 0 on x86-64 SSE2
     and aarch64).
   - TOINT_INTRINSICS is 0 (as in glibc for x86-64).
   - The FMA (__FP_FAST_FMA) paths of e_log.c / e_pow.c are always taken and
     every contraction GCC performs in the glibc *_fma ifunc variants
     (-mfma -mavx2, -ffp-contract=fast) is written as an explicit
     __builtin_fma, so the sources must be compiled with -ffp-contract=off.  */

#ifndef LP_EXPLOG_H
#define LP_EXPLOG_H

#include <stdint.h>

#define WANT_ROUNDING 1
#define TOINT_INTRINSICS 0
#define WANT_ERRNO 1 /* selects the same branches as glibc; errno itself is never set */
#define INFINITY __builtin_inf ()

#define __glibc_unlikely(c) __builtin_expect ((c), 0)
#define __glibc_likely(c) __builtin_expect ((c), 1)

typedef double double_t_lp;
#define double_t double_t_lp

/* Explicit fused multiply-add.  */
#define LP_FMA(a, b, c) __builtin_fma ((a), (b), (c))

static inline double
math_opt_barrier (double x)
{
  volatile double v = x;
  return v;
}

static inline void
math_force_eval (double x)
{
  volatile double v = x;
  (void) v;
}

#define math_narrow_eval(x) (x)

static inline int
clz_uint64 (uint64_t x)
{
  return __builtin_clzll (x);
}

static inline int
ctz_uint64 (uint64_t x)
{
  return __builtin_ctzll (x);
}

static inline uint64_t
asuint64 (double f)
{
  union
  {
    double f;
    uint64_t i;
  } u = {f};
  return u.i;
}

static inline double
asdouble (uint64_t i)
{
  union
  {
    uint64_t i;
    double f;
  } u = {i};
  return u.f;
}

static inline double
lp_fabs (double x)
{
  return asdouble (asuint64 (x) & 0x7fffffffffffffffULL);
}

static inline int
lp_isnan (double x)
{
  return (asuint64 (x) & 0x7fffffffffffffffULL) > 0x7ff0000000000000ULL;
}

/* x86-64 / aarch64: HIGH_ORDER_BIT_IS_SET_FOR_SNAN == 0.  */
static inline int
issignaling_inline (double x)
{
  uint64_t ix = asuint64 (x);
  return 2 * (ix ^ 0x0008000000000000) > 2 * 0x7ff8000000000000ULL;
}

#define BIT_WIDTH       64
#define MANTISSA_WIDTH  52
#define EXPONENT_WIDTH  11
#define MANTISSA_MASK   UINT64_C(0x000fffffffffffff)
#define EXPONENT_MASK   UINT64_C(0x7ff0000000000000)
#define EXP_MANT_MASK   UINT64_C(0x7fffffffffffffff)
#define QUIET_NAN_MASK  UINT64_C(0x0008000000000000)
#define SIGN_MASK	UINT64_C(0x8000000000000000)

static inline uint64_t
get_mantissa (uint64_t x)
{
  return x & MANTISSA_MASK;
}

static inline double
make_double (uint64_t x, int64_t ep, uint64_t s)
{
  int lz = clz_uint64 (x) - EXPONENT_WIDTH;
  x <<= lz;
  ep -= lz;

  if (__glibc_unlikely (ep < 0 || x == 0))
    {
      x >>= -ep;
      ep = 0;
    }

  return asdouble (s + x + (ep << MANTISSA_WIDTH));
}

/* Error handling (glibc math_err.c without errno).  */
static inline double
lp_explog_xflow (uint32_t sign, double y)
{
  y = math_opt_barrier (sign ? -y : y) * y;
  return y;
}

static inline double
__math_uflow (uint32_t sign)
{
  return lp_explog_xflow (sign, 0x1p-767);
}

static inline double
__math_oflow (uint32_t sign)
{
  return lp_explog_xflow (sign, 0x1p769);
}

static inline double
__math_divzero (uint32_t sign)
{
  double y = math_opt_barrier (sign ? -1.0 : 1.0) / 0.0;
  return y;
}

/* x86-64 SSE NaN rules, made explicit so that neither the compiler's operand
   order nor the target (aarch64 gives signaling NaNs precedence and its
   default NaN is positive) can change the result bits:
   - an invalid operation without NaN operands returns the default NaN
     0xfff8000000000000 (negative quiet NaN);
   - a binary operation with NaN operand(s) returns the first NaN operand,
     quieted (SNaN or QNaN alike).  */
#define LP_X86_DEFAULT_NAN asdouble (0xfff8000000000000ULL)

static inline double
lp_quiet (double x)
{
  return asdouble (asuint64 (x) | 0x0008000000000000ULL);
}

/* Value of x OP y on x86-64 SSE when x or y is a NaN (any arithmetic OP).  */
static inline double
lp_nan2 (double x, double y)
{
  return lp_isnan (x) ? lp_quiet (x) : lp_quiet (y);
}

/* glibc: (x - x) / (x - x).  */
static inline double
__math_invalid (double x)
{
  return lp_isnan (x) ? lp_quiet (x) : LP_X86_DEFAULT_NAN;
}

static inline double
__math_edom (double y)
{
  return y;
}

#define check_oflow(x) (x)
#define check_uflow(x) (x)

#define EXP_TABLE_BITS 7
#define EXP_POLY_ORDER 5
#define EXP2_POLY_ORDER 5
extern const struct exp_data
{
  double invln2N;
  double shift;
  double negln2hiN;
  double negln2loN;
  double poly[4]; /* Last four coefficients.  */
  double exp2_shift;
  double exp2_poly[EXP2_POLY_ORDER];
  double invlog10_2N;
  double neglog10_2hiN;
  double neglog10_2loN;
  double exp10_poly[5];
  uint64_t tab[2*(1 << EXP_TABLE_BITS)];
} lp_explog_exp_data;

#define LOG_TABLE_BITS 7
#define LOG_POLY_ORDER 6
#define LOG_POLY1_ORDER 12
extern const struct log_data
{
  double ln2hi;
  double ln2lo;
  double poly[LOG_POLY_ORDER - 1]; /* First coefficient is 1.  */
  double poly1[LOG_POLY1_ORDER - 1];
  struct {double invc, logc;} tab[1 << LOG_TABLE_BITS];
  /* tab2 omitted: only used without FMA.  */
} lp_explog_log_data;

#define POW_LOG_TABLE_BITS 7
#define POW_LOG_POLY_ORDER 8
extern const struct pow_log_data
{
  double ln2hi;
  double ln2lo;
  double poly[POW_LOG_POLY_ORDER - 1]; /* First coefficient is 1.  */
  struct {double invc, pad, logc, logctail;} tab[1 << POW_LOG_TABLE_BITS];
} lp_explog_pow_log_data;

/* Exports.  */
double lp_exp (double);
double lp_log (double);
double lp_log10 (double);
double lp_pow (double, double);
double lp_cbrt (double);
double lp_fmod (double, double);

#endif
