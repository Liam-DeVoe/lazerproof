/* lazerproof shim replacing the glibc-internal headers used by
   sysdeps/ieee754/dbl-64/{e_asin.c,s_atan.c,e_atan2.c} (glibc 2.39).
   Target: bit-identical to the x86-64 *_fma ifunc variants
   (__ieee754_asin_fma, __ieee754_acos_fma, __atan_fma, __ieee754_atan2_fma),
   which glibc builds with -mfma -mavx2 (GCC, -ffp-contract=fast).
   Every multiply-add GCC contracts there is written as an explicit
   __builtin_fma in these sources, so they must be compiled with
   -ffp-contract=off.  Assumes round-to-nearest (glibc's SET_RESTORE_ROUND
   only matters under a non-default rounding mode) and ignores FP exception
   flags (math_check_force_underflow / math_force_eval only raise flags).
   Public symbols follow libm.so.6: asin/acos are glibc's math/w_asin_compat.c and
   w_acos_compat.c wrappers (|x| > 1 returns +NaN via __kernel_standard,
   _LIB_VERSION == _POSIX_); atan2's wrapper (w_atan2_compat.c) only sets errno, so
   lp_atan2 is __ieee754_atan2 itself; atan has no wrapper.  */
#ifndef LP_INVTRIG_SHIM_H
#define LP_INVTRIG_SHIM_H

#include <float.h>

/* x86-64 and aarch64 are both little-endian (glibc include/endian.h).  */
#define LITTLE_ENDI 1
#define HIGH_HALF 1
#define LOW_HALF 0

#define fabs(x) __builtin_fabs (x)
#define copysign(x, y) __builtin_copysign (x, y)

#define SET_RESTORE_ROUND(m) do { } while (0)
#define math_check_force_underflow(x) do { } while (0)
#define math_check_force_underflow_nonneg(x) do { } while (0)
#define math_force_eval(x) do { volatile double lp_invtrig_fe_ = (x); (void) lp_invtrig_fe_; } while (0)

#define SECTION

/* Exported names.  */
#define __ieee754_asin lp_invtrig_ieee754_asin	/* lp_asin: wrapper in e_asin.c */
#define __ieee754_acos lp_invtrig_ieee754_acos	/* lp_acos: wrapper in e_asin.c */
#define __atan lp_atan
#define __ieee754_atan2 lp_atan2

double lp_invtrig_ieee754_asin (double);
double lp_invtrig_ieee754_acos (double);
double lp_asin (double);
double lp_acos (double);
double lp_atan (double);
double lp_atan2 (double, double);

#endif
