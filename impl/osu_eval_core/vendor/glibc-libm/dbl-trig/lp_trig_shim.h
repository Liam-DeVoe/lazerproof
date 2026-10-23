/* lazerproof shim replacing glibc-internal headers (math_private.h, fenv_private.h,
   math-underflow.h, libm-alias-double.h, mydefs.h, include/endian.h) for the vendored
   glibc 2.39 sysdeps/ieee754/dbl-64 sin/cos/tan.
   Dropped glibc behaviour (result-neutral): SET_RESTORE_ROUND_53BIT (we assume the caller
   runs in round-to-nearest, as Rust always does), errno setting, forced underflow flags. */
#ifndef LP_TRIG_SHIM_H
#define LP_TRIG_SHIM_H
#include <math.h>

typedef int int4;
typedef union { int4 i[2]; double x; double d; } mynumber;

#if defined (__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
# define BIG_ENDI 1
# define HIGH_HALF 0
# define LOW_HALF 1
#else
# define LITTLE_ENDI 1
# define HIGH_HALF 1
# define LOW_HALF 0
#endif

/* -fno-builtin is in the fixed flags: use the builtins explicitly so these stay inline. */
/* glibc builds s_sin.c/s_tan.c for x86-64 multiarch with -mfma -mavx2 and GCC's default
   -ffp-contract=fast.  Every multiply-add GCC 13 contracts there (from
   -fdump-tree-widening_mul) is written out as LP_FMA, and the code is built with
   -ffp-contract=off so no other contraction happens. */
#define LP_FMA(a, b, c) __builtin_fma ((a), (b), (c))

#undef fabs
#undef copysign
#define fabs(x) __builtin_fabs (x)
#define copysign(x, y) __builtin_copysign ((x), (y))

int lp_trig_branred (double x, double *a, double *aa);
union lp_trig_sincostab_u { int4 i[880]; double x[440]; };
extern const union lp_trig_sincostab_u lp_trig_sincostab;

double lp_sin (double x);
double lp_cos (double x);
double lp_tan (double x);
#endif
