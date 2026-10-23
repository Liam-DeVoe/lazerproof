/* Compute cubic root of double value.
   Copyright (C) 1997-2024 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

#include "lp_explog.h"

/* glibc 2.39 sysdeps/ieee754/dbl-64/s_frexp.c (__frexp), made static.  */
static double
lp_explog_frexp (double x, int *eptr)
{
  int64_t ix = (int64_t) asuint64 (x);
  int32_t ex = 0x7ff & (ix >> 52);
  int e = 0;

  if (__glibc_likely (ex != 0x7ff && x != 0.0))
    {
      /* Not zero and finite.  */
      e = ex - 1022;
      if (__glibc_unlikely (ex == 0))
	{
	  /* Subnormal.  */
	  x *= 0x1p54;
	  ix = (int64_t) asuint64 (x);
	  ex = 0x7ff & (ix >> 52);
	  e = ex - 1022 - 54;
	}

      ix = (ix & INT64_C (0x800fffffffffffff)) | INT64_C (0x3fe0000000000000);
      x = asdouble ((uint64_t) ix);
    }
  else
    /* Quiet signaling NaNs.  */
    x += x;

  *eptr = e;
  return x;
}

static inline double
lp_explog_copysign (double x, double y)
{
  return asdouble ((asuint64 (x) & 0x7fffffffffffffffULL)
		   | (asuint64 (y) & 0x8000000000000000ULL));
}

/* glibc 2.39 sysdeps/ieee754/dbl-64/s_scalbn.c (__scalbn) wrapped as in
   math/s_ldexp_template.c (__ldexp, errno dropped), made static.  */
static double
lp_explog_ldexp (double x, int n)
{
  static const double two54 = 1.80143985094819840000e+16,
		      twom54 = 5.55111512312578270212e-17,
		      huge = 1.0e+300, tiny = 1.0e-300;
  int64_t ix;
  int64_t k;
  if (!(lp_fabs (x) <= 0x1.fffffffffffffp1023) || x == 0)
    return x + x;
  ix = (int64_t) asuint64 (x);
  k = (ix >> 52) & 0x7ff;
  if (__builtin_expect (k == 0, 0))
    {
      if ((ix & UINT64_C (0xfffffffffffff)) == 0)
	return x;
      x *= two54;
      ix = (int64_t) asuint64 (x);
      k = ((ix >> 52) & 0x7ff) - 54;
    }
  if (__builtin_expect (k == 0x7ff, 0))
    return x + x;
  if (__builtin_expect (n < -50000, 0))
    return tiny * lp_explog_copysign (tiny, x);
  if (__builtin_expect (n > 50000 || k + n > 0x7fe, 0))
    return huge * lp_explog_copysign (huge, x);
  k = k + n;
  if (__builtin_expect (k > 0, 1))
    return asdouble ((uint64_t) ((ix & UINT64_C (0x800fffffffffffff))
				 | (k << 52)));
  if (k <= -54)
    return tiny * lp_explog_copysign (tiny, x);
  k += 54;
  x = asdouble ((uint64_t) ((ix & INT64_C (0x800fffffffffffff)) | (k << 52)));
  return x * twom54;
}


#define CBRT2 1.2599210498948731648		/* 2^(1/3) */
#define SQR_CBRT2 1.5874010519681994748		/* 2^(2/3) */

static const double factor[5] =
{
  1.0 / SQR_CBRT2,
  1.0 / CBRT2,
  1.0,
  CBRT2,
  SQR_CBRT2
};


double
lp_cbrt (double x)
{
  double xm, ym, u, t2;
  int xe;

  /* Reduce X.  XM now is an range 1.0 to 0.5.  */
  xm = lp_explog_frexp (lp_fabs (x), &xe);

  /* If X is not finite or is null return it (with raising exceptions
     if necessary.
     Note: *Our* version of `frexp' sets XE to zero if the argument is
     Inf or NaN.  This is not portable but faster.  */
  if (xe == 0 && (x == 0.0 || !(lp_fabs (x) <= 0x1.fffffffffffffp1023)))
    return x + x;

  u = (0.354895765043919860
       + ((1.50819193781584896
	   + ((-2.11499494167371287
	       + ((2.44693122563534430
		   + ((-1.83469277483613086
		       + (0.784932344976639262 - 0.145263899385486377 * xm)
	                  * xm)
		      * xm))
		  * xm))
	      * xm))
	  * xm));

  t2 = u * u * u;

  ym = u * (t2 + 2.0 * xm) / (2.0 * t2 + xm) * factor[2 + xe % 3];

  return lp_explog_ldexp (x > 0.0 ? ym : -ym, xe / 3);
}
