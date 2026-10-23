/* Double-precision log(x) function.
   Copyright (C) 2018-2024 Free Software Foundation, Inc.
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

#define T lp_explog_log_data.tab
#define T2 lp_explog_log_data.tab2
#define B lp_explog_log_data.poly1
#define A lp_explog_log_data.poly
#define Ln2hi lp_explog_log_data.ln2hi
#define Ln2lo lp_explog_log_data.ln2lo
#define N (1 << LOG_TABLE_BITS)
#define OFF 0x3fe6000000000000

/* Top 16 bits of a double.  */
static inline uint32_t
top16 (double x)
{
  return asuint64 (x) >> 48;
}


double
lp_log (double x)
{
  /* double_t for better performance on targets with FLT_EVAL_METHOD==2.  */
  double_t w, z, r, r2, r3, y, invc, logc, kd, hi, lo;
  uint64_t ix, iz, tmp;
  uint32_t top;
  int k, i;

  ix = asuint64 (x);
  top = top16 (x);

#define LO asuint64 (1.0 - 0x1p-4)
#define HI asuint64 (1.0 + 0x1.09p-4)
  if (__glibc_unlikely (ix - LO < HI - LO))
    {
      /* Handle close to 1.0 inputs separately.  */
      /* Fix sign of zero with downward rounding when x==1.  */
      if (WANT_ROUNDING && __glibc_unlikely (ix == asuint64 (1.0)))
	return 0;
      r = x - 1.0;
      r2 = r * r;
      r3 = r * r2;
      /* y = r3 * p; the multiplication is fused into "y += lo" below.  */
      double_t p = LP_FMA (LP_FMA (LP_FMA (B[10], r3, LP_FMA (B[9], r2, LP_FMA (B[8], r, B[7]))),
				   r3, LP_FMA (B[6], r2, LP_FMA (B[5], r, B[4]))),
			   r3, LP_FMA (B[3], r2, LP_FMA (B[2], r, B[1])));
      /* Worst-case error is around 0.507 ULP.  */
      /* w = r * 0x1p27; rhi = r + w - w, contracted by GCC as below.  */
      double_t rhi = LP_FMA (-r, 0x1p27, LP_FMA (r, 0x1p27, r));
      double_t rlo = r - rhi;
      w = rhi * rhi; /* times B[0] == -0.5, fused below.  */
      hi = LP_FMA (w, B[0], r);
      lo = LP_FMA (w, B[0], r - hi);
      lo = LP_FMA (B[0] * rlo, rhi + r, lo);
      y = LP_FMA (p, r3, lo);
      y += hi;
      return y;
    }
  if (__glibc_unlikely (top - 0x0010 >= 0x7ff0 - 0x0010))
    {
      /* x < 0x1p-1022 or inf or nan.  */
      if (ix * 2 == 0)
	return __math_divzero (1);
      if (ix == asuint64 (INFINITY)) /* log(inf) == inf.  */
	return x;
      if ((top & 0x8000) || (top & 0x7ff0) == 0x7ff0)
	return __math_invalid (x);
      /* x is subnormal, normalize it.  */
      ix = asuint64 (x * 0x1p52);
      ix -= 52ULL << 52;
    }

  /* x = 2^k z; where z is in range [OFF,2*OFF) and exact.
     The range is split into N subintervals.
     The ith subinterval contains z and c is near its center.  */
  tmp = ix - OFF;
  i = (tmp >> (52 - LOG_TABLE_BITS)) % N;
  k = (int64_t) tmp >> 52; /* arithmetic shift */
  iz = ix - (tmp & 0xfffULL << 52);
  invc = T[i].invc;
  logc = T[i].logc;
  z = asdouble (iz);

  /* log(x) = log1p(z/c-1) + log(c) + k*Ln2.  */
  /* r ~= z/c - 1, |r| < 1/(2*N).  */
#if 1 /* __FP_FAST_FMA: glibc *_fma variant */
  /* rounding error: 0x1p-55/N.  */
  r = __builtin_fma (z, invc, -1.0);
#else
  /* rounding error: 0x1p-55/N + 0x1p-66.  */
  r = (z - T2[i].chi - T2[i].clo) * invc;
#endif
  kd = (double_t) k;

  /* hi + lo = r + log(c) + k*Ln2.  */
  w = LP_FMA (Ln2hi, kd, logc);
  hi = w + r;
  lo = LP_FMA (Ln2lo, kd, w - hi + r);

  /* log(x) = lo + (log1p(r) - r) + hi.  */
  r2 = r * r; /* rounding error: 0x1p-54/N^2.  */
  /* Worst case error if |y| > 0x1p-4: 0.519 ULP (0.520 ULP without fma).
     0.5 + 2.06/N + abs-poly-error*2^56 ULP (+ 0.001 ULP without fma).  */
  y = LP_FMA (r * r2, LP_FMA (LP_FMA (A[4], r, A[3]), r2, LP_FMA (A[2], r, A[1])),
	     LP_FMA (A[0], r2, lo))
      + hi;
  return y;
}
