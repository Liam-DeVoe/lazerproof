/*
 * IBM Accurate Mathematical Library
 * written by International Business Machines Corp.
 * Copyright (C) 2001-2024 Free Software Foundation, Inc.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; if not, see <https://www.gnu.org/licenses/>.
 */
/*********************************************************************/
/*  MODULE_NAME: utan.c                                              */
/*                                                                   */
/*  FUNCTIONS: utan                                                  */
/*                                                                   */
/*  FILES NEEDED:dla.h endian.h mydefs.h utan.h                      */
/*               branred.c                                           */
/*               utan.tbl                                            */
/*                                                                   */
/*********************************************************************/

#include "lp_trig_shim.h"
#include "dla.h"

#ifndef SECTION
# define SECTION
#endif

/* tan with max ULP of ~0.619 based on random sampling.  */
double
SECTION
lp_tan (double x)
{
#include "utan.h"
#include "utan.tbl"

  int ux, i, n;
  double a, da, a2, b, db, c, dc, fi, gi, pz,
	 s, sy, t, t1, t2, t3, t4, w, x2, xn, y, ya,
         yya, z0, z, z2;
  mynumber num, v;

  double retval;



  /* x=+-INF, x=NaN */
  num.d = x;
  ux = num.i[HIGH_HALF];
  if ((ux & 0x7ff00000) == 0x7ff00000)
    {
      retval = x - x;
      goto ret;
    }

  w = (x < 0.0) ? -x : x;

  /* (I) The case abs(x) <= 1.259e-8 */
  if (w <= g1.d)
    {
      retval = x;
      goto ret;
    }

  /* (II) The case 1.259e-8 < abs(x) <= 0.0608 */
  if (w <= g2.d)
    {
      x2 = x * x;

      t2 = LP_FMA (x2, d11.d, d9.d);
      t2 = LP_FMA (x2, t2, d7.d);
      t2 = LP_FMA (x2, t2, d5.d);
      t2 = LP_FMA (x2, t2, d3.d);

      y = LP_FMA (x * x2, t2, x);
      retval = y;
      /* Max ULP is 0.504.  */
      goto ret;
    }

  /* (III) The case 0.0608 < abs(x) <= 0.787 */
  if (w <= g3.d)
    {
      i = ((int) LP_FMA (w, 256, mfftnhf.d));
      z = w - xfg[i][0].d;
      z2 = z * z;
      s = (x < 0.0) ? -1 : 1;
      pz = LP_FMA (z * z2, LP_FMA (z2, e1.d, e0.d), z);
      fi = xfg[i][1].d;
      gi = xfg[i][2].d;
      t2 = pz * (gi + fi) / (gi - pz);
      y = fi + t2;
      retval = (s * y);
      /* Max ULP is 0.60.  */
      goto ret;
    }

  /* (---) The case 0.787 < abs(x) <= 25 */
  if (w <= g4.d)
    {
      /* Range reduction by algorithm i */
      t = LP_FMA (x, hpinv.d, toint.d);
      xn = t - toint.d;
      v.d = t;
      t1 = LP_FMA (-xn, mp2.d, LP_FMA (-xn, mp1.d, x));
      n = v.i[LOW_HALF] & 0x00000001;
      a = LP_FMA (-xn, mp3.d, t1);
      da = LP_FMA (-xn, mp3.d, t1 - a);
      if (a < 0.0)
	{
	  ya = -a;
	  yya = -da;
	  sy = -1;
	}
      else
	{
	  ya = a;
	  yya = da;
	  sy = 1;
	}

      /* (VI) The case 0.787 < abs(x) <= 25,    0 < abs(y) <= 0.0608 */
      if (ya <= gy2.d)
	{
	  a2 = a * a;
	  t2 = LP_FMA (a2, d11.d, d9.d);
	  t2 = LP_FMA (a2, t2, d7.d);
	  t2 = LP_FMA (a2, t2, d5.d);
	  t2 = LP_FMA (a2, t2, d3.d);
	  t2 = LP_FMA (a * a2, t2, da);

	  if (n)
	    {
	      /* -cot */
	      EADD (a, t2, b, db);
	      DIV2 (1.0, 0.0, b, db, c, dc, t1, t2, t3, t4);
	      y = c + dc;
	      retval = (-y);
	      /* Max ULP is 0.506.  */
	      goto ret;
	    }
	  else
	    {
	      /* tan */
	      y = a + t2;
	      retval = y;
	      /* Max ULP is 0.506.  */
	      goto ret;
	    }
	}

      /* (VII) The case 0.787 < abs(x) <= 25,    0.0608 < abs(y) <= 0.787 */

      i = ((int) LP_FMA (ya, 256, mfftnhf.d));
      z = (z0 = (ya - xfg[i][0].d)) + yya;
      z2 = z * z;
      pz = LP_FMA (z * z2, LP_FMA (z2, e1.d, e0.d), z);
      fi = xfg[i][1].d;
      gi = xfg[i][2].d;

      if (n)
	{
	  /* -cot */
	  t2 = pz * (fi + gi) / (fi + pz);
	  y = gi - t2;
	  retval = (-sy * y);
	  /* Max ULP is 0.62.  */
	  goto ret;
	}
      else
	{
	  /* tan */
	  t2 = pz * (gi + fi) / (gi - pz);
	  y = fi + t2;
	  retval = (sy * y);
	  /* Max ULP is 0.62.  */
	  goto ret;
	}
    }

  /* (---) The case 25 < abs(x) <= 1e8 */
  if (w <= g5.d)
    {
      /* Range reduction by algorithm ii */
      t = LP_FMA (x, hpinv.d, toint.d);
      xn = t - toint.d;
      v.d = t;
      t1 = LP_FMA (-xn, mp2.d, LP_FMA (-xn, mp1.d, x));
      n = v.i[LOW_HALF] & 0x00000001;
      t = LP_FMA (-xn, pp3.d, t1);
      da = LP_FMA (-xn, pp3.d, t1 - t);
      a = LP_FMA (-xn, pp4.d, t);
      da = LP_FMA (-xn, pp4.d, t - a) + da;
      EADD (a, da, t1, t2);
      a = t1;
      da = t2;
      if (a < 0.0)
	{
	  ya = -a;
	  yya = -da;
	  sy = -1;
	}
      else
	{
	  ya = a;
	  yya = da;
	  sy = 1;
	}

      /* (VIII) The case 25 < abs(x) <= 1e8,    0 < abs(y) <= 0.0608 */
      if (ya <= gy2.d)
	{
	  a2 = a * a;
	  t2 = LP_FMA (a2, d11.d, d9.d);
	  t2 = LP_FMA (a2, t2, d7.d);
	  t2 = LP_FMA (a2, t2, d5.d);
	  t2 = LP_FMA (a2, t2, d3.d);
	  t2 = LP_FMA (a * a2, t2, da);

	  if (n)
	    {
	      /* -cot */
	      EADD (a, t2, b, db);
	      DIV2 (1.0, 0.0, b, db, c, dc, t1, t2, t3, t4);
	      y = c + dc;
	      retval = (-y);
	      /* Max ULP is 0.506.  */
	      goto ret;
	    }
	  else
	    {
	      /* tan */
	      y = a + t2;
	      retval = y;
	      /* Max ULP is 0.506.  */
	      goto ret;
	    }
	}

      /* (IX) The case 25 < abs(x) <= 1e8,    0.0608 < abs(y) <= 0.787 */
      i = ((int) LP_FMA (ya, 256, mfftnhf.d));
      z = (z0 = (ya - xfg[i][0].d)) + yya;
      z2 = z * z;
      pz = LP_FMA (z * z2, LP_FMA (z2, e1.d, e0.d), z);
      fi = xfg[i][1].d;
      gi = xfg[i][2].d;

      if (n)
	{
	  /* -cot */
	  t2 = pz * (fi + gi) / (fi + pz);
	  y = gi - t2;
	  retval = (-sy * y);
	  /* Max ULP is 0.62.  */
	  goto ret;
	}
      else
	{
	  /* tan */
	  t2 = pz * (gi + fi) / (gi - pz);
	  y = fi + t2;
	  retval = (sy * y);
	  /* Max ULP is 0.62.  */
	  goto ret;
	}
    }

  /* (---) The case 1e8 < abs(x) < 2**1024 */
  /* Range reduction by algorithm iii */
  n = (lp_trig_branred (x, &a, &da)) & 0x00000001;
  EADD (a, da, t1, t2);
  a = t1;
  da = t2;
  if (a < 0.0)
    {
      ya = -a;
      yya = -da;
      sy = -1;
    }
  else
    {
      ya = a;
      yya = da;
      sy = 1;
    }

  /* (X) The case 1e8 < abs(x) < 2**1024,    0 < abs(y) <= 0.0608 */
  if (ya <= gy2.d)
    {
      a2 = a * a;
      t2 = LP_FMA (a2, d11.d, d9.d);
      t2 = LP_FMA (a2, t2, d7.d);
      t2 = LP_FMA (a2, t2, d5.d);
      t2 = LP_FMA (a2, t2, d3.d);
      t2 = LP_FMA (a * a2, t2, da);
      if (n)
	{
	  /* -cot */
	  EADD (a, t2, b, db);
	  DIV2 (1.0, 0.0, b, db, c, dc, t1, t2, t3, t4);
	  y = c + dc;
	  retval = (-y);
	  /* Max ULP is 0.506.  */
	  goto ret;
	}
      else
	{
	  /* tan */
	  y = a + t2;
	  retval = y;
	  /* Max ULP is 0.507.  */
	  goto ret;
	}
    }

  /* (XI) The case 1e8 < abs(x) < 2**1024,    0.0608 < abs(y) <= 0.787 */
  i = ((int) LP_FMA (ya, 256, mfftnhf.d));
  z = (z0 = (ya - xfg[i][0].d)) + yya;
  z2 = z * z;
  pz = LP_FMA (z * z2, LP_FMA (z2, e1.d, e0.d), z);
  fi = xfg[i][1].d;
  gi = xfg[i][2].d;

  if (n)
    {
      /* -cot */
      t2 = pz * (fi + gi) / (fi + pz);
      y = gi - t2;
      retval = (-sy * y);
      /* Max ULP is 0.62.  */
      goto ret;
    }
  else
    {
      /* tan */
      t2 = pz * (gi + fi) / (gi - pz);
      y = fi + t2;
      retval = (sy * y);
      /* Max ULP is 0.62.  */
      goto ret;
    }

ret:
  return retval;
}

