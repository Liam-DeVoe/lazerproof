/* Smoke test: lp_* (vendored) vs the system glibc libm.so.6 (dlsym), bitwise.
   usage: smoke [N per function, default 1e7] [seed]
   build: cc -O2 -ffp-contract=off -I.. smoke.c ../<sources> -ldl -lm  */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

double lp_exp (double);
double lp_log (double);
double lp_log10 (double);
double lp_pow (double, double);
double lp_cbrt (double);
double lp_fmod (double, double);

static uint64_t s0 = 0x9E3779B97F4A7C15ULL;
static uint64_t
rnd (void)
{
  uint64_t z = (s0 += 0x9E3779B97F4A7C15ULL);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}
static double
asd (uint64_t i)
{
  double d;
  memcpy (&d, &i, 8);
  return d;
}
static uint64_t
asu (double d)
{
  uint64_t i;
  memcpy (&i, &d, 8);
  return i;
}
static double
unif (double a, double b)
{
  return a + (b - a) * ((rnd () >> 11) * 0x1p-53);
}
/* log-uniform positive magnitude over all binades */
static double
anypos (void)
{
  return asd (rnd () & 0x7fefffffffffffffULL);
}

static const double specials[] = {
  0.0, -0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, -3.0, 10.0, 0.1, 100.0, 1e22, 1e23,
  __builtin_inf (), -__builtin_inf (), __builtin_nan (""), -__builtin_nan (""),
  __builtin_nan ("1"), -__builtin_nan ("2"), __builtin_nans ("3"), -__builtin_nans ("4"),
  0x1p-1074, -0x1p-1074, 0x1p-1022, -0x1p-1022, 0x1.fffffffffffffp1023, -0x1.fffffffffffffp1023,
  0x1p-54, 0x1p-55, 709.782712893384, 709.7827128933841, -745.1332191019411, -745.1332191019412,
  -708.3964185322641, 1024.0, -1075.0, 0x1p63, -0x1p63, 0x1p-65, 0x1.0000000000001p0, 0x1.fffffffffffffp-1,
  0.9375, 1.0644531250000002, 0.5, 1.5, 1e-300, 1e300, -1e-300, 4.5, -4.5, 1e10, 2.5, -2.5, 7.0, 0.3333333333333333
};
#define NSPEC (sizeof specials / sizeof specials[0])

static long mism, nanmism;
static int printed;
static void
check1 (const char *name, double x, double y, double got, double want)
{
  if (asu (got) != asu (want))
    {
      int bothnan = got != got && want != want;
      if (bothnan)
	nanmism++;
      else
	mism++;
      if (printed++ < 8)
	printf ("  MISMATCH %s(%a, %a): lp=%a sys=%a%s\n", name, x, y, got, want,
		bothnan ? " (NaN payload/sign)" : "");
    }
}

typedef double (*f1) (double);
typedef double (*f2) (double, double);

int
main (int argc, char **argv)
{
  long n = argc > 1 ? atol (argv[1]) : 10000000;
  if (argc > 2)
    s0 = strtoull (argv[2], 0, 0);
  void *h = dlopen ("libm.so.6", RTLD_NOW);
  if (!h)
    {
      printf ("dlopen failed\n");
      return 2;
    }
  struct { const char *name; f1 lp; } one[] = {
    {"exp", lp_exp}, {"log", lp_log}, {"log10", lp_log10}, {"cbrt", lp_cbrt}};
  struct { const char *name; f2 lp; } two[] = {{"pow", lp_pow}, {"fmod", lp_fmod}};
  long total = 0;
  for (int k = 0; k < 4; k++)
    {
      f1 sys = (f1) dlsym (h, one[k].name), lp = one[k].lp;
      mism = nanmism = printed = 0;
      for (unsigned i = 0; i < NSPEC; i++)
	check1 (one[k].name, specials[i], 0, lp (specials[i]), sys (specials[i]));
      for (long i = 0; i < n; i++)
	{
	  double x;
	  switch (i & 3)
	    {
	    case 0: x = asd (rnd ()); break;
	    case 1:
	      if (k == 0) x = unif (-750, 710);
	      else if (k == 3) x = unif (-1e6, 1e6);
	      else x = unif (0.0, 4.0);
	      break;
	    case 2:
	      if (k == 0) x = unif (-40, 40);
	      else if (k == 3) x = anypos () * ((rnd () & 1) ? 1 : -1);
	      else x = unif (0.9, 1.1);
	      break;
	    default:
	      if (k == 0) x = unif (-1, 1) * asd ((uint64_t) (0x3c9 + rnd () % 0x41) << 52);
	      else x = anypos ();
	      break;
	    }
	  check1 (one[k].name, x, 0, lp (x), sys (x));
	}
      printf ("%-6s n=%ld mismatches=%ld nan-only=%ld\n", one[k].name, n + (long) NSPEC, mism, nanmism);
      total += mism + nanmism;
    }
  for (int k = 0; k < 2; k++)
    {
      f2 sys = (f2) dlsym (h, two[k].name), lp = two[k].lp;
      mism = nanmism = printed = 0;
      for (unsigned i = 0; i < NSPEC; i++)
	for (unsigned j = 0; j < NSPEC; j++)
	  check1 (two[k].name, specials[i], specials[j], lp (specials[i], specials[j]),
		  sys (specials[i], specials[j]));
      for (long i = 0; i < n; i++)
	{
	  double x, y;
	  switch (i % 6)
	    {
	    case 0: x = asd (rnd ()); y = asd (rnd ()); break;
	    case 1: x = unif (0, 10); y = unif (-50, 50); break;
	    case 2: /* integer / half-integer exponents, any sign base */
	      x = unif (-20, 20); y = (double) ((int64_t) (rnd () % 401) - 200) * ((rnd () & 1) ? 1 : 0.5); break;
	    case 3: x = anypos () * ((rnd () & 1) ? 1 : -1); y = (double) ((int64_t) (rnd () % 64) - 32); break;
	    case 4: x = unif (0.5, 2); y = unif (-2000, 2000); break;
	    default: x = anypos (); y = unif (-1, 1) * asd ((uint64_t) (0x3c0 + rnd () % 0x80) << 52); break;
	    }
	  if (k == 1 && (i % 6) == 4) { x = anypos (); y = anypos (); }
	  if (k == 1 && (i % 6) == 5) { x = unif (-1e6, 1e6); y = unif (-10, 10); }
	  check1 (two[k].name, x, y, lp (x, y), sys (x, y));
	}
      printf ("%-6s n=%ld mismatches=%ld nan-only=%ld\n", two[k].name, n + (long) (NSPEC * NSPEC), mism, nanmism);
      total += mism + nanmism;
    }
  printf ("TOTAL mismatches %ld\n", total);
  return total != 0;
}
