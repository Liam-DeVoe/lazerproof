/* Smoke test: lp_asin/lp_acos/lp_atan/lp_atan2 vs the host glibc libm.so.6 (dlsym), bitwise.
   usage: smoke [N]   (N random inputs per distribution, default 1e7)
   build: $CC -O2 -std=gnu11 -ffp-contract=off -fno-fast-math -fno-builtin -I.. smoke.c ../e_asin.c ../s_atan.c ../e_atan2.c -ldl -lm  */
#include <dlfcn.h>
#include <float.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

double lp_asin (double);
double lp_acos (double);
double lp_atan (double);
double lp_atan2 (double, double);

typedef double (*f1) (double);
typedef double (*f2) (double, double);

static uint64_t rs = 0x9E3779B97F4A7C15ull;
static uint64_t rnd (void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double bits (uint64_t u) { double d; memcpy (&d, &u, 8); return d; }
static uint64_t ubits (double d) { uint64_t u; memcpy (&u, &d, 8); return u; }
static double unif (double a, double b) { return a + (b - a) * ((rnd () >> 11) * 0x1p-53); }
/* sign * 2^e * m, e uniform in [lo, hi] */
static double logu (int lo, int hi) { int e = lo + (int) (rnd () % (uint64_t) (hi - lo + 1)); double m = 1 + (rnd () >> 12) * 0x1p-52; return ((rnd () & 1) ? -1 : 1) * ldexp (m, e); }

static long total_bad;
static long bad1 (const char *name, const char *dist, f1 lp, f1 ref, double x, long *shown)
{
  double a = lp (x), b = ref (x);
  if (ubits (a) != ubits (b)) { if ((*shown)++ < 5) printf ("  MISMATCH %s(%a) [%s]: lp %a glibc %a\n", name, x, dist, a, b); return 1; }
  return 0;
}
static long bad2 (const char *dist, f2 lp, f2 ref, double y, double x, long *shown)
{
  double a = lp (y, x), b = ref (y, x);
  if (ubits (a) != ubits (b)) { if ((*shown)++ < 5) printf ("  MISMATCH atan2(%a, %a) [%s]: lp %a glibc %a\n", y, x, dist, a, b); return 1; }
  return 0;
}

static const double specials[] = { 0.0, -0.0, INFINITY, -INFINITY, NAN, -NAN, 1.0, -1.0, 0.5, -0.5, 0.125, -0.125,
  0.75, 0.921875, 0.953125, 0.96875, 0.984375, 0x1p-26, 0x1p-27, 0x1.fffffffffffffp-1, -0x1.fffffffffffffp-1,
  0x1.0000000000001p0, 2.0, 16.0, -16.0, 0x1p-3, 0x1p-4, 1.0 / 16, 0x1.3d9d4d6b4a8b6p-3, 0x1.ap52, 5.805361265115136e+15,
  0x1p-1022, 0x0.0000000000001p-1022, -0x0.0000000000001p-1022, 0x1.fffffffffffffp1023, -0x1.fffffffffffffp1023,
  0x1p-500, 0x1p500, 0x1p-560, 0x1p560, 0x1p-1000, 0x1p1000, 3.141592653589793, 1e-17, 2.7755575615628914e-17 };
#define NS (sizeof specials / sizeof specials[0])

int main (int argc, char **argv)
{
  long n = argc > 1 ? atol (argv[1]) : 10000000;
  void *h = dlopen ("libm.so.6", RTLD_NOW);
  if (!h) { fprintf (stderr, "dlopen: %s\n", dlerror ()); return 2; }
  f1 r_asin = (f1) dlsym (h, "asin"), r_acos = (f1) dlsym (h, "acos"), r_atan = (f1) dlsym (h, "atan");
  f2 r_atan2 = (f2) dlsym (h, "atan2");
  struct { const char *name; f1 lp, ref; int inv; } fs[] = { { "asin", lp_asin, 0, 1 }, { "acos", lp_acos, 0, 1 }, { "atan", lp_atan, 0, 0 } };
  fs[0].ref = r_asin; fs[1].ref = r_acos; fs[2].ref = r_atan;
  for (int k = 0; k < 3; k++)
    {
      static const char *dn[] = { "specials", "bits", "unif[-1,1]", "near+-1", "logu[-60,1]", "logu[-1074,1023]", "unif[-20,20]", "logu[-30,60]" };
      long cnt[8] = { 0 }, shown = 0;
      for (size_t i = 0; i < NS; i++) cnt[0] += bad1 (fs[k].name, dn[0], fs[k].lp, fs[k].ref, specials[i], &shown);
      for (long i = 0; i < n; i++) cnt[1] += bad1 (fs[k].name, dn[1], fs[k].lp, fs[k].ref, bits (rnd ()), &shown);
      if (fs[k].inv)
	{
	  for (long i = 0; i < n; i++) cnt[2] += bad1 (fs[k].name, dn[2], fs[k].lp, fs[k].ref, unif (-1, 1), &shown);
	  for (long i = 0; i < n; i++) { double d = logu (-60, -1); cnt[3] += bad1 (fs[k].name, dn[3], fs[k].lp, fs[k].ref, d < 0 ? -1 - d : 1 - d, &shown); }
	  for (long i = 0; i < n; i++) cnt[4] += bad1 (fs[k].name, dn[4], fs[k].lp, fs[k].ref, logu (-60, -1), &shown);
	}
      else
	{
	  for (long i = 0; i < n; i++) cnt[5] += bad1 (fs[k].name, dn[5], fs[k].lp, fs[k].ref, logu (-1074, 1023), &shown);
	  for (long i = 0; i < n; i++) cnt[6] += bad1 (fs[k].name, dn[6], fs[k].lp, fs[k].ref, unif (-20, 20), &shown);
	  for (long i = 0; i < n; i++) cnt[7] += bad1 (fs[k].name, dn[7], fs[k].lp, fs[k].ref, logu (-30, 60), &shown);
	}
      long t = 0; printf ("%s:", fs[k].name);
      for (int d = 0; d < 8; d++) if (cnt[d] || d == 0 || (fs[k].inv ? (d >= 1 && d <= 4) : (d == 1 || d >= 5))) { printf (" %s=%ld", dn[d], cnt[d]); t += cnt[d]; }
      printf (" total=%ld\n", t); total_bad += t;
    }
  {
    static const char *dn[] = { "specials^2", "bits", "logu[-1074,1023]^2", "unif[-10,10]^2", "logu[-30,30]^2", "close-ratio", "logu[-60,60]^2" };
    long cnt[7] = { 0 }, shown = 0;
    for (size_t i = 0; i < NS; i++) for (size_t j = 0; j < NS; j++) cnt[0] += bad2 (dn[0], lp_atan2, r_atan2, specials[i], specials[j], &shown);
    for (long i = 0; i < n; i++) cnt[1] += bad2 (dn[1], lp_atan2, r_atan2, bits (rnd ()), bits (rnd ()), &shown);
    for (long i = 0; i < n; i++) cnt[2] += bad2 (dn[2], lp_atan2, r_atan2, logu (-1074, 1023), logu (-1074, 1023), &shown);
    for (long i = 0; i < n; i++) cnt[3] += bad2 (dn[3], lp_atan2, r_atan2, unif (-10, 10), unif (-10, 10), &shown);
    for (long i = 0; i < n; i++) cnt[4] += bad2 (dn[4], lp_atan2, r_atan2, logu (-30, 30), logu (-30, 30), &shown);
    for (long i = 0; i < n; i++) { double x = logu (-30, 30); double y = x * (1 + logu (-50, -1)); if (rnd () & 1) y = -y; cnt[5] += bad2 (dn[5], lp_atan2, r_atan2, y, x, &shown); }
    for (long i = 0; i < n; i++) cnt[6] += bad2 (dn[6], lp_atan2, r_atan2, logu (-60, 60), logu (-60, 60), &shown);
    long t = 0; printf ("atan2:");
    for (int d = 0; d < 7; d++) { printf (" %s=%ld", dn[d], cnt[d]); t += cnt[d]; }
    printf (" total=%ld\n", t); total_bad += t;
  }
  printf ("TOTAL mismatches: %ld\n", total_bad);
  return total_bad != 0;
}
