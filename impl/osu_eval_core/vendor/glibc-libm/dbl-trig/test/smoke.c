/* Smoke test: lp_sin/lp_cos/lp_tan vs the system glibc libm.so.6 (dlsym), bitwise.
   usage: smoke [N]   (N per random category, default 1e7)
   build: see ../FLAGS.txt; link with -ldl */
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

double lp_sin (double), lp_cos (double), lp_tan (double);
typedef double (*fn) (double);

static uint64_t st = 0x9E3779B97F4A7C15ull;
static uint64_t next (void)
{
  uint64_t z = (st += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}
static double b2d (uint64_t b) { double d; memcpy (&d, &b, 8); return d; }
static uint64_t d2b (double d) { uint64_t b; memcpy (&b, &d, 8); return b; }
static double unit (void) { return (next () >> 11) * 0x1p-53; }

static const char *names[3] = { "sin", "cos", "tan" };
static fn mine[3] = { lp_sin, lp_cos, lp_tan };
static fn ref[3];
static long mism[3], shown[3], total;

static void check (double x)
{
  total++;
  for (int f = 0; f < 3; f++)
    {
      double a = mine[f] (x), b = ref[f] (x);
      if (d2b (a) != d2b (b))
        {
          mism[f]++;
          if (shown[f]++ < 5)
            printf ("MISMATCH %s(%a) [%016llx]: lp %a ref %a\n", names[f], x,
                    (unsigned long long) d2b (x), a, b);
        }
    }
}

int main (int argc, char **argv)
{
  long n = argc > 1 ? atol (argv[1]) : 10000000;
  void *h = dlopen ("libm.so.6", RTLD_NOW);
  if (!h) { fprintf (stderr, "dlopen: %s\n", dlerror ()); return 2; }
  for (int f = 0; f < 3; f++)
    if (!(ref[f] = (fn) dlsym (h, names[f]))) { fprintf (stderr, "dlsym %s\n", names[f]); return 2; }

  static const double sp[] = { 0.0, -0.0, INFINITY, -INFINITY, NAN, -NAN, 0x1p-1074, -0x1p-1074,
    0x1p-1022, 0x1.fffffffffffffp1023, -0x1.fffffffffffffp1023, 1e300, -1e300, 1e22, 1e100,
    105414350.0, 105414351.0, 1e8, 25.0, 0.787, 0.0608, 1.259e-8, 0x1p-26, 0x1p-27, 0.855469,
    2.426265, 3.141592653589793, 1.5707963267948966, 6.283185307179586, 0x1.921fb54442d18p+1 };
  for (unsigned i = 0; i < sizeof sp / sizeof *sp; i++)
    { check (sp[i]); check (nextafter (sp[i], INFINITY)); check (nextafter (sp[i], -INFINITY)); }
  long base = total;
  for (long i = 0; i < n; i++) check (b2d (next ()));               /* uniform bit patterns */
  printf ("bits:    %ld inputs, mismatches sin %ld cos %ld tan %ld\n", total - base, mism[0], mism[1], mism[2]);
  for (long i = 0; i < n; i++) check (unit () * 20.0 - 10.0);       /* uniform [-10,10] */
  printf ("+[-10,10]: cumulative mismatches sin %ld cos %ld tan %ld\n", mism[0], mism[1], mism[2]);
  for (long i = 0; i < n / 4; i++)                                  /* log-uniform |x| in [2^-30, 2^40] */
    { double x = ldexp (1.0 + unit (), (int) (next () % 70) - 30); check ((next () & 1) ? -x : x); }
  printf ("+log-uniform: cumulative mismatches sin %ld cos %ld tan %ld\n", mism[0], mism[1], mism[2]);
  printf ("TOTAL %ld inputs: sin %ld cos %ld tan %ld\n", total, mism[0], mism[1], mism[2]);
  return (mism[0] | mism[1] | mism[2]) ? 1 : 0;
}
