/* Smoke test: lp_* (vendored glibc 2.39 flt-32) vs the system libm.so.6.
   One-argument functions: all 2^32 inputs.  atan2f/powf: N random pairs
   (default 1e8) plus a special-value grid.  Results compared bitwise
   (NaN vs NaN counts as a match only when the bits are equal too; NaN
   payload-only differences are reported separately).
   Build (from the flt dir):
     for f in $(grep -v '^#' SOURCES.txt); do $CC <fixed flags> -c $f; done
     $CC -O2 -I. test/smoke.c *.o -o smoke -ldl -lm -lpthread
   Usage: smoke [fn ...] [-n pairs]   (default: all functions)  */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

float lp_sinf (float), lp_cosf (float), lp_tanf (float), lp_asinf (float),
  lp_acosf (float), lp_atanf (float), lp_expf (float), lp_logf (float);
float lp_atan2f (float, float), lp_powf (float, float);

typedef float (*f1_t) (float);
typedef float (*f2_t) (float, float);
static const struct { const char *name; f1_t lp; } F1[] = {
  {"sinf", lp_sinf}, {"cosf", lp_cosf}, {"tanf", lp_tanf},
  {"asinf", lp_asinf}, {"acosf", lp_acosf}, {"atanf", lp_atanf},
  {"expf", lp_expf}, {"logf", lp_logf}};
static const struct { const char *name; f2_t lp; } F2[] = {
  {"atan2f", lp_atan2f}, {"powf", lp_powf}};

static uint32_t bits (float f) { uint32_t u; memcpy (&u, &f, 4); return u; }
static float flt (uint32_t u) { float f; memcpy (&f, &u, 4); return f; }

#define NTH 2
struct job { f1_t lp, sys; f2_t lp2, sys2; uint64_t lo, hi, seed;
  uint64_t bad, nanbad; uint32_t ex[4][3]; };

static void record (struct job *j, uint32_t a, uint32_t b, float r1, float r2)
{
  if (isnan (r1) && isnan (r2)) j->nanbad++;
  else { if (j->bad < 4) { j->ex[j->bad][0] = a; j->ex[j->bad][1] = b;
      j->ex[j->bad][2] = bits (r1) ^ bits (r2); } j->bad++; }
}

static void *run1 (void *p)
{
  struct job *j = p;
  for (uint64_t i = j->lo; i < j->hi; i++)
    {
      float x = flt ((uint32_t) i);
      float r1 = j->lp (x), r2 = j->sys (x);
      if (bits (r1) != bits (r2)) record (j, (uint32_t) i, 0, r1, r2);
    }
  return NULL;
}

static uint64_t rng (uint64_t *s)
{ *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }

/* Random pair: mix of raw bit patterns and "interesting" magnitudes.  */
static void gen (uint64_t *s, int ispow, uint32_t *a, uint32_t *b)
{
  uint64_t r = rng (s);
  *a = (uint32_t) r; *b = (uint32_t) (r >> 32);
  uint64_t m = rng (s) & 3;
  if (m == 1 && ispow)
    { /* x near 1 with arbitrary y; or moderate x and y.  */
      *a = (*a & 0x807fffff) | ((uint32_t) (120 + (rng (s) % 16)) << 23);
      *b = (*b & 0x807fffff) | ((uint32_t) (110 + (rng (s) % 30)) << 23); }
  else if (m == 1)
    { *a = (*a & 0x807fffff) | ((uint32_t) (90 + (rng (s) % 76)) << 23);
      *b = (*b & 0x807fffff) | ((uint32_t) (90 + (rng (s) % 76)) << 23); }
  else if (m == 2 && ispow)
    { /* integer-valued y, x of any sign.  */
      float y = (float) ((int) (rng (s) % 201) - 100);
      *b = bits (y);
      *a = (*a & 0x807fffff) | ((uint32_t) (100 + (rng (s) % 56)) << 23); }
  else if (m == 2)
    { /* exponents close together.  */
      uint32_t e = 1 + rng (s) % 253;
      *a = (*a & 0x807fffff) | (e << 23);
      *b = (*b & 0x807fffff) | ((e + (rng (s) % 5) - 2) << 23); }
}

static void *run2 (void *p)
{
  struct job *j = p;
  uint64_t s = j->seed;
  int ispow = j->lp2 == lp_powf;
  for (uint64_t i = j->lo; i < j->hi; i++)
    {
      uint32_t a, b;
      gen (&s, ispow, &a, &b);
      float r1 = j->lp2 (flt (a), flt (b)), r2 = j->sys2 (flt (a), flt (b));
      if (bits (r1) != bits (r2)) record (j, a, b, r1, r2);
    }
  return NULL;
}

static const uint32_t SPEC[] = {
  0x00000000, 0x80000000, 0x3f800000, 0xbf800000, 0x40000000, 0xc0000000,
  0x3f000000, 0xbf000000, 0x7f800000, 0xff800000, 0x7fc00000, 0xffc00000,
  0x7fa00000, 0xffa00000, 0x00000001, 0x80000001, 0x007fffff, 0x807fffff,
  0x00800000, 0x80800000, 0x7f7fffff, 0xff7fffff, 0x40400000, 0xc0400000,
  0x3f7fffff, 0x3f800001, 0xbf7fffff, 0xbf800001, 0x4b000000, 0xcb000000,
  0x4b000001, 0xcb000001, 0x4b800000, 0x4f000000, 0xcf000000, 0x3eaaaaab,
  0x40490fdb, 0xc0490fdb, 0x3fc90fdb, 0xbfc90fdb, 0x42b17218, 0x42fe0000,
  0xc3160000, 0x43000000, 0xc3000000, 0x3effffff, 0x4effffff, 0x7f000000,
  0x7fc00001, 0xffc00002, 0x7f800003, 0xff800004, 0x7fc12345, 0xff812345};

int main (int argc, char **argv)
{
  uint64_t npairs = 100000000;
  const char *want[16]; int nw = 0;
  for (int i = 1; i < argc; i++)
    if (!strcmp (argv[i], "-n") && i + 1 < argc) npairs = strtoull (argv[++i], 0, 10);
    else if (nw < 16) want[nw++] = argv[i];
  void *h = dlopen ("libm.so.6", RTLD_NOW);
  if (!h) { fprintf (stderr, "dlopen: %s\n", dlerror ()); return 2; }
  uint64_t total = 0;
#define WANTED(n) (nw == 0 || ({ int w_ = 0; for (int k = 0; k < nw; k++) w_ |= !strcmp (want[k], n); w_; }))
  for (size_t f = 0; f < sizeof F1 / sizeof F1[0]; f++)
    {
      if (!WANTED (F1[f].name)) continue;
      f1_t sys = (f1_t) dlsym (h, F1[f].name);
      struct job j[NTH]; pthread_t t[NTH];
      for (int k = 0; k < NTH; k++)
	{ memset (&j[k], 0, sizeof j[k]); j[k].lp = F1[f].lp; j[k].sys = sys;
	  j[k].lo = (1ULL << 32) * k / NTH; j[k].hi = (1ULL << 32) * (k + 1) / NTH;
	  pthread_create (&t[k], 0, run1, &j[k]); }
      uint64_t bad = 0, nb = 0;
      for (int k = 0; k < NTH; k++) { pthread_join (t[k], 0); bad += j[k].bad; nb += j[k].nanbad; }
      printf ("%-7s exhaustive 2^32: mismatches %llu (nan-payload-only %llu)\n", F1[f].name,
	      (unsigned long long) bad, (unsigned long long) nb);
      for (int k = 0; k < NTH; k++)
	for (uint64_t e = 0; e < j[k].bad && e < 4; e++)
	  printf ("   x=0x%08x xorbits=0x%08x\n", j[k].ex[e][0], j[k].ex[e][2]);
      total += bad + nb;
    }
  for (size_t f = 0; f < sizeof F2 / sizeof F2[0]; f++)
    {
      if (!WANTED (F2[f].name)) continue;
      f2_t sys = (f2_t) dlsym (h, F2[f].name);
      uint64_t sbad = 0, nspec = sizeof SPEC / sizeof SPEC[0];
      for (uint64_t a = 0; a < nspec; a++)
	for (uint64_t b = 0; b < nspec; b++)
	  {
	    float r1 = F2[f].lp (flt (SPEC[a]), flt (SPEC[b])), r2 = sys (flt (SPEC[a]), flt (SPEC[b]));
	    if (bits (r1) != bits (r2))
	      { if (sbad < 4) printf ("   special x=0x%08x y=0x%08x\n", SPEC[a], SPEC[b]); sbad++; }
	  }
      struct job j[NTH]; pthread_t t[NTH];
      for (int k = 0; k < NTH; k++)
	{ memset (&j[k], 0, sizeof j[k]); j[k].lp2 = F2[f].lp; j[k].sys2 = sys;
	  j[k].lo = npairs * k / NTH; j[k].hi = npairs * (k + 1) / NTH;
	  j[k].seed = 0x9e3779b97f4a7c15ULL * (k + 1) + f;
	  pthread_create (&t[k], 0, run2, &j[k]); }
      uint64_t bad = 0, nb = 0;
      for (int k = 0; k < NTH; k++) { pthread_join (t[k], 0); bad += j[k].bad; nb += j[k].nanbad; }
      printf ("%-7s special %llux%llu: mismatches %llu; random %llu pairs: mismatches %llu (nan-payload-only %llu)\n",
	      F2[f].name, (unsigned long long) nspec, (unsigned long long) nspec, (unsigned long long) sbad,
	      (unsigned long long) npairs, (unsigned long long) bad, (unsigned long long) nb);
      for (int k = 0; k < NTH; k++)
	for (uint64_t e = 0; e < j[k].bad && e < 4; e++)
	  printf ("   x=0x%08x y=0x%08x xorbits=0x%08x\n", j[k].ex[e][0], j[k].ex[e][1], j[k].ex[e][2]);
      total += sbad + bad + nb;
    }
  printf ("TOTAL mismatches %llu\n", (unsigned long long) total);
  return total != 0;
}
