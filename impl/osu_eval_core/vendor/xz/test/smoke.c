/* Smoke test: vendored lp_lzma_* (static) vs the system liblzma.so.5 (dlopen), on the LZMA
 * frame stream of every .osr given on the command line (plus truncated / corrupted variants).
 * The decode loop is the one of impl/osu_eval_core/src/lzma.rs (same buffer growth, LZMA_FINISH,
 * memlimit UINT64_MAX). Requires byte-identical output and identical lzma_ret codes.
 *
 * Build (from this dir's parent):
 *   cc -O2 -I. -DHAVE_CONFIG_H -Isrc/common -Isrc/liblzma/api test/smoke.c <the SOURCES.txt .c> -ldl -o smoke
 *   ./smoke file1.osr file2.osr ...
 */
#include "config.h"
#include <lzma.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef lzma_ret (*alone_fn)(lzma_stream *, uint64_t);
typedef lzma_ret (*code_fn)(lzma_stream *, lzma_action);
typedef void (*end_fn)(lzma_stream *);
struct lib { alone_fn alone; code_fn code; end_fn end; };

struct res { int init_ret; int ret; uint8_t *out; size_t len; uint64_t total_in, total_out; };

/* Mirrors lzma.rs lzma_alone_decode; ret = final lzma_ret (LZMA_STREAM_END on success),
 * or -1 for OutputTooLarge. */
static struct res decode(const struct lib *L, const uint8_t *in, size_t n, size_t max_out) {
	struct res r = {0};
	lzma_stream s = LZMA_STREAM_INIT;
	r.init_ret = L->alone(&s, UINT64_MAX);
	if (r.init_ret != LZMA_OK) { r.ret = -2; return r; }
	size_t cap = n * 4 + 4096;
	if (cap > max_out) cap = max_out + 1;
	uint8_t *out = malloc(cap);
	size_t len = 0;
	s.next_in = in; s.avail_in = n;
	for (;;) {
		if (len == cap) {
			if (cap > max_out) { L->end(&s); r.ret = -1; goto done; }
			size_t nc = cap * 2; if (nc > max_out + 1) nc = max_out + 1;
			out = realloc(out, nc); cap = nc;
		}
		s.next_out = out + len; s.avail_out = cap - len;
		lzma_ret ret = L->code(&s, LZMA_FINISH);
		len = cap - s.avail_out;
		if (ret == LZMA_STREAM_END) { r.ret = ret; break; }
		if (ret != LZMA_OK) { r.ret = ret; L->end(&s); goto done; }
	}
	L->end(&s);
	if (len > max_out) r.ret = -1;
done:
	r.out = out; r.len = len; r.total_in = s.total_in; r.total_out = s.total_out;
	return r;
}

static long n_cmp, n_bad, n_ok_full, err_hist[16];

static void compare(const struct lib *A, const struct lib *B, const uint8_t *in, size_t n,
		size_t max_out, const char *name, const char *what) {
	struct res a = decode(A, in, n, max_out), b = decode(B, in, n, max_out);
	n_cmp++;
	if (a.init_ret != b.init_ret || a.ret != b.ret || a.len != b.len
			|| a.total_in != b.total_in || a.total_out != b.total_out
			|| (a.len && memcmp(a.out, b.out, a.len) != 0)) {
		n_bad++;
		fprintf(stderr, "MISMATCH %s [%s]: vendored ret %d len %zu in %llu | system ret %d len %zu in %llu\n",
			name, what, a.ret, a.len, (unsigned long long)a.total_in,
			b.ret, b.len, (unsigned long long)b.total_in);
	}
	err_hist[(a.ret + 2) & 15]++;
	free(a.out); free(b.out);
}

static int rd_str(const uint8_t *b, size_t n, size_t *p) {
	if (*p >= n) return 0;
	uint8_t t = b[(*p)++];
	if (t == 0) return 1;
	if (t != 0x0b) return 0;
	uint64_t len = 0; int sh = 0;
	for (;;) { if (*p >= n || sh > 56) return 0; uint8_t c = b[(*p)++]; len |= (uint64_t)(c & 0x7f) << sh; if (!(c & 0x80)) break; sh += 7; }
	if (len > n - *p) return 0;
	*p += len; return 1;
}

/* .osr: mode u8, version i32, md5 str, player str, replay md5 str, 6*u16, score i32, combo u16,
 * perfect u8, mods i32, lifebar str, timestamp i64, compressed length i32, LZMA bytes. */
static int frame_stream(const uint8_t *b, size_t n, size_t *off, size_t *len) {
	size_t p = 5;
	if (!rd_str(b, n, &p) || !rd_str(b, n, &p) || !rd_str(b, n, &p)) return 0;
	p += 12 + 4 + 2 + 1 + 4;
	if (!rd_str(b, n, &p)) return 0;
	p += 8;
	if (p + 4 > n) return 0;
	uint32_t l = b[p] | b[p+1] << 8 | b[p+2] << 16 | (uint32_t)b[p+3] << 24; p += 4;
	if (l > n - p) return 0;
	*off = p; *len = l; return 1;
}

static uint64_t rng = 0x9E3779B97F4A7C15ull;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

int main(int argc, char **argv) {
	struct lib V = { lzma_alone_decoder, lzma_code, lzma_end };  /* = lp_lzma_* via lp_prefix.h */
	void *h = dlopen("liblzma.so.5", RTLD_NOW | RTLD_LOCAL);
	if (!h) { fprintf(stderr, "no system liblzma\n"); return 2; }
	struct lib S = { (alone_fn)dlsym(h, "lzma_alone_decoder"), (code_fn)dlsym(h, "lzma_code"), (end_fn)dlsym(h, "lzma_end") };
	const char *(*sysver)(void) = (const char *(*)(void))dlsym(h, "lzma_version_string");
	printf("system liblzma %s, vendored %s\n", sysver(), lp_lzma_version_string());
	long files = 0, skipped = 0, corrupt_runs = 0;
	const size_t MAX = 64u << 20;
	for (int i = 1; i < argc; i++) {
		FILE *f = fopen(argv[i], "rb");
		if (!f) { skipped++; continue; }
		fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
		uint8_t *b = malloc(sz ? sz : 1);
		if (fread(b, 1, sz, f) != (size_t)sz) { fclose(f); free(b); skipped++; continue; }
		fclose(f);
		size_t off, len;
		if (!frame_stream(b, sz, &off, &len)) { skipped++; free(b); continue; }
		files++;
		const uint8_t *in = b + off;
		compare(&V, &S, in, len, MAX, argv[i], "full");
		/* every 10th file: corrupted / truncated variants */
		if (i % 10 == 0 && len > 16) {
			uint8_t *c = malloc(len);
			size_t cuts[] = {0, 1, 4, 5, 12, 13, 14, len / 2, len - 1, len - 5};
			for (size_t k = 0; k < sizeof cuts / sizeof *cuts; k++)
				compare(&V, &S, in, cuts[k], MAX, argv[i], "truncated");
			for (int k = 0; k < 8; k++) {           /* random byte flips in the stream body */
				memcpy(c, in, len);
				int nf = 1 + (int)(next() % 4);
				for (int j = 0; j < nf; j++) c[13 + next() % (len - 13)] ^= (uint8_t)(1 + next() % 255);
				compare(&V, &S, c, len, MAX, argv[i], "flip");
			}
			memcpy(c, in, len); c[0] = 225; compare(&V, &S, c, len, MAX, argv[i], "props=225");
			memcpy(c, in, len); c[0] = (uint8_t)(next() % 225); compare(&V, &S, c, len, MAX, argv[i], "props random");
			memcpy(c, in, len); c[1] = 0x12; c[2] = 0x34; c[3] = 0x56; c[4] = 0x78; compare(&V, &S, c, len, MAX, argv[i], "odd dict");
			memcpy(c, in, len); memset(c + 5, 0xff, 8); compare(&V, &S, c, len, MAX, argv[i], "unknown size");
			memcpy(c, in, len); c[5] ^= 1; compare(&V, &S, c, len, MAX, argv[i], "size +-1");
			memcpy(c, in, len); c[12] = 0x01; compare(&V, &S, c, len, MAX, argv[i], "size huge");
			memcpy(c, in, len); c[13] = 0x80; compare(&V, &S, c, len, MAX, argv[i], "rc first byte");
			compare(&V, &S, in, len, 1000, argv[i], "max_out 1000");
			corrupt_runs++;
			free(c);
		}
		free(b);
	}
	printf("files %ld (skipped %ld), corrupted-sets %ld, comparisons %ld, mismatches %ld\n",
		files, skipped, corrupt_runs, n_cmp, n_bad);
	printf("result codes (vendored): ok/STREAM_END %ld, OutputTooLarge %ld, init-fail %ld, FORMAT %ld, DATA %ld, BUF %ld, other %ld\n",
		err_hist[(1 + 2) & 15], err_hist[1], err_hist[0], err_hist[(7 + 2) & 15], err_hist[(9 + 2) & 15], err_hist[(10 + 2) & 15],
		n_cmp - err_hist[3] - err_hist[1] - err_hist[0] - err_hist[9] - err_hist[11] - err_hist[12]);
	return n_bad ? 1 : 0;
}
