/* TRUSTED BOUNDARY (docs/model-eval.md): LZMA "alone" (.lzma, 13-byte header) decompression for .osr payloads,
   delegated to the system liblzma (xz-utils, statically linked). Lazer uses SharpCompress' LzmaStream for the same
   format (LegacyScoreDecoder.cs:168-193). This is the only native code of the evaluator besides the Lean runtime.

   osu_lzma_alone_decode : @& ByteArray -> USize -> Except String ByteArray
   (`Except` built by hand: ctor 0 = error (String), ctor 1 = ok (ByteArray)). liblzma reports truncated input
   as LZMA_BUF_ERROR once no further progress is possible with LZMA_FINISH. */
#include <lean/lean.h>
#include <lzma.h>
#include <string.h>
#include <stdlib.h>

static lean_obj_res mk_except_error(const char *msg) {
    lean_object *r = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(r, 0, lean_mk_string(msg));
    return r;
}

static lean_obj_res mk_except_ok(lean_object *v) {
    lean_object *r = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(r, 0, v);
    return r;
}

LEAN_EXPORT lean_obj_res osu_lzma_alone_decode(b_lean_obj_arg input, size_t max_out) {
    const uint8_t *in = lean_sarray_cptr(input);
    size_t in_size = lean_sarray_size(input);
    lzma_stream strm = LZMA_STREAM_INIT;
    if (lzma_alone_decoder(&strm, UINT64_MAX) != LZMA_OK)
        return mk_except_error("lzma: decoder init failed");
    size_t cap = in_size * 4 + 4096, len = 0;
    if (cap > max_out) cap = max_out + 1;
    uint8_t *out = malloc(cap);
    if (!out) { lzma_end(&strm); return mk_except_error("lzma: out of memory"); }
    strm.next_in = in;
    strm.avail_in = in_size;
    lzma_ret ret;
    for (;;) {
        if (len == cap) {
            if (cap > max_out) { free(out); lzma_end(&strm); return mk_except_error("lzma: output too large"); }
            size_t ncap = cap * 2;
            if (ncap > max_out + 1) ncap = max_out + 1;
            uint8_t *n = realloc(out, ncap);
            if (!n) { free(out); lzma_end(&strm); return mk_except_error("lzma: out of memory"); }
            out = n; cap = ncap;
        }
        strm.next_out = out + len;
        strm.avail_out = cap - len;
        ret = lzma_code(&strm, LZMA_FINISH);
        len = cap - strm.avail_out;
        if (ret == LZMA_STREAM_END) break;
        if (ret != LZMA_OK) {
            free(out); lzma_end(&strm);
            switch (ret) {
                case LZMA_FORMAT_ERROR: return mk_except_error("lzma: format error");
                case LZMA_DATA_ERROR: return mk_except_error("lzma: data error");
                case LZMA_BUF_ERROR: return mk_except_error("lzma: truncated input");
                case LZMA_MEM_ERROR: return mk_except_error("lzma: out of memory");
                default: return mk_except_error("lzma: decode error");
            }
        }
    }
    lzma_end(&strm);
    if (len > max_out) { free(out); return mk_except_error("lzma: output too large"); }
    lean_object *arr = lean_alloc_sarray(1, len, len);
    memcpy(lean_sarray_cptr(arr), out, len);
    free(out);
    return mk_except_ok(arr);
}
