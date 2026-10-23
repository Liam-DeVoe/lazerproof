/* Renames all external symbols of the vendored liblzma subset to lp_* (included from config.h,
 * i.e. before lzma.h, so the public API is declared and defined as lp_lzma_*). Exported API used
 * by impl/osu_eval_core/src/lzma.rs: lp_lzma_alone_decoder, lp_lzma_code, lp_lzma_end. */
#ifndef LP_XZ_PREFIX_H
#define LP_XZ_PREFIX_H
#define lzma_alloc lp_lzma_alloc
#define lzma_alloc_zero lp_lzma_alloc_zero
#define lzma_alone_decoder lp_lzma_alone_decoder
#define lzma_alone_decoder_init lp_lzma_alone_decoder_init
#define lzma_bufcpy lp_lzma_bufcpy
#define lzma_code lp_lzma_code
#define lzma_end lp_lzma_end
#define lzma_free lp_lzma_free
#define lzma_get_check lp_lzma_get_check
#define lzma_get_progress lp_lzma_get_progress
#define lzma_lz_decoder_init lp_lzma_lz_decoder_init
#define lzma_lz_decoder_memusage lp_lzma_lz_decoder_memusage
#define lzma_lzma_decoder_create lp_lzma_lzma_decoder_create
#define lzma_lzma_decoder_init lp_lzma_lzma_decoder_init
#define lzma_lzma_decoder_memusage lp_lzma_lzma_decoder_memusage
#define lzma_lzma_decoder_memusage_nocheck lp_lzma_lzma_decoder_memusage_nocheck
#define lzma_lzma_lclppb_decode lp_lzma_lzma_lclppb_decode
#define lzma_lzma_props_decode lp_lzma_lzma_props_decode
#define lzma_memlimit_get lp_lzma_memlimit_get
#define lzma_memlimit_set lp_lzma_memlimit_set
#define lzma_memusage lp_lzma_memusage
#define lzma_next_end lp_lzma_next_end
#define lzma_next_filter_init lp_lzma_next_filter_init
#define lzma_next_filter_update lp_lzma_next_filter_update
#define lzma_strm_init lp_lzma_strm_init
#define lzma_version_number lp_lzma_version_number
#define lzma_version_string lp_lzma_version_string
#endif
