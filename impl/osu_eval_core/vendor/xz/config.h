/* config.h for the lazerproof vendored liblzma decoder subset (xz 5.4.5, Ubuntu
 * xz-utils 5.6.1+really5.4.5-1ubuntu0.4 patches applied). Hand-written, replaces the
 * autoconf-generated one. Only what the .lzma ("alone") decoder needs; no threads,
 * no CRC, no encoders. Portable C (gcc / clang, Linux / macOS). */
#ifndef LP_XZ_CONFIG_H
#define LP_XZ_CONFIG_H

/* glibc: expose sigset_t (mythread.h) also under strict -std=c11; no effect on macOS */
#ifndef _DEFAULT_SOURCE
#  define _DEFAULT_SOURCE 1
#endif
#define NDEBUG 1                   /* as configure without --enable-debug (Ubuntu build) */
#define HAVE_STDINT_H 1
#define HAVE_INTTYPES_H 1
#define HAVE_STDBOOL_H 1
#define HAVE__BOOL 1
#define HAVE_VISIBILITY 1          /* LZMA_API -> visibility("default") (overrides -fvisibility=hidden) */
#define HAVE_DECODER_LZMA1 1
#define PACKAGE_NAME "XZ Utils"
#define PACKAGE_URL "https://tukaani.org/xz/"
#define SIZEOF_SIZE_T __SIZEOF_SIZE_T__
/* Not defined on purpose: HAVE_BYTESWAP_H (glibc only), HAVE_SMALL, TUKLIB_FAST_UNALIGNED_ACCESS
 * (memcpy-based integer access everywhere; affects speed only), MYTHREAD_* (single-threaded),
 * HAVE_SYMBOL_VERSIONS_LINUX. */

/* Little-endian only (x86-64, aarch64). WORDS_BIGENDIAN stays undefined. */
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__
#  error "vendored xz: big-endian targets need WORDS_BIGENDIAN"
#endif

/* Rename every external symbol to lp_* so it never clashes with a system liblzma. */
#include "lp_prefix.h"

#endif
