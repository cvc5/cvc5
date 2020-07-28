/*********************                                                        */
/*! \file configuration_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Provides compile-time configuration information about the
 ** CVC4 library.
 **/

#include "cvc4_private.h"

#ifndef CVC4__CONFIGURATION_PRIVATE_H
#define CVC4__CONFIGURATION_PRIVATE_H

#include <string>

#include "base/configuration.h"

namespace CVC4 {

#ifdef CVC4_DEBUG
#  define IS_DEBUG_BUILD true
#else /* CVC4_DEBUG */
#  define IS_DEBUG_BUILD false
#endif /* CVC4_DEBUG */

#ifdef CVC4_STATISTICS_ON
#  define IS_STATISTICS_BUILD true
#else /* CVC4_STATISTICS_ON */
#  define IS_STATISTICS_BUILD false
#endif /* CVC4_STATISTICS_ON */

#ifdef CVC4_TRACING
#  define IS_TRACING_BUILD true
#else /* CVC4_TRACING */
#  define IS_TRACING_BUILD false
#endif /* CVC4_TRACING */

#ifdef CVC4_DUMPING
#  define IS_DUMPING_BUILD true
#else /* CVC4_DUMPING */
#  define IS_DUMPING_BUILD false
#endif /* CVC4_DUMPING */

#ifdef CVC4_MUZZLE
#  define IS_MUZZLED_BUILD true
#else /* CVC4_MUZZLE */
#  define IS_MUZZLED_BUILD false
#endif /* CVC4_MUZZLE */

#ifdef CVC4_ASSERTIONS
#  define IS_ASSERTIONS_BUILD true
#else /* CVC4_ASSERTIONS */
#  define IS_ASSERTIONS_BUILD false
#endif /* CVC4_ASSERTIONS */

#ifdef CVC4_PROOF
#  define IS_PROOFS_BUILD true
#else  /* CVC4_PROOF */
#  define IS_PROOFS_BUILD false
#endif /* CVC4_PROOF */

#ifdef CVC4_COVERAGE
#  define IS_COVERAGE_BUILD true
#else /* CVC4_COVERAGE */
#  define IS_COVERAGE_BUILD false
#endif /* CVC4_COVERAGE */

#ifdef CVC4_PROFILING
#  define IS_PROFILING_BUILD true
#else /* CVC4_PROFILING */
#  define IS_PROFILING_BUILD false
#endif /* CVC4_PROFILING */

#ifdef CVC4_COMPETITION_MODE
#  define IS_COMPETITION_BUILD true
#else /* CVC4_COMPETITION_MODE */
#  define IS_COMPETITION_BUILD false
#endif /* CVC4_COMPETITION_MODE */

#ifdef CVC4_GMP_IMP
#  define IS_GMP_BUILD true
#else /* CVC4_GMP_IMP */
#  define IS_GMP_BUILD false
#endif /* CVC4_GMP_IMP */

#ifdef CVC4_CLN_IMP
#  define IS_CLN_BUILD true
#else /* CVC4_CLN_IMP */
#  define IS_CLN_BUILD false
#endif /* CVC4_CLN_IMP */

#if CVC4_USE_GLPK
#  define IS_GLPK_BUILD true
#else /* CVC4_USE_GLPK */
#  define IS_GLPK_BUILD false
#endif /* CVC4_USE_GLPK */

#if CVC4_USE_ABC
#  define IS_ABC_BUILD true
#else /* CVC4_USE_ABC */
#  define IS_ABC_BUILD false
#endif /* CVC4_USE_ABC */

#if CVC4_USE_CADICAL
#define IS_CADICAL_BUILD true
#else /* CVC4_USE_CADICAL */
#define IS_CADICAL_BUILD false
#endif /* CVC4_USE_CADICAL */

#if CVC4_USE_CRYPTOMINISAT
#  define IS_CRYPTOMINISAT_BUILD true
#else /* CVC4_USE_CRYPTOMINISAT */
#  define IS_CRYPTOMINISAT_BUILD false
#endif /* CVC4_USE_CRYPTOMINISAT */

#if CVC4_USE_DRAT2ER
#  define IS_DRAT2ER_BUILD true
#else /* CVC4_USE_DRAT2ER */
#  define IS_DRAT2ER_BUILD false
#endif /* CVC4_USE_DRAT2ER */

#if CVC4_USE_KISSAT
#define IS_KISSAT_BUILD true
#else /* CVC4_USE_KISSAT */
#define IS_KISSAT_BUILD false
#endif /* CVC4_USE_KISSAT */

#if CVC4_USE_LFSC
#define IS_LFSC_BUILD true
#else /* CVC4_USE_LFSC */
#define IS_LFSC_BUILD false
#endif /* CVC4_USE_LFSC */

#if CVC4_USE_POLY
#define IS_POLY_BUILD true
#else /* CVC4_USE_POLY */
#define IS_POLY_BUILD false
#endif /* CVC4_USE_POLY */

#if HAVE_LIBEDITLINE
#define IS_EDITLINE_BUILD true
#else /* HAVE_LIBEDITLINE */
#define IS_EDITLINE_BUILD false
#endif /* HAVE_LIBEDITLINE */

#ifdef CVC4_USE_SYMFPU
#define IS_SYMFPU_BUILD true
#else /* HAVE_SYMFPU_HEADERS */
#define IS_SYMFPU_BUILD false
#endif /* HAVE_SYMFPU_HEADERS */

#if CVC4_GPL_DEPS
#  define IS_GPL_BUILD true
#else /* CVC4_GPL_DEPS */
#  define IS_GPL_BUILD false
#endif /* CVC4_GPL_DEPS */

#define IS_ASAN_BUILD false

// GCC test
#if defined(__SANITIZE_ADDRESS__)
#  undef IS_ASAN_BUILD
#  define IS_ASAN_BUILD true
#endif /* defined(__SANITIZE_ADDRESS__) */

// Clang test
#if defined(__has_feature)
#  if __has_feature(address_sanitizer)
#    undef IS_ASAN_BUILD
#    define IS_ASAN_BUILD true
#  endif /* __has_feature(address_sanitizer) */
#endif /* defined(__has_feature) */

#ifdef CVC4_USE_UBSAN
#define IS_UBSAN_BUILD true
#else /* CVC4_USE_UBSAN */
#define IS_UBSAN_BUILD false
#endif /* CVC4_USE_UBSAN */

#define IS_TSAN_BUILD false

// GCC test
#if defined(__SANITIZE_THREAD__)
#undef IS_TSAN_BUILD
#define IS_TSAN_BUILD true
#endif /* defined(__SANITIZE_THREAD__) */

// Clang test
#if defined(__has_feature)
#if __has_feature(thread_sanitizer)
#undef IS_TSAN_BUILD
#define IS_TSAN_BUILD true
#endif /* __has_feature(thread_sanitizer) */
#endif /* defined(__has_feature) */

}/* CVC4 namespace */

#endif /* CVC4__CONFIGURATION_PRIVATE_H */
