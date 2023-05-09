/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andres Noetzli, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Provide compile-time configuration information about the cvc5 library.
 */

#include "cvc5_private.h"

#ifndef CVC5__CONFIGURATION_PRIVATE_H
#define CVC5__CONFIGURATION_PRIVATE_H

#include <string>

#include "base/configuration.h"

namespace cvc5::internal {

#ifdef CVC5_DEBUG
#  define IS_DEBUG_BUILD true
#else /* CVC5_DEBUG */
#  define IS_DEBUG_BUILD false
#endif /* CVC5_DEBUG */

#ifdef CVC5_TRACING
#  define IS_TRACING_BUILD true
#else /* CVC5_TRACING */
#  define IS_TRACING_BUILD false
#endif /* CVC5_TRACING */

#ifdef CVC5_MUZZLE
#  define IS_MUZZLED_BUILD true
#else /* CVC5_MUZZLE */
#  define IS_MUZZLED_BUILD false
#endif /* CVC5_MUZZLE */

#ifdef CVC5_ASSERTIONS
#  define IS_ASSERTIONS_BUILD true
#else /* CVC5_ASSERTIONS */
#  define IS_ASSERTIONS_BUILD false
#endif /* CVC5_ASSERTIONS */

#ifdef CVC5_COVERAGE
#  define IS_COVERAGE_BUILD true
#else /* CVC5_COVERAGE */
#  define IS_COVERAGE_BUILD false
#endif /* CVC5_COVERAGE */

#ifdef CVC5_PROFILING
#  define IS_PROFILING_BUILD true
#else /* CVC5_PROFILING */
#  define IS_PROFILING_BUILD false
#endif /* CVC5_PROFILING */

#ifdef CVC5_COMPETITION_MODE
#  define IS_COMPETITION_BUILD true
#else /* CVC5_COMPETITION_MODE */
#  define IS_COMPETITION_BUILD false
#endif /* CVC5_COMPETITION_MODE */

#ifdef CVC5_GMP_IMP
#  define IS_GMP_BUILD true
#else /* CVC5_GMP_IMP */
#  define IS_GMP_BUILD false
#endif /* CVC5_GMP_IMP */

#ifdef CVC5_CLN_IMP
#  define IS_CLN_BUILD true
#else /* CVC5_CLN_IMP */
#  define IS_CLN_BUILD false
#endif /* CVC5_CLN_IMP */

#if CVC5_USE_GLPK
#  define IS_GLPK_BUILD true
#else /* CVC5_USE_GLPK */
#  define IS_GLPK_BUILD false
#endif /* CVC5_USE_GLPK */

#if CVC5_USE_CRYPTOMINISAT
#  define IS_CRYPTOMINISAT_BUILD true
#else /* CVC5_USE_CRYPTOMINISAT */
#  define IS_CRYPTOMINISAT_BUILD false
#endif /* CVC5_USE_CRYPTOMINISAT */

#if CVC5_USE_KISSAT
#define IS_KISSAT_BUILD true
#else /* CVC5_USE_KISSAT */
#define IS_KISSAT_BUILD false
#endif /* CVC5_USE_KISSAT */

#if CVC5_USE_POLY
#define IS_POLY_BUILD true
#else /* CVC5_USE_POLY */
#define IS_POLY_BUILD false
#endif /* CVC5_USE_POLY */

#if CVC5_USE_COCOA
#define IS_COCOA_BUILD true
#else /* CVC5_USE_COCOA */
#define IS_COCOA_BUILD false
#endif /* CVC5_USE_COCOA */

#if HAVE_LIBEDITLINE
#define IS_EDITLINE_BUILD true
#else /* HAVE_LIBEDITLINE */
#define IS_EDITLINE_BUILD false
#endif /* HAVE_LIBEDITLINE */

#if CVC5_GPL_DEPS
#  define IS_GPL_BUILD true
#else /* CVC5_GPL_DEPS */
#  define IS_GPL_BUILD false
#endif /* CVC5_GPL_DEPS */

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

#ifdef CVC5_USE_UBSAN
#define IS_UBSAN_BUILD true
#else /* CVC5_USE_UBSAN */
#define IS_UBSAN_BUILD false
#endif /* CVC5_USE_UBSAN */

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

}  // namespace cvc5::internal

#endif /* CVC5__CONFIGURATION_PRIVATE_H */
