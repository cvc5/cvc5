/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check macros for the cvc5 C API.
 *
 * These macros implement guards for the cvc5 C API functions.
 */

#include "cvc5_private.h"

#ifndef CVC5__CAPI__CHECKS_H
#define CVC5__CAPI__CHECKS_H

#include <cvc5/cvc5.h>

#include <cstdlib>
#include <iostream>
#include <sstream>

#include "api/cpp/cvc5_checks.h"
#include "base/check.h"

namespace cvc5 {

/* -------------------------------------------------------------------------- */

/**
 * Record an error that occurred during a cvc5 C API call.
 *
 * This sets the thread-local error flag and stores `msg` as the associated
 * error message. It is invoked by #CVC5_CAPI_TRY_CATCH_END whenever a C API
 * function catches an exception, instead of terminating the process. The
 * recorded state can be queried via `cvc5_has_error()` and
 * `cvc5_get_error_message()`.
 *
 * @param msg The error message to store.
 *
 * @note Exported for linkage of the parser library, which uses the
 *       #CVC5_CAPI_TRY_CATCH_END macro.
 */
CVC5_EXPORT void cvc5_capi_set_error(const std::string& msg);
/**
 * Clear the thread-local error state.
 *
 * This is invoked by #CVC5_CAPI_TRY_CATCH_BEGIN on entry of each guarded C API
 * function so that the error state always reflects the most recent call. It is
 * also exposed to users via `cvc5_reset_error()`.
 */
CVC5_EXPORT void cvc5_capi_reset_error();
/**
 * @return True if an error occurred during the most recent guarded C API call
 *         on the current thread.
 */
CVC5_EXPORT bool cvc5_capi_has_error();
/**
 * @return The message associated with the most recent error on the current
 *         thread, or the empty string if no error occurred. The returned
 *         pointer is valid until the next guarded C API call on this thread.
 */
CVC5_EXPORT const char* cvc5_capi_get_error_message();

/**
 * Reset the thread-local error state on entry of a guarded C API function.
 *
 * @note We do not start the `try` block here so that the reset is performed
 *       unconditionally, even for functions that perform work before their
 *       #CVC5_CAPI_TRY_CATCH_BEGIN.
 */
#define CVC5_CAPI_TRY_CATCH_BEGIN \
  cvc5::cvc5_capi_reset_error();  \
  try                             \
  {
/**
 * Capture any exception thrown by a guarded C API function as a thread-local
 * error instead of terminating the process. On error, the function falls
 * through and returns its default-initialized return value; the caller is
 * expected to check `cvc5_has_error()`.
 *
 * @note The trailing `catch (...)` ensures that no exception can escape the
 *       `extern "C"` boundary, which would call `std::terminate`. This is not
 *       merely theoretical: cvc5 links third-party libraries whose exception
 *       types do not derive from `std::exception` (e.g. CoCoALib's
 *       `CoCoA::ErrorInfo`, used by the finite-field theory). Should such an
 *       exception ever reach the C API uncaught (e.g. via a missed catch on
 *       some C++ code path), the catch-all records it instead of aborting.
 */
#define CVC5_CAPI_TRY_CATCH_END                                            \
  }                                                                        \
  catch (const cvc5::CVC5ApiException& e)                                  \
  {                                                                        \
    cvc5::cvc5_capi_set_error(e.getMessage());                             \
  }                                                                        \
  catch (const std::exception& e) { cvc5::cvc5_capi_set_error(e.what()); } \
  catch (...) { cvc5::cvc5_capi_set_error("unknown C++ exception"); }

#endif

#define CVC5_CAPI_CHECK_NOT_NULL(arg)                                          \
  CVC5_API_CHECK(arg != nullptr) << "invalid call to '" << __PRETTY_FUNCTION__ \
                                 << "', unexpected NULL argument"

#define CVC5_CAPI_CHECK_NOT_NULL_AT_IDX(arg, i)     \
  CVC5_API_CHECK(arg[i] != nullptr)                 \
      << "invalid call to '" << __PRETTY_FUNCTION__ \
      << "', unexpected NULL argument at index " << i

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_KIND(kind)                 \
  CVC5_API_CHECK((kind) >= CVC5_KIND_INTERNAL_KIND \
                 && (kind) < CVC5_KIND_LAST_KIND)  \
      << "invalid term kind"

#define CVC5_CAPI_CHECK_SORT_KIND(kind)                      \
  CVC5_API_CHECK((kind) >= CVC5_SORT_KIND_INTERNAL_SORT_KIND \
                 && (kind) < CVC5_SORT_KIND_LAST_SORT_KIND)  \
      << "invalid sort kind"

#define CVC5_CAPI_CHECK_RM(rm) \
  CVC5_API_CHECK((rm) >= 0 && (rm) < CVC5_RM_LAST) << "invalid rounding mode"

#define CVC5_CAPI_CHECK_UNKNOWN_EXPLANATION(e)                    \
  CVC5_API_CHECK((e) >= 0 && (e) < CVC5_UNKNOWN_EXPLANATION_LAST) \
      << "invalid unknown explanation kind"

#define CVC5_CAPI_CHECK_BLOCK_MODELS_MODE(mode)                       \
  CVC5_API_CHECK((mode) >= 0 && (mode) < CVC5_BLOCK_MODELS_MODE_LAST) \
      << "invalid block models mode"

#define CVC5_CAPI_CHECK_FIND_SYNTH_TARGET(target)                         \
  CVC5_API_CHECK((target) >= 0 && (target) < CVC5_FIND_SYNTH_TARGET_LAST) \
      << "invalid find synthesis target"

#define CVC5_CAPI_CHECK_OPTION_CATEGORY(cat)                      \
  CVC5_API_CHECK((cat) >= 0 && (cat) < CVC5_OPTION_CATEGORY_LAST) \
      << "invalid option category"

#define CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang)                       \
  CVC5_API_CHECK((lang) >= 0 && (lang) < CVC5_INPUT_LANGUAGE_LAST) \
      << "invalid input language"

#define CVC5_CAPI_CHECK_LEARNED_LIT_TYPE(type)                       \
  CVC5_API_CHECK((type) >= 0 && (type) < CVC5_LEARNED_LIT_TYPE_LAST) \
      << "invalid learned literal type"

#define CVC5_CAPI_CHECK_PROOF_COMPONENT(pc)                     \
  CVC5_API_CHECK((pc) >= 0 && (pc) < CVC5_PROOF_COMPONENT_LAST) \
      << "invalid proof component kind"

#define CVC5_CAPI_CHECK_PROOF_FORMAT(format)                         \
  CVC5_API_CHECK((format) >= 0 && (format) < CVC5_PROOF_FORMAT_LAST) \
      << "invalid proof format"

#define CVC5_CAPI_CHECK_PROOF_RULE(rule)                       \
  CVC5_API_CHECK((rule) >= 0 && (rule) < CVC5_PROOF_RULE_LAST) \
      << "invalid proof rule"

#define CVC5_CAPI_CHECK_PROOF_REWRITE_RULE(rule)                       \
  CVC5_API_CHECK((rule) >= 0 && (rule) < CVC5_PROOF_REWRITE_RULE_LAST) \
      << "invalid proof rewrite rule"

#define CVC5_CAPI_CHECK_SKOLEM_ID(id)                                          \
  CVC5_API_CHECK((id) >= 0 && (id) < CVC5_SKOLEM_ID_LAST) << "invalid skolem " \
                                                             "id"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_SORT(sort) \
  CVC5_API_CHECK(sort != nullptr) << "invalid sort"

#define CVC5_CAPI_CHECK_SORT_AT_IDX(sorts, i) \
  CVC5_API_CHECK(sorts[i] != nullptr) << "invalid sort at index " << i

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_DT_DECL(decl) \
  CVC5_API_CHECK(decl != nullptr) << "invalid datatype declaration"

#define CVC5_CAPI_CHECK_DT_DECL_AT_IDX(decls, i) \
  CVC5_API_CHECK(decls[i] != nullptr)            \
      << "invalid datatype declaration at index " << i

#define CVC5_CAPI_CHECK_DT_CONS_DECL(decl)                           \
  CVC5_API_CHECK(decl != nullptr) << "invalid datatype constructor " \
                                     "declaration"

#define CVC5_CAPI_CHECK_DT_CONS_DECL_AT_IDX(decls, i) \
  CVC5_API_CHECK(decls[i] != nullptr)                 \
      << "invalid datatype constructor declaration at index " << i

#define CVC5_CAPI_CHECK_DT_SEL(sel) \
  CVC5_API_CHECK(sel != nullptr) << "invalid datatype selector"

#define CVC5_CAPI_CHECK_DT_CONS(cons) \
  CVC5_API_CHECK(cons != nullptr) << "invalid datatype constructor"

#define CVC5_CAPI_CHECK_DT(dt) \
  CVC5_API_CHECK(dt != nullptr) << "invalid datatype"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_TERM(term) \
  CVC5_API_CHECK(term != nullptr) << "invalid term"

#define CVC5_CAPI_CHECK_TERM_AT_IDX(terms, i) \
  CVC5_API_CHECK(terms[i] != nullptr) << "invalid term at index " << i

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_OP(op) \
  CVC5_API_CHECK(op != nullptr) << "invalid operator term"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_RESULT(res) \
  CVC5_API_CHECK(res != nullptr) << "invalid result"

#define CVC5_CAPI_CHECK_SYNTH_RESULT(res) \
  CVC5_API_CHECK(res != nullptr) << "invalid synthesis result"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_PROOF(proof) \
  CVC5_API_CHECK(proof != nullptr) << "invalid proof"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_GRAMMAR(grammar) \
  CVC5_API_CHECK(grammar != nullptr) << "invalid grammar"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_STAT(stat) \
  CVC5_API_CHECK(stat != nullptr) << "invalid statistic"

#define CVC5_CAPI_CHECK_STATS(stat) \
  CVC5_API_CHECK(stat != nullptr) << "invalid statistics"

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_CMD(cmd) \
  CVC5_API_CHECK(cmd != nullptr) << "invalid command"

/* -------------------------------------------------------------------------- */
}
