/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

class Cvc5CApiAbortStream
{
 public:
  Cvc5CApiAbortStream(const std::string& msg_prefix)
  {
    stream() << msg_prefix << " ";
  }
  ~Cvc5CApiAbortStream()
  {
    std::cerr << d_stream.str() << std::endl;
    exit(EXIT_FAILURE);
  }
  std::ostream& stream() { return d_stream; }

 private:
  void flush()
  {
    stream() << std::endl;
    stream().flush();
  }
  std::stringstream d_stream;
};

#define CVC5_CAPI_ABORT           \
  cvc5::internal::OstreamVoider() \
      & cvc5::Cvc5CApiAbortStream("cvc5: error:").stream()

#define CVC5_CAPI_TRY_CATCH_BEGIN \
  try                             \
  {
#define CVC5_CAPI_TRY_CATCH_END \
  }                             \
  catch (cvc5::CVC5ApiException & e) { CVC5_CAPI_ABORT << e.getMessage(); }

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
