/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

/* -------------------------------------------------------------------------- */

#define CVC5_CAPI_CHECK_KIND(kind)                 \
  CVC5_API_CHECK((kind) >= CVC5_KIND_INTERNAL_KIND \
                 && (kind) < CVC5_KIND_LAST_KIND)  \
      << "invalid term kind";

#define CVC5_CAPI_CHECK_SORT_KIND(kind)                      \
  CVC5_API_CHECK((kind) >= CVC5_SORT_KIND_INTERNAL_SORT_KIND \
                 && (kind) < CVC5_SORT_KIND_LAST_SORT_KIND)  \
      << "invalid sort kind";

#define CVC5_CAPI_CHECK_RM(rm) \
  CVC5_API_CHECK((rm) >= 0 && (rm) < CVC5_RM_LAST) << "invalid rounding mode";

#define CVC5_CAPI_CHECK_UNKNOWN_EXPLANATION(e)                    \
  CVC5_API_CHECK((e) >= 0 && (e) < CVC5_UNKNOWN_EXPLANATION_LAST) \
      << "invalid unknown explanation kind";

#define CVC5_CAPI_CHECK_BLOCK_MODELS_MODE(mode)                       \
  CVC5_API_CHECK((mode) >= 0 && (mode) < CVC5_BLOCK_MODELS_MODE_LAST) \
      << "invalid block models mode";

#define CVC5_CAPI_CHECK_FIND_SYNTH_TARGET(target)                         \
  CVC5_API_CHECK((target) >= 0 && (target) < CVC5_FIND_SYNTH_TARGET_LAST) \
      << "invalid find synthesis target";

#define CVC5_CAPI_CHECK_INPUT_LANGUAGE(lang)                       \
  CVC5_API_CHECK((lang) >= 0 && (lang) < CVC5_INPUT_LANGUAGE_LAST) \
      << "invalid input language";

#define CVC5_CAPI_CHECK_LEARNED_LIT_TYPE(type)                       \
  CVC5_API_CHECK((type) >= 0 && (type) < CVC5_LEARNED_LIT_TYPE_LAST) \
      << "invalid learned literal type";

#define CVC5_CAPI_CHECK_PROOF_COMPONENT(pc)                     \
  CVC5_API_CHECK((pc) >= 0 && (pc) < CVC5_PROOF_COMPONENT_LAST) \
      << "invalid proof component kind";

#define CVC5_CAPI_CHECK_PROOF_FORMAT(format)                         \
  CVC5_API_CHECK((format) >= 0 && (format) < CVC5_PROOF_FORMAT_LAST) \
      << "invalid proof format";

/* -------------------------------------------------------------------------- */
}
