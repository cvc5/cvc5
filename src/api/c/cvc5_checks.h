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

/* -------------------------------------------------------------------------- */
}
