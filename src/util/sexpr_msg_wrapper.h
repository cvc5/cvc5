/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple wrapper to be used in Env::outputMsg(tag) and
 * EnvObj::outputMsg(tag). It forwards any input to the underlying output
 * streams, but wraps the entire message <msg> into the following S-expression:
 *   (message "<msg>" :tag)
 */

#include "cvc5_private.h"

#ifndef CVC5__UTIL__SEXPR_MSG_WRAPPER_H
#define CVC5__UTIL__SEXPR_MSG_WRAPPER_H

#include <iosfwd>

namespace cvc5 {

namespace options {
enum class OutputTag;
}
using OutputTag = options::OutputTag;

/**
 * A simple wrapper for Env::outputMsg(), wrapping any output into an
 * S-expression.
 */
class SExprMsgWrapper
{
 public:
  /** Forwards everything to the underlying output stream. */
  template <typename T>
  SExprMsgWrapper& operator<<(const T& t)
  {
    d_os << t;
    return *this;
  }
  /** Prefix the output with `(message "`. */
  SExprMsgWrapper(std::ostream& os, OutputTag tag);
  /** Suffix the output with `" :tag)`. */
  ~SExprMsgWrapper();

 private:
  /** The underlying output stream. */
  std::ostream& d_os;
  /** The output tag this message is meant for. */
  OutputTag d_tag;
};

}  // namespace cvc5

#endif /* CVC5__UTIL__SEXPR_MSG_WRAPPER_H */
