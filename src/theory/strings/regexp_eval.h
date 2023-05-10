/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for regular expression membership.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__REGEXP_EVAL_H
#define CVC5__THEORY__STRINGS__REGEXP_EVAL_H

#include "expr/node.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/**
 * Evaluation of regular expressions via compilation to NFA. This class
 * handles only a class of regular expressions that do not contain
 * intersections or complements.
 *
 * For details, see https://swtch.com/~rsc/regexp/regexp1.html.
 */
class RegExpEval
{
 public:
  /**
   * Checks whether it is possible to evaluate regular expression r via
   * a simple compilation to NFA. This is the case if r contains only
   * re.*, re.++, re.union, re.allchar, and constant re.range and str.to_re.
   */
  static bool canEvaluate(const Node& r);
  /**
   * Return true if string s is in r, where r can be evaluated via compilation
   * to NFA.
   *
   * This constructs an NFA for r whose states are roughly equivalent to the
   * number of subterms of r. It evaluates whether s is in r, which is a
   * linear scan through s while tracking the (set of) states in the NFA.
   *
   * Note that the NFA construction is not cached. Moreover, for this reason we
   * do not compile the NFA to a DFA, which would lead to faster evaluation if
   * testing many strings in the same regular expression.
   */
  static bool evaluate(String& s, const Node& r);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__REWRITES_H */
