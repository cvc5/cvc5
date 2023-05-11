/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Variable match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H

#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** match generator for purified terms
 * This handles the special case of invertible terms like x+1 (see
 * Trigger::getTermInversionVariable).
 */
class VarMatchGeneratorTermSubs : public InstMatchGenerator
{
 public:
  VarMatchGeneratorTermSubs(Env& env, Trigger* tparent, Node var, Node subs);

  /** Reset */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;

 private:
  /** variable we are matching (x in the example x+1). */
  Node d_var;
  /** cache of d_var.getType() */
  TypeNode d_var_type;
  /** The substitution for what we match (x-1 in the example x+1). */
  Node d_subs;
  /** stores whether we have written a value for d_var in the current match. */
  bool d_rm_prev;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
