/*********************                                                        */
/*! \file var_match_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief variable match generator class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H
#define CVC4__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace CVC4 {
namespace theory {
namespace inst {

/** match generator for purified terms
 * This handles the special case of invertible terms like x+1 (see
 * Trigger::getTermInversionVariable).
 */
class VarMatchGeneratorTermSubs : public InstMatchGenerator
{
 public:
  VarMatchGeneratorTermSubs(Node var, Node subs);

  /** Reset */
  bool reset(Node eqc, QuantifiersEngine* qe) override;
  /** Get the next match. */
  int getNextMatch(Node q,
                   InstMatch& m,
                   QuantifiersEngine* qe,
                   Trigger* tparent) override;

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
}  // namespace theory
}  // namespace CVC4

#endif
