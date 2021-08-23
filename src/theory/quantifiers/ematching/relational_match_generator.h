/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relational match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__RELATIONAL_MATCH_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__RELATIONAL_MATCH_GENERATOR_H

#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace inst {

/** match generator for relational triggers x ~ t
 */
class RelationalMatchGenerator : public InstMatchGenerator
{
 public:
  RelationalMatchGenerator(Trigger* tparent,
                           Node rtrigger,
                           bool hasPol,
                           bool pol);

  /** Reset */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(Node q, InstMatch& m) override;

 private:
  /** the variable */
  Node d_var;
  /** The index of the variable */
  int64_t d_vindex;
  /** the relation kind */
  Kind d_rel;
  /** the right hand side */
  Node d_rhs;
  /** whether we have a required polarity */
  bool d_hasPol;
  /** the required polarity, if it exists */
  bool d_pol;
  /** the current number of terms we have generated since the last call to reset
   */
  size_t d_counter;
  /** stores whether we have written a value for d_var in the current match. */
  bool d_rmPrev;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
