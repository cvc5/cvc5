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
 * Relational match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__RELATIONAL_MATCH_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__RELATIONAL_MATCH_GENERATOR_H

#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/**
 * Match generator for relational triggers x ~ t where t is a ground term.
 * This match generator tries a small fixed set of terms based on the kind of
 * relation and the required polarity of the trigger in the quantified formula.
 *
 * For example, for quantified formula (forall ((x Int)) (=> (> x n) (P x))),
 * we have that (> x n) is a relational trigger with required polarity "true".
 * This generator will try the match `x -> n+1` only, where notice that n+1 is
 * the canonical term chosen to satisfy x>n. Canonical terms for arithmetic
 * relations (~ x n) are in set { n, n+1, n-1 }.
 *
 * If a relational trigger does not have a required polarity, then up to 2
 * terms are tried, a term that satisfies the relation, and one that does not.
 * If (>= x n) is a relational trigger with no polarity, then `x -> n` and
 * `x -> n-1` will be generated.
 *
 * Currently this class handles only equality between real or integer valued
 * terms, or inequalities (kind GEQ). It furthermore only considers ground terms
 * t for the right hand side of relations.
 */
class RelationalMatchGenerator : public InstMatchGenerator
{
 public:
  /**
   * @param tparent The parent trigger that this match generator belongs to
   * @param rtrigger The relational trigger
   * @param hasPol Whether the trigger has an entailed polarity
   * @param pol The entailed polarity of the relational trigger.
   */
  RelationalMatchGenerator(
      Env& env, Trigger* tparent, Node rtrigger, bool hasPol, bool pol);

  /** Reset */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;

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
  /**
   * The current number of terms we have generated since the last call to reset
   */
  size_t d_counter;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
