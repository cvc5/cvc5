/*********************                                                        */
/*! \file ceg_epr_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_epr_instantiator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H
#define CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H

#include <map>
#include <vector>
#include "expr/node_trie.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Effectively Propositional (EPR) Instantiator
 *
 * This implements a selection function for the EPR fragment.
 */
class EprInstantiator : public Instantiator
{
 public:
  EprInstantiator(TypeNode tn) : Instantiator(tn) {}
  virtual ~EprInstantiator() {}
  /** reset */
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  /** this instantiator implements hasProcessEqualTerm */
  bool hasProcessEqualTerm(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort) override;
  /** process equal terms
   *
   * This adds n to the set of equal terms d_equal_terms if matching heuristics
   * are enabled (--quant-epr-match), or simply tries the substitution pv -> n
   * otherwise.
   */
  bool processEqualTerm(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        TermProperties& pv_prop,
                        Node n,
                        CegInstEffort effort) override;
  /** process equal terms
   *
   * Called when pv is equal to the set eqc. If matching heuristics are enabled,
   * this adds the substitution pv -> n based on the best term n in eqc.
   */
  bool processEqualTerms(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         std::vector<Node>& eqc,
                         CegInstEffort effort) override;
  /** identify */
  std::string identify() const override { return "Epr"; }

 private:
  /**
   * The current set of terms that are equal to the variable-to-instantate of
   * this class.
   */
  std::vector<Node> d_equal_terms;
  /** compute match score
   *
   * This method computes the map match_score, from ground term t to the
   * number of times that occur in simple matches for a quantified formula.
   * For example, for quantified formula forall xy. P( x ) V Q( x, y ) and
   * ground terms { P( a ), Q( a, a ), Q( b, c ), Q( a, c ) }, we compute for x:
   *   match_score[a] = 3,
   *   match_score[b] = 1,
   *   match_score[c] = 0.
   * The higher the match score for a term, the more likely this class is to use
   * t in instantiations.
   */
  void computeMatchScore(CegInstantiator* ci,
                         Node pv,
                         Node catom,
                         std::vector<Node>& arg_reps,
                         TNodeTrie* tat,
                         unsigned index,
                         std::map<Node, int>& match_score);
  void computeMatchScore(CegInstantiator* ci,
                         Node pv,
                         Node catom,
                         Node eqc,
                         std::map<Node, int>& match_score);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H */
