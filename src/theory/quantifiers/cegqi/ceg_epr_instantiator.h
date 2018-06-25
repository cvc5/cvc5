/*********************                                                        */
/*! \file ceg_epr_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_epr_instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H
#define __CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H

#include <map>
#include <vector>
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TermArgTrie;

/** Effectively Propositional (EPR) Instantiator
 *
 */
class EprInstantiator : public Instantiator
{
 public:
  EprInstantiator(QuantifiersEngine* qe, TypeNode tn) : Instantiator(qe, tn) {}
  virtual ~EprInstantiator() {}
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  bool processEqualTerm(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        TermProperties& pv_prop,
                        Node n,
                        CegInstEffort effort) override;
  bool processEqualTerms(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         std::vector<Node>& eqc,
                         CegInstEffort effort) override;
  /** identify */
  std::string identify() const override { return "Epr"; }
 private:
  std::vector<Node> d_equal_terms;
  void computeMatchScore(CegInstantiator* ci,
                         Node pv,
                         Node catom,
                         std::vector<Node>& arg_reps,
                         TermArgTrie* tat,
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

#endif /* __CVC4__THEORY__QUANTIFIERS__CEG_EPR_INSTANTIATOR_H */
