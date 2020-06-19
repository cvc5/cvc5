/*********************                                                        */
/*! \file ceg_dt_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_dt_instantiator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H
#define CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H

#include "expr/node.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Datatypes Instantiator
 *
 * This class implements a selection function for datatypes based on solving
 * for occurrences of variables in subfields of datatypes.
 */
class DtInstantiator : public Instantiator
{
 public:
  DtInstantiator(TypeNode tn) : Instantiator(tn) {}
  virtual ~DtInstantiator() {}
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
   * This tries to find an equality eqc[i] = eqc[j] such that pv can be solved
   * for (via solve_dt). If a solved form for pv can be found in this way, we
   * add the substitution for pv to sf and recurse.
   */
  bool processEqualTerms(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         std::vector<Node>& eqc,
                         CegInstEffort effort) override;
  /** this instantiator processes equalities */
  bool hasProcessEquality(CegInstantiator* ci,
                          SolvedForm& sf,
                          Node pv,
                          CegInstEffort effort) override;
  /** process equality
   *
   * This tries to find a solved form for pv based on the equality
   * terms[0] = terms[1] via solve_dt. If a solved form for pv can be found in
   * this way, we add the substitution for pv to sf and recurse.
   */
  bool processEquality(CegInstantiator* ci,
                       SolvedForm& sf,
                       Node pv,
                       std::vector<TermProperties>& term_props,
                       std::vector<Node>& terms,
                       CegInstEffort effort) override;
  /** identify */
  std::string identify() const override { return "Dt"; }

 private:
  /** solve datatype
   *
   * If this method returns a non-null node ret, then v -> ret is a
   * solution for v in the equality a = b and ret does not contain v.
   *
   * For example, if cons( v, nil ) = cons( 5, nil ), this method returns 5.
   * For example, if cons( v, nil ) = L, this method returns head( L ).
   * For example, if cons( v, nil ) = cons( v+1, nil ), this method returns
   * the null node.
   */
  Node solve_dt(Node v, Node a, Node b, Node sa, Node sb);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEG_DT_INSTANTIATOR_H */
