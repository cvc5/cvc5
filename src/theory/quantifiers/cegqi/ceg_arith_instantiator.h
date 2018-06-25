/*********************                                                        */
/*! \file ceg_arith_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_arith_instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H
#define __CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H

#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


/** Arithmetic instantiator
 * 
 * This implements a selection function for arithmetic, which is based on
 * variants of:
 * - Loos/Weispfenning's method (virtual term substitution) for linear real 
 *    arithmetic,
 * - Ferrante/Rackoff's method (interior points) for linear real arithmetic,
 * - Cooper's method for linear arithmetic.
 * For details, see Reynolds et al, "Solving Linear Arithmetic Using 
 * Counterexample-Guided Instantiation", FMSD 2017.
 * 
 * This class contains all necessary information for instantiating a single
 * real or integer typed variable of a single quantified formula.
 */
class ArithInstantiator : public Instantiator {
 public:
  ArithInstantiator( QuantifiersEngine * qe, TypeNode tn );
  virtual ~ArithInstantiator(){}
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  bool hasProcessEquality(CegInstantiator* ci,
                          SolvedForm& sf,
                          Node pv,
                          CegInstEffort effort) override;
  bool processEquality(CegInstantiator* ci,
                       SolvedForm& sf,
                       Node pv,
                       std::vector<TermProperties>& term_props,
                       std::vector<Node>& terms,
                       CegInstEffort effort) override;
  bool hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort) override;
  Node hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           Node lit,
                           CegInstEffort effort) override;
  bool processAssertion(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        Node lit,
                        Node alit,
                        CegInstEffort effort) override;
  bool processAssertions(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         CegInstEffort effort) override;
  bool needsPostProcessInstantiationForVariable(CegInstantiator* ci,
                                                SolvedForm& sf,
                                                Node pv,
                                                CegInstEffort effort) override;
  bool postProcessInstantiationForVariable(CegInstantiator* ci,
                                           SolvedForm& sf,
                                           Node pv,
                                           CegInstEffort effort,
                                           std::vector<Node>& lemmas) override;
  std::string identify() const override { return "Arith"; }
 private:
  /** zero/one */
  Node d_zero;
  Node d_one;
  //--------------------------------------current bounds
  /** Virtual term symbols (vts), where 0: infinity, 1: delta. */
  Node d_vts_sym[2];
  /** Current 0:lower, 1:upper bounds for the variable to instantiate */
  std::vector<Node> d_mbp_bounds[2];
  /** Coefficients for the lower/upper bounds for the variable to instantiate */
  std::vector<Node> d_mbp_coeff[2];
  /** Coefficients for virtual terms for each bound. */
  std::vector<Node> d_mbp_vts_coeff[2][2];
  /** The source literal (explanation) for each bound. */
  std::vector<Node> d_mbp_lit[2];
  //--------------------------------------end current bounds
  /** solve arith 
   * 
   * Given variable to instantiate pv, this isolates the atom into solved form:
   *    veq_c * pv <> val + vts_coeff_delta * delta + vts_coeff_inf * inf
   * where we ensure val has Int type if pv has Int type, and val does not
   * contain vts symbols.
   */
  int solve_arith(CegInstantiator* ci,
                  Node v,
                  Node atom,
                  Node& veq_c,
                  Node& val,
                  Node& vts_coeff_inf,
                  Node& vts_coeff_delta);
  /** get model based projection value 
   * 
   * 
   */
  Node getModelBasedProjectionValue(CegInstantiator* ci,
                                    Node e,
                                    Node t,
                                    bool isLower,
                                    Node c,
                                    Node me,
                                    Node mt,
                                    Node theta,
                                    Node inf_coeff,
                                    Node delta_coeff);
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H */
