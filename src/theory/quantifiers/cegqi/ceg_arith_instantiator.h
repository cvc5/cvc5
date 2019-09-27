/*********************                                                        */
/*! \file ceg_arith_instantiator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief ceg_arith_instantiator
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H
#define CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H

#include <vector>
#include "expr/node.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "theory/quantifiers/cegqi/vts_term_cache.h"

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
class ArithInstantiator : public Instantiator
{
 public:
  ArithInstantiator(TypeNode tn, VtsTermCache* vtc);
  virtual ~ArithInstantiator() {}
  /** reset */
  void reset(CegInstantiator* ci,
             SolvedForm& sf,
             Node pv,
             CegInstEffort effort) override;
  /** this instantiator processes equalities */
  bool hasProcessEquality(CegInstantiator* ci,
                          SolvedForm& sf,
                          Node pv,
                          CegInstEffort effort) override;
  /**
   * Process the equality term[0]=term[1]. If this equality is equivalent to one
   * of the form c * pv = t, then we add the substitution c * pv -> t to sf and
   * recurse.
   */
  bool processEquality(CegInstantiator* ci,
                       SolvedForm& sf,
                       Node pv,
                       std::vector<TermProperties>& term_props,
                       std::vector<Node>& terms,
                       CegInstEffort effort) override;
  /** this instantiator processes assertions */
  bool hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort) override;
  /** this instantiator processes literals lit of kinds EQUAL and GEQ */
  Node hasProcessAssertion(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           Node lit,
                           CegInstEffort effort) override;
  /** process assertion lit
   *
   * If lit can be turned into a bound of the form c * pv <> t, then we store
   * information about this bound (see d_mbp_bounds).
   *
   * If cbqiModel is false (not the default), we recursively try adding the
   * substitution { c * pv -> t } to sf and recursing.
   */
  bool processAssertion(CegInstantiator* ci,
                        SolvedForm& sf,
                        Node pv,
                        Node lit,
                        Node alit,
                        CegInstEffort effort) override;
  /** process assertions
   *
   * This is called after processAssertion has been called on all current bounds
   * for pv. This method selects the "best" bound of those we have seen, which
   * can be one of the following:
   * - Maximal lower bound,
   * - Minimal upper bound,
   * - Midpoint of maximal lower and minimal upper bounds, [if pv is not Int,
   *   and --cbqi-midpoint]
   * - (+-) Infinity, [if no upper (resp. lower) bounds, and --cbqi-use-vts-inf]
   * - Zero, [if no bounds]
   * - Non-optimal bounds. [if the above bounds fail, and --cbqi-nopt]
   */
  bool processAssertions(CegInstantiator* ci,
                         SolvedForm& sf,
                         Node pv,
                         CegInstEffort effort) override;
  /**
   * This instantiator needs to postprocess variables that have substitutions
   * with coefficients, i.e. c*x -> t.
   */
  bool needsPostProcessInstantiationForVariable(CegInstantiator* ci,
                                                SolvedForm& sf,
                                                Node pv,
                                                CegInstEffort effort) override;
  /** post-process instantiation for variable
   *
   * If the solved form for integer variable pv is a substitution with
   * coefficients c*x -> t, this turns its solved form into x -> div(t,c), where
   * div is integer division.
   */
  bool postProcessInstantiationForVariable(CegInstantiator* ci,
                                           SolvedForm& sf,
                                           Node pv,
                                           CegInstEffort effort,
                                           std::vector<Node>& lemmas) override;
  std::string identify() const override { return "Arith"; }

 private:
  /** pointer to the virtual term substitution term cache class */
  VtsTermCache* d_vtc;
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
   *
   * It returns a CegTermType:
   *   CEG_TT_INVALID if it was not possible to put atom into a solved form,
   *   CEG_TT_LOWER if <> in the above equation is >=,
   *   CEG_TT_UPPER if <> in the above equation is <=, or
   *   CEG_TT_EQUAL if <> in the above equation is =.
   */
  CegTermType solve_arith(CegInstantiator* ci,
                          Node v,
                          Node atom,
                          Node& veq_c,
                          Node& val,
                          Node& vts_coeff_inf,
                          Node& vts_coeff_delta);
  /** get model based projection value
   *
   * Given a implied (non-strict) bound:
   *   c*e <=/>= t + inf_coeff*INF + delta_coeff*DELTA
   * this method returns ret, the minimal (resp. maximal) term such that:
   *   c*ret <> t + inf_coeff*INF + delta_coeff*DELTA
   * is satisfied in the current model M, and such that the divisibilty
   * constraint is also satisfied:
   *   ret^M mod c*theta = (c*e)^M mod c*theta
   * where the input theta is a constant (which is assumed to be 1 if null). The
   * values of me and mt are the current model values of e and t respectively.
   *
   * For example, if e has Real type and:
   *   isLower = false, e^M = 0, t^M = 2, inf_coeff = 0, delta_coeff = 2
   * Then, this function returns t+2*delta.
   *
   * For example, if e has Int type and:
   *   isLower = true, e^M = 4, t^M = 2, theta = 3
   * Then, this function returns t+2, noting that (t+2)^M mod 3 = e^M mod 3 = 2.
   *
   * For example, if e has Int type and:
   *   isLower = false, e^M = 1, t^M = 5, theta = 3
   * Then, this function returns t-1, noting that (t-1)^M mod 3 = e^M mod 3 = 1.
   *
   * The value that is added or substracted from t in the return value when e
   * is an integer is the value of "rho" from Figure 6 of Reynolds et al,
   * "Solving Linear Arithmetic Using Counterexample-Guided Instantiation",
   * FMSD 2017.
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__CEG_ARITH_INSTANTIATOR_H */
