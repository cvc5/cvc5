/*********************                                                        */
/*! \file nonlinear_extension.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Extensions for incomplete handling of nonlinear multiplication.
 **
 ** Extensions to the theory of arithmetic incomplete handling of nonlinear
 ** multiplication via axiom instantiations.
 **/

#ifndef CVC4__THEORY__ARITH__NL__NONLINEAR_EXTENSION_H
#define CVC4__THEORY__ARITH__NL__NONLINEAR_EXTENSION_H

#include <stdint.h>
#include <map>
#include <vector>

#include "context/cdlist.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/nl/iand_solver.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/nl_solver.h"
#include "theory/arith/nl/transcendental_solver.h"
#include "theory/arith/theory_arith.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/** Non-linear extension class
 *
 * This class implements model-based refinement schemes
 * for non-linear arithmetic, described in:
 *
 * - "Invariant Checking of NRA Transition Systems
 * via Incremental Reduction to LRA with EUF" by
 * Cimatti et al., TACAS 2017.
 *
 * - Section 5 of "Desiging Theory Solvers with
 * Extensions" by Reynolds et al., FroCoS 2017.
 *
 * - "Satisfiability Modulo Transcendental
 * Functions via Incremental Linearization" by Cimatti
 * et al., CADE 2017.
 *
 * It's main functionality is a check(...) method,
 * which is called by TheoryArithPrivate either:
 * (1) at full effort with no conflicts or lemmas emitted, or
 * (2) at last call effort.
 * In this method, this class calls d_out->lemma(...)
 * for valid arithmetic theory lemmas, based on the current set of assertions,
 * where d_out is the output channel of TheoryArith.
 */
class NonlinearExtension
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  NonlinearExtension(TheoryArith& containing, eq::EqualityEngine* ee);
  ~NonlinearExtension();
  /** Get current substitution
   *
   * This function and the one below are
   * used for context-dependent
   * simplification, see Section 3.1 of
   * "Designing Theory Solvers with Extensions"
   * by Reynolds et al. FroCoS 2017.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * vars : a set of arithmetic variables.
   *
   * This function populates subs and exp, such that for 0 <= i < vars.size():
   *   ( exp[vars[i]] ) => vars[i] = subs[i]
   * where exp[vars[i]] is a set of assertions
   * that hold in the current context. We call { vars -> subs } a "derivable
   * substituion" (see Reynolds et al. FroCoS 2017).
   */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node>>& exp);
  /** Is the term n in reduced form?
   *
   * Used for context-dependent simplification.
   *
   * effort : an identifier indicating the stage where
   *          we are performing context-dependent simplification,
   * on : the original term that we reduced to n,
   * exp : an explanation such that ( exp => on = n ).
   *
   * We return a pair ( b, exp' ) such that
   *   if b is true, then:
   *     n is in reduced form
   *     if exp' is non-null, then ( exp' => on = n )
   * The second part of the pair is used for constructing
   * minimal explanations for context-dependent simplifications.
   */
  std::pair<bool, Node> isExtfReduced(int effort,
                                      Node n,
                                      Node on,
                                      const std::vector<Node>& exp) const;
  /** Check at effort level e.
   *
   * This call may result in (possibly multiple) calls to d_out->lemma(...)
   * where d_out is the output channel of TheoryArith.
   *
   * If e is FULL, then we add lemmas based on context-depedent
   * simplification (see Reynolds et al FroCoS 2017).
   *
   * If e is LAST_CALL, we add lemmas based on model-based refinement
   * (see additionally Cimatti et al., TACAS 2017). The lemmas added at this
   * effort may be computed during a call to interceptModel as described below.
   */
  void check(Theory::Effort e);
  /** intercept model
   *
   * This method is called during TheoryArith::collectModelInfo, which is
   * invoked after the linear arithmetic solver passes a full effort check
   * with no lemmas.
   *
   * The argument arithModel is a map of the form { v1 -> c1, ..., vn -> cn }
   * which represents the linear arithmetic theory solver's contribution to the
   * current candidate model. That is, its collectModelInfo method is requesting
   * that equalities v1 = c1, ..., vn = cn be added to the current model, where
   * v1, ..., vn are arithmetic variables and c1, ..., cn are constants. Notice
   * arithmetic variables may be real-valued terms belonging to other theories,
   * or abstractions of applications of multiplication (kind NONLINEAR_MULT).
   *
   * This method requests that the non-linear solver inspect this model and
   * do any number of the following:
   * (1) Construct lemmas based on a model-based refinement procedure inspired
   * by Cimatti et al., TACAS 2017.,
   * (2) In the case that the nonlinear solver finds that the current
   * constraints are satisfiable, it may "repair" the values in the argument
   * arithModel so that it satisfies certain nonlinear constraints. This may
   * involve e.g. solving for variables in nonlinear equations.
   *
   * Notice that in the former case, the lemmas it constructs are not sent out
   * immediately. Instead, they are put in temporary vector d_cmiLemmas, which
   * are then sent out (if necessary) when a last call
   * effort check is issued to this class.
   */
  void interceptModel(std::map<Node, Node>& arithModel);
  /** Does this class need a call to check(...) at last call effort? */
  bool needsCheckLastEffort() const { return d_needsLastCall; }
  /** presolve
   *
   * This function is called during TheoryArith's presolve command.
   * In this function, we send lemmas we accumulated during preprocessing,
   * for instance, definitional lemmas from expandDefinitions are sent out
   * on the output channel of TheoryArith in this function.
   */
  void presolve();

 private:
  /** Model-based refinement
   *
   * This is the main entry point of this class for generating lemmas on the
   * output channel of the theory of arithmetic.
   *
   * It is currently run at last call effort. It applies lemma schemas
   * described in Reynolds et al. FroCoS 2017 that are based on ruling out
   * the current candidate model.
   *
   * This function returns true if a lemma was added to the vector lems.
   * Otherwise, it returns false. In the latter case, the model object d_model
   * may have information regarding how to construct a model, in the case that
   * we determined the problem is satisfiable.
   */
  bool modelBasedRefinement(std::vector<NlLemma>& mlems);

  /** check last call
   *
   * Check assertions for consistency in the effort LAST_CALL with a subset of
   * the assertions, false_asserts, that evaluate to false in the current model.
   *
   * xts : the list of (non-reduced) extended terms in the current context.
   *
   * This method adds lemmas to arguments lems and wlems, each of
   * which are intended to be sent out on the output channel of TheoryArith
   * under certain conditions.
   *
   * If the set lems is non-empty, then no further processing is
   * necessary. The last call effort check should terminate and these
   * lemmas should be sent.
   *
   * The "waiting" lemmas wlems contain lemmas that should be sent on the
   * output channel as a last resort. In other words, only if we are not
   * able to establish SAT via a call to checkModel(...) should wlems be
   * considered. This set typically contains tangent plane lemmas.
   */
  int checkLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts,
                    std::vector<NlLemma>& lems,
                    std::vector<NlLemma>& wlems);

  /** get assertions
   *
   * Let M be the set of assertions known by THEORY_ARITH. This function adds a
   * set of literals M' to assertions such that M' and M are equivalent.
   *
   * Examples of how M' differs with M:
   * (1) M' may not include t < c (in M) if t < c' is in M' for c' < c, where
   * c and c' are constants,
   * (2) M' may contain t = c if both t >= c and t <= c are in M.
   */
  void getAssertions(std::vector<Node>& assertions);
  /** check model
   *
   * Returns the subset of assertions whose concrete values we cannot show are
   * true in the current model. Notice that we typically cannot compute concrete
   * values for assertions involving transcendental functions. Any assertion
   * whose model value cannot be computed is included in the return value of
   * this function.
   */
  std::vector<Node> checkModelEval(const std::vector<Node>& assertions);

  //---------------------------check model
  /** Check model
   *
   * Checks the current model based on solving for equalities, and using error
   * bounds on the Taylor approximation.
   *
   * If this function returns true, then all assertions in the input argument
   * "assertions" are satisfied for all interpretations of variables within
   * their computed bounds (as stored in d_check_model_bounds).
   *
   * For details, see Section 3 of Cimatti et al CADE 2017 under the heading
   * "Detecting Satisfiable Formulas".
   *
   * The arguments lemmas and gs store the lemmas and guard literals to be sent
   * out on the output channel of TheoryArith as lemmas and calls to
   * ensureLiteral respectively.
   */
  bool checkModel(const std::vector<Node>& assertions,
                  const std::vector<Node>& false_asserts,
                  std::vector<NlLemma>& lemmas,
                  std::vector<Node>& gs);
  //---------------------------end check model

  /** Is n entailed with polarity pol in the current context? */
  bool isEntailed(Node n, bool pol);

  /**
   * Potentially adds lemmas to the set out and clears lemmas. Returns
   * the number of lemmas added to out. We do not add lemmas that have already
   * been sent on the output channel of TheoryArith.
   */
  unsigned filterLemmas(std::vector<NlLemma>& lemmas,
                        std::vector<NlLemma>& out);
  /** singleton version of above */
  unsigned filterLemma(NlLemma lem, std::vector<NlLemma>& out);

  /**
   * Send lemmas in out on the output channel of theory of arithmetic.
   */
  void sendLemmas(const std::vector<NlLemma>& out);
  /** Process side effect se */
  void processSideEffect(const NlLemma& se);

  /** cache of all lemmas sent on the output channel (user-context-dependent) */
  NodeSet d_lemmas;
  /** Same as above, for preprocessed lemmas */
  NodeSet d_lemmasPp;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_true;
  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;
  // pointer to used equality engine
  eq::EqualityEngine* d_ee;
  // needs last call effort
  bool d_needsLastCall;
  /** The non-linear model object
   *
   * This class is responsible for computing model values for arithmetic terms
   * and for establishing when we are able to answer "SAT".
   */
  NlModel d_model;
  /** The transcendental extension object
   *
   * This is the subsolver responsible for running the procedure for
   * transcendental functions.
   */
  TranscendentalSolver d_trSlv;
  /** The nonlinear extension object
   *
   * This is the subsolver responsible for running the procedure for
   * constraints involving nonlinear mulitplication, Cimatti et al., TACAS 2017.
   */
  NlSolver d_nlSlv;
  /** The integer and solver
   *
   * This is the subsolver responsible for running the procedure for
   * constraints involving integer and.
   */
  IAndSolver d_iandSlv;
  /**
   * The lemmas we computed during collectModelInfo, to be sent out on the
   * output channel of TheoryArith.
   */
  std::vector<NlLemma> d_cmiLemmas;
  /**
   * The approximations computed during collectModelInfo. For details, see
   * NlModel::getModelValueRepair.
   */
  std::map<Node, std::pair<Node, Node>> d_approximations;
  /** have we successfully built the model in this SAT context? */
  context::CDO<bool> d_builtModel;
}; /* class NonlinearExtension */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NONLINEAR_EXTENSION_H */
