/*********************                                                        */
/*! \file nl_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Solver for standard non-linear constraints
 **/

#ifndef CVC4__THEORY__ARITH__NL_SOLVER_H
#define CVC4__THEORY__ARITH__NL_SOLVER_H

#include <map>
#include <unordered_map>
#include <utility>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdinsert_hashmap.h"
#include "context/cdlist.h"
#include "context/cdqueue.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl/shared_check_data.h"
#include "theory/arith/nl/nl_constraint.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/nl/nl_monomial.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

typedef std::map<Node, unsigned> NodeMultiset;

/** Non-linear solver class
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
 */
class NlSolver
{
  typedef std::map<Node, NodeMultiset> MonomialExponentMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  NlSolver(InferenceManager& im,
           ArithState& astate,
           NlModel& model,
           SharedCheckData* data);
  ~NlSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);
  //-------------------------------------------- lemma schemas

  //-------------------------------------------- end lemma schemas
 private:
  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  SharedCheckData* d_data;
  /** commonly used terms */
  Node d_zero;
  Node d_true;
  Node d_false;
}; /* class NlSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__NL_SOLVER_H */
