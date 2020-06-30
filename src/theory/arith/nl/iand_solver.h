/*********************                                                        */
/*! \file iand_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Solver for integer and (IAND) constraints
 **/

#ifndef CVC4__THEORY__ARITH__NL__IAND_SOLVER_H
#define CVC4__THEORY__ARITH__NL__IAND_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/arith/theory_arith.h"

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

/** Integer and solver class
 *
 */
class IAndSolver
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  IAndSolver(TheoryArith& containing, NlModel& model);
  ~IAndSolver();

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
  /** check initial refine
   *
   * Returns a set of valid theory lemmas, based on simple facts about IAND.
   *
   * Examples where iand is shorthand for (_ iand k):
   *
   * 0 <= iand(x,y) < 2^k
   * iand(x,y) <= x
   * iand(x,y) <= y
   * x=y => iand(x,y)=x
   *
   * This should be a heuristic incomplete check that only introduces a
   * small number of new terms in the lemmas it returns.
   */
  std::vector<NlLemma> checkInitialRefine();
  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  std::vector<NlLemma> checkFullRefine();

  //-------------------------------------------- end lemma schemas
 private:
  // The theory of arithmetic containing this extension.
  TheoryArith& d_containing;
  /** Reference to the non-linear model object */
  NlModel& d_model;
  /** commonly used terms */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_two;
  Node d_true;
  Node d_false;
  /** IAND terms that have been given initial refinement lemmas */
  NodeSet d_initRefine;
  /** all IAND terms, for each bit-width */
  std::map<unsigned, std::vector<Node> > d_iands;

  /**
   * convert integer value to bitvector value of bitwidth k,
   * equivalent to Rewriter::rewrite( ((_ intToBv k) n) ).
   */
  Node convertToBvK(unsigned k, Node n) const;
  /** 2^k */
  Node twoToK(unsigned k) const;
  /** 2^k-1 */
  Node twoToKMinusOne(unsigned k) const;
  /** make iand */
  Node mkIAnd(unsigned k, Node x, Node y) const;
  /** make ior */
  Node mkIOr(unsigned k, Node x, Node y) const;
  /** make inot */
  Node mkINot(unsigned k, Node i) const;
  /** extract from integer
   *  ((_ extract i j) n) is n / 2^j mod 2^{i-j+1}
   */
  Node iextract(unsigned i, unsigned j, Node n) const;
  /**
   * Value-based refinement lemma for i of the form ((_ iand k) x y). Returns:
   *   x = M(x) ^ y = M(y) =>
   *     ((_ iand k) x y) = Rewriter::rewrite(((_ iand k) M(x) M(y)))
   */
  Node valueBasedLemma(Node i);
  /**
   * Sum-based refinement lemma for i of the form ((_ iand k) x y). Returns:
   * i = 2^0*min(x[0],y[0])+...2^{k-1}*min(x[k-1],y[k-1])
   * where x[i] is x div i mod 2
   * and min is defined with an ite.
   */
  Node sumBasedLemma(Node i);
  /** Bitwise refinement lemma for i of the form ((_ iand k) x y). Returns:
   *   x[j1] = y[j1] ^ ... ^ x[jn] = y[jn]
   *   where j1, ..., jn with n < k are the bit indices where M(x) ^ M(y)
   *   does not match M(((_ iand k) x y))
   */
  Node bitwiseLemma(Node i);
}; /* class IAndSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__ARITH__IAND_SOLVER_H */
