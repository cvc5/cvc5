/*********************                                                        */
/*! \file regexp_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Regular expression solver for the theory of strings.
 **
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__REGEXP_SOLVER_H
#define CVC4__THEORY__STRINGS__REGEXP_SOLVER_H

#include <map>
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/skolem_cache.h"
#include "theory/strings/regexp_operation.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/solver_state.h"
#include "util/string.h"

namespace CVC4 {
namespace theory {
namespace strings {

class RegExpSolver
{
  typedef context::CDList<Node> NodeList;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, unsigned, NodeHashFunction> NodeUIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;

 public:
  RegExpSolver(SolverState& s,
               InferenceManager& im,
               SkolemCache* skc,
               CoreSolver& cs,
               ExtfSolver& es,
               SequencesStatistics& stats);
  ~RegExpSolver() {}

  /** check regular expression memberships
   *
   * This checks the satisfiability of all regular expression memberships
   * of the form (not) s in R. We use various heuristic techniques based on
   * unrolling, combined with techniques from Liang et al, "A Decision Procedure
   * for Regular Membership and Length Constraints over Unbounded Strings",
   * FroCoS 2015.
   */
  void checkMemberships();

 private:
  /** check
   *
   * Tells this solver to check whether the regular expressions in mems
   * are consistent. If they are not, then this class will call the
   * sendInference method of its parent TheoryString object, indicating that
   * it requires a conflict or lemma to be processed.
   *
   * The argument mems maps representative string terms r to memberships of the
   * form (t in R) or ~(t in R), where t = r currently holds in the equality
   * engine of the theory of strings.
   */
  void check(const std::map<Node, std::vector<Node>>& mems);
  /**
   * Check memberships in equivalence class for regular expression
   * inclusion.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains str.in.re(xi, Ri) and ~str.in.re(xj, Rj) and Rj includes Ri.
   *
   * @param mems Vector of memberships of the form: (~)str.in.re(x1, R1)
   *             ... (~)str.in.re(xn, Rn) where x1 = ... = xn in the
   *             current context. The function removes elements from this
   *             vector that were marked as reduced.
   * @param expForRe Additional explanations for regular expressions.
   * @return False if a conflict was detected, true otherwise
   */
  bool checkEqcInclusion(std::vector<Node>& mems);

  /**
   * Check memberships for equivalence class.
   * The vector mems is a vector of memberships of the form:
   *   (~) (x1 in R1 ) ... (~) (xn in Rn)
   * where x1 = ... = xn in the current context.
   *
   * This method may add lemmas or conflicts via the inference manager.
   *
   * This method returns false if it discovered a conflict for this set of
   * assertions, and true otherwise. It discovers a conflict e.g. if mems
   * contains (xi in Ri) and (xj in Rj) and intersect(xi,xj) is empty.
   */
  bool checkEqcIntersect(const std::vector<Node>& mems);
  // Constants
  Node d_emptyString;
  Node d_emptyRegexp;
  Node d_true;
  Node d_false;
  /** The solver state of the parent of this object */
  SolverState& d_state;
  /** the output channel of the parent of this object */
  InferenceManager& d_im;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** reference to the extended function solver of the parent */
  ExtfSolver& d_esolver;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  // check membership constraints
  Node mkAnd(Node c1, Node c2);
  /**
   * Check partial derivative
   *
   * Returns false if a lemma pertaining to checking the partial derivative
   * of x in r was added. In this case, addedLemma is updated to true.
   *
   * The argument atom is the assertion that explains x in r, which is the
   * normalized form of atom that may be modified using a substitution whose
   * explanation is nf_exp.
   */
  bool checkPDerivative(
      Node x, Node r, Node atom, bool& addedLemma, std::vector<Node>& nf_exp);
  Node getMembership(Node n, bool isPos, unsigned i);
  unsigned getNumMemberships(Node n, bool isPos);
  CVC4::String getHeadConst(Node x);
  bool deriveRegExp(Node x, Node r, Node atom, std::vector<Node>& ant);
  Node getNormalSymRegExp(Node r, std::vector<Node>& nf_exp);
  // regular expression memberships
  NodeSet d_regexp_ucached;
  NodeSet d_regexp_ccached;
  // semi normal forms for symbolic expression
  std::map<Node, Node> d_nf_regexps;
  std::map<Node, std::vector<Node> > d_nf_regexps_exp;
  // processed memberships
  NodeSet d_processed_memberships;
  /** regular expression operation module */
  RegExpOpr d_regexp_opr;
}; /* class TheoryStrings */

}  // namespace strings
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__THEORY_STRINGS_H */
