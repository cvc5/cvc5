/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per quantified formula in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__QUANT_INFO_H

#include <map>

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {

namespace expr {
class TermCanonize;
}

namespace theory {
namespace quantifiers {

class TermDb;

namespace ccfv {

/**
 * Stores all static information for a quantified formula. Also maintains
 * context-dependent state information for the quantified formula in CCFV
 * search.
 */
class QuantInfo
{
  using NodeBoolPairHashFunction =
      PairHashFunction<Node, bool, std::hash<Node>>;

 public:
  QuantInfo(context::Context* c);
  /**
   * Initialize, called once.
   */
  void initialize(TNode q,
                  TermDb* tdb,
                  eq::EqualityEngine* ee,
                  expr::TermCanonize& tc);
  //-------------------------- static information
  /** Get free variables */
  const std::vector<TNode>& getFreeVariables() const;
  /** Get ordered list of free variables */
  const std::vector<TNode>& getOrderedFreeVariables() const;
  /**
   * Get the constraints, which maps pattern terms to node corresponding to
   * their constraints for making the quantified formula have a propagating
   * instance. For details on the range of constraints, see d_req.
   */
  const std::map<TNode, std::vector<Node>>& getConstraints() const;
  /** Get the constraint terms */
  const std::vector<TNode>& getConstraintTerms() const;
  /** Get congruence terms, the terms to add to the equality engine */
  const std::vector<TNode>& getCongruenceTerms() const;
  /** Get evaluate argument terms */
  const std::vector<TNode>& getEvalArgTerms() const;
  /** Get variable to final terms map */
  const std::map<TNode, std::vector<TNode>>& getVarToFinalTermMap() const;
  //-------------------------- per round
  /**
   * Reset round, called once per full effort check
   */
  void resetRound(TermDb* tdb);
  /** Get next variable. This is used to initialize the search. */
  TNode getNextSearchVariable();
  //-------------------------- queries local to round
  /** get the matcher for variable v */
  TNode getMatcherFor(TNode v) const;
  /** Is alive? */
  bool isActive() const;
  /** set dead */
  void setActive(bool val);
  /** Set no conflict */
  void setNoConflict();
  /** Is maybe conflict */
  bool isMaybeConflict() const;
  //-------------------------- utilities
  /** Do we traverse this node? */
  static bool isTraverseTerm(TNode n);
  /** is c a disequality constraint for p? */
  static bool isDeqConstraint(TNode c, TNode p, TNode& val);
  /** is c a disequality constraint for p? */
  static bool isDeqConstraint(TNode c, TNode p);
  /** Debug print */
  std::string toStringDebug() const;

 private:
  /**
   * Process matching requirement for subterm cur which is a disjunct in the
   * quantified formula of this class.
   */
  void computeMatchReq(TNode cur,
                       eq::EqualityEngine* ee,
                       std::vector<TNode>& visit);
  /** Add match term that must be (dis)equal from eqc */
  void addMatchTermReq(TNode t, Node eqc, bool isEq);
  /** Process match requirement terms */
  void processMatchReqTerms(TermDb* tdb, eq::EqualityEngine* ee);
  /** Register candidate matcher */
  void registerCandidateMatcher(TermDb* tdb, TNode m);
  /** Set matchers */
  TNode getBestMatcherFor(TermDb* tdb,
                          TNode v,
                          std::unordered_set<TNode>& usedMatchers,
                          bool& feasible);
  /**
   * Get minimum matcher, returns the minimal number of current terms in a
   * matchable function in m, or 0 if there are no matching constraints.
   */
  size_t getMinMatchCount(TermDb* tdb, TNode m) const;
  //------------------- static
  /** The quantified formula */
  Node d_quant;
  /** Canonical form of body */
  Node d_canonBody;
  /**
   * List of canonical variables corresponding to each bound variable.
   */
  std::vector<TNode> d_canonVars;
  /**
   * Ordered list of canon variables, ensures that the index of the variables
   * from term canonization is minimal lexiocographically.
   */
  std::vector<TNode> d_canonVarOrdered;
  /**
   * The match terms maped to their requirements. A requirement for p can be:
   * (1) Node::null(), saying that the term must be equal to any ground term
   * (2) (not (= p g)), saying that pattern must be disequal from g
   * (3) g, saying that the pattern must be equal to g
   */
  std::map<TNode, std::vector<Node>> d_req;
  /** The domain of d_req */
  std::vector<TNode> d_reqTerms;
  /**
   * List of all "congruence terms". This is the set of all subterms of the
   * domain of d_req whose kind we are doing congruence over in the equality
   * engine that this class was initialized for.
   */
  std::vector<TNode> d_congTerms;
  /**
   * The maximum variable for each term. For each pattern subterm
   * t, this is the variable that occurs in t that has a maximum index in
   * d_canonVarOrdered.
   *
   * This variable is used for tracking the variable which, when assigned,
   * makes the congruence term fully assigned.
   */
  std::map<TNode, std::vector<TNode>> d_varToFinalTerms;
  /** All matchers for each variable */
  std::map<TNode, std::vector<TNode>> d_candidateMatchers;
  /**
   * Matcher to constraint score
   * 0: no constraints, 2: "some" constraint, 4: disequal, 6: equal +
   * 1 if matching restriction
   */
  std::map<TNode, size_t> d_matcherToCScore;
  /**
   * Matchers to the function symbols they require matching for, e.g.
   * P(f(g(x))) ---> [P, f, g]
   */
  std::map<TNode, std::vector<TNode>> d_matcherToFun;
  /**
   * Subterms of d_req that are direct subterms of a congruence term that
   * are not congruence terms. These will require evaluation + asserting
   * equalities.
   */
  std::vector<TNode> d_evalArgTerms;
  //------------------- initializing search
  /** init variable index */
  size_t d_initVarIndex;
  /**
   * Mapping from free variables to a "matcher" for that variable. These terms
   * determine what to invoke matching on.
   *
   * A matcher for variable v:
   * (1) is a top-level congruence term, i.e. one that occurs as a subterm in
   * the domain of d_req in positions that are not nested under other congruence
   * terms.
   * (2) if t is a matcher for variable v' where v' < v, and t contains v, then
   * t is also the matcher for v. In other words, matchers for earlier
   * variables in the order are used for all variables they bind.
   */
  std::map<TNode, TNode> d_matchers;
  //------------------- within search
  /** is alive, false if we know it is not possible to construct a propagating
   * instance for this quantified formula  */
  context::CDO<bool> d_isActive;
  /**
   * False if a constraint was not entailed; a fully assigned quantified
   * formula with this flag set to flag corresponds to one with a propagating
   * instance.
   */
  context::CDO<bool> d_maybeConflict;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
