/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst evaluator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H

#include <vector>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/ieval/state.h"
#include "theory/quantifiers/ieval/term_evaluator.h"
#include "theory/quantifiers/index_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;

namespace ieval {

/**
 * Inst evaluator
 *
 * Incrementally maintains the state of the evaluated form of the quantified
 * formula under a substitution. In other words, substitutions can
 * be added one variable at a time with push, and removed with pop. This
 * class tracks whether the evaluated form of a quantified formula meets
 * a certain criteria based on the term evaluation mode (e.g. is not entailed,
 * is false in model, etc.).
 *
 * To use this class, after construction, you must:
 * - Watch quantified formulas.
 * - Push/pop variable assignments.
 *
 * The main information that is provided by this class is whether the current
 * variable assignment is feasible, which is based on the evaluation mode.
 */
class InstEvaluator : protected EnvObj
{
  using NodeList = context::CDList<Node>;
  using NodeNodeMap = context::CDHashMap<Node, Node>;

 public:
  /** Constructor
   *
   * @param env Reference to the env
   * @param qs Reference to the quantifiers state
   * @param tev The evaluation mode for this inst evaluator
   * @param genLearning If this flag is true, then whenever we discover
   * that the set of quantified formulas watched by this class is infeasible,
   * we learn a generalized substitution from the current one that explains
   * the failure. This is tracked in a data structure, which is subsequently
   * used for fast lookups for future assignments.
   * @param canonize If this flag is true, the bodies of quantified formulas are
   * made canonical. This means that portions of quantified formulas that are
   * alpha-equivalent share information on how they evaluate. This method is
   * recommended if multiple quantified formulas are being watched
   * @param trackAssignedQuant If this flag is true, we calculate when
   * quantified formulas have a complete assignment, for push.
   */
  InstEvaluator(Env& env,
                QuantifiersState& qs,
                TermDb& tdb,
                TermEvaluatorMode tev,
                bool genLearning = false,
                bool canonize = false,
                bool trackAssignedQuant = false);
  /**
   * Set that we are watching quantified formula q. This can only be done if
   * there are no variable assignments yet.
   */
  void watch(Node q);
  /** Same as above, with possibly preprocessed body. */
  void watch(Node q, Node body);
  /**
   * Set that we are considering instantiations v -> s.
   *
   * Return false if all quantified formulas watched by this class are
   * infeasible.
   *
   * If this returns true, this adds quantified formulas that are fully
   * instantiated to assignedQuants if trackAssignedQuant is true.
   */
  bool push(TNode v, TNode s, std::vector<Node>& assignedQuants);
  /** Same as above, without tracking assigned quantifiers */
  bool push(TNode v, TNode s);
  /** pop the last (successful) push */
  void pop();
  /**
   * Reset all variable assignments.
   *
   * If isSoft is true, this saves the state initialization of ground terms,
   * the learned failures, and the watched quantifier information.
   *
   * If isSoft is false, this saves the watched quantifier information only.
   */
  void resetAll(bool isSoft = true);
  /** Get current instantiation for quantified formula q. */
  std::vector<Node> getInstantiationFor(Node q) const;
  /**
   * Is feasible, return true if at least one watched quantified formula is
   * feasible.
   *
   * A quantified formula is feasible if it has not failed the criteria
   * specified by the evaluation mode. For example, if this class was
   * initialized with tev NO_ENTAIL, then the quantified formula is
   * infeasible if all extensions of the current variable assignment
   * lead to instantiations that are entailed by the ground context.
   */
  bool isFeasible() const;

 private:
  /** Set evaluator mode. */
  void setEvaluatorMode(TermEvaluatorMode tev);
  /** Initialize the state, return false if we are infeasible. */
  bool initialize();
  /** Push internal, helper for push methods above */
  bool pushInternal(TNode v, TNode s, std::vector<Node>& assignedQuants);
  /**
   * Learn failure, called immediately after the state is finished. Adds the
   * current assignment to the database.
   */
  void learnFailure();
  /**
   * Check if there is currently a learned failure for the current assignment.
   */
  bool checkLearnedFailure() const;
  /**
   * Get the current list of assigned terms, based on the ordering in
   * d_varList.
   */
  std::vector<Node> getCurrentTerms() const;
  /**
   * Lookup canonical term, return the canonical form of n, assumes that it has
   * been canonized.
   */
  Node lookupCanonicalTerm(TNode n) const;
  /** A context object */
  context::Context d_context;
  /** do generalized learning */
  bool d_genLearning;
  /** do canonize */
  bool d_canonize;
  /** Are we tracking unassigned quantifiers? */
  bool d_trackAssignedQuant;
  /** The state object */
  State d_state;
  /** Variable mapping */
  NodeNodeMap d_varMap;
  /** Term canonizer */
  expr::TermCanonize d_tcanon;
  /** Visited map for the term canonizer */
  std::map<TNode, Node> d_canonVisited;
  /** The list of quantified formulas we are tracking */
  NodeList d_quantList;
  /** The (canonical) variables of the quantified formulas we are tracking */
  NodeList d_varList;
  /** An index trie, if we are using generalized learning */
  std::unique_ptr<IndexTrie> d_itrie;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__IEVAL__INST_EVALUATOR_H */
