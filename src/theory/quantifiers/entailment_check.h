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
 * Entailment check class
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ENTAILMENT_CHECK_H
#define CVC5__THEORY__QUANTIFIERS__ENTAILMENT_CHECK_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermDb;

/**
 * Entailment check utility, which determines whether formulas are entailed
 * in the current context. The main focus of this class is on UF formulas.
 * It works by looking at the term argument trie data structures in term
 * database. For details, see e.g. Section 4.1 of Reynolds et al TACAS 2018.
 */
class EntailmentCheck : protected EnvObj
{
 public:
  EntailmentCheck(Env& env, QuantifiersState& qs, TermDb& tdb);
  ~EntailmentCheck();
  /** evaluate term
   *
   * Returns a term n' such that n * subs = n' is entailed based on the current
   * set of equalities, where ( n * subs ) is term n under the substitution
   * subs.
   *
   * This function may generate new terms. In particular, we typically rewrite
   * subterms of n of maximal size (in terms of the AST) to terms that exist
   * in the equality engine.
   *
   * useEntailmentTests is whether to call the theory engine's entailmentTest
   * on literals n for which this call fails to find a term n' that is
   * equivalent to n, for increased precision. This is not frequently used.
   *
   * If reqHasTerm, then we require that the returned term is a Boolean
   * combination of terms that exist in the equality engine used by this call.
   * If no such term is constructable, this call returns null. The motivation
   * for setting this to true is to "fail fast" if we require the return value
   * of this function to only involve existing terms. This is used e.g. in
   * the "propagating instances" portion of conflict-based instantiation
   * (quant_conflict_find.h).
   *
   * @param n The term under consideration
   * @param subs The substitution under consideration
   * @param subsRep Whether the range of subs are representatives in the current
   * equality engine
   * @param useEntailmentTests Whether to use entailment tests to show
   * n * subs is equivalent to true/false.
   * @param reqHasTerm Whether we require the returned term to be a Boolean
   * combination of terms known to the current equality engine
   * @return the term n * subs evaluates to
   */
  Node evaluateTerm(TNode n,
                    std::map<TNode, TNode>& subs,
                    bool subsRep,
                    bool useEntailmentTests = false,
                    bool reqHasTerm = false);
  /** Same as above, without a substitution */
  Node evaluateTerm(TNode n,
                    bool useEntailmentTests = false,
                    bool reqHasTerm = false);
  /** get entailed term
   *
   * If possible, returns a term n' such that:
   * (1) n' exists in the current equality engine (as specified by the state),
   * (2) n = n' is entailed in the current context.
   * It returns null if no such term can be found.
   * Wrt evaluateTerm, this version does not construct new terms, and
   * thus is less aggressive.
   */
  TNode getEntailedTerm(TNode n);
  /** get entailed term
   *
   * If possible, returns a term n' such that:
   * (1) n' exists in the current equality engine (as specified by the state),
   * (2) n * subs = n' is entailed in the current context, where * denotes
   * substitution application.
   * It returns null if no such term can be found.
   * subsRep is whether the substitution maps to terms that are representatives
   * according to the quantifiers state.
   * Wrt evaluateTerm, this version does not construct new terms, and
   * thus is less aggressive.
   */
  TNode getEntailedTerm(TNode n, std::map<TNode, TNode>& subs, bool subsRep);
  /** is entailed
   * Checks whether the current context entails n with polarity pol, based on
   * the equality information in the quantifiers state. Returns true if the
   * entailment can be successfully shown.
   */
  bool isEntailed(TNode n, bool pol);
  /** is entailed
   *
   * Checks whether the current context entails ( n * subs ) with polarity pol,
   * based on the equality information in the quantifiers state,
   * where * denotes substitution application.
   * subsRep is whether the substitution maps to terms that are representatives
   * according to in the quantifiers state.
   */
  bool isEntailed(TNode n,
                  std::map<TNode, TNode>& subs,
                  bool subsRep,
                  bool pol);

 protected:
  /** helper for evaluate term */
  Node evaluateTerm2(TNode n,
                     std::map<TNode, Node>& visited,
                     std::map<TNode, TNode>& subs,
                     bool subsRep,
                     bool useEntailmentTests,
                     bool reqHasTerm);
  /** helper for get entailed term */
  TNode getEntailedTerm2(TNode n, std::map<TNode, TNode>& subs, bool subsRep);
  /** helper for is entailed */
  bool isEntailed2(TNode n,
                   std::map<TNode, TNode>& subs,
                   bool subsRep,
                   bool pol);
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
  /** Reference to the term database */
  TermDb& d_tdb;
  /** boolean terms */
  Node d_true;
  Node d_false;
}; /* class EntailmentCheck */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ENTAILMENT_CHECK_H */
