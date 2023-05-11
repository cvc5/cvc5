/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_unif
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/sygus/sygus_unif_strat.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/** Sygus unification utility
 *
 * This utility implements synthesis-by-unification style approaches for a
 * set of functions-to-synthesize. These approaches include a combination of:
 * (1) Decision tree learning, inspired by Alur et al TACAS 2017,
 * (2) Divide-and-conquer via string concatenation.
 *
 * This class maintains, for each function-to-synthesize f:
 * (1) A "strategy tree" based on the syntactic restrictions for f that is
 * constructed during initialize (d_strategy),
 *
 * Based on the above, solutions can be constructed via calls to
 * constructSolution.
 */
class SygusUnif : protected EnvObj
{
 public:
  SygusUnif(Env& env);
  virtual ~SygusUnif();

  /** initialize candidate
   *
   * This initializes this class with functions-to-synthesize f. We also call
   * this a "candidate variable". This function can be called more than once
   * for different functions-to-synthesize in the same conjecture.
   *
   * This call constructs a set of enumerators for the relevant subfields of
   * the grammar of f and adds them to enums. These enumerators are those that
   * should be later given to calls to notifyEnumeration below.
   *
   * This also may result in lemmas being added to strategy_lemmas,
   * which correspond to static symmetry breaking predicates (for example,
   * those that exclude ITE from enumerators whose role is enum_io when the
   * strategy is ITE_strat). The lemmas are associated with a strategy point of
   * the respective function-to-synthesize.
   */
  virtual void initializeCandidate(
      TermDbSygus* tds,
      Node f,
      std::vector<Node>& enums,
      std::map<Node, std::vector<Node>>& strategy_lemmas);

  /**
   * Notify that the value v has been enumerated for enumerator e. This call
   * will add lemmas L to lemmas such that L entails e^M != v for all future
   * models M.
   */
  virtual void notifyEnumeration(Node e, Node v, std::vector<Node>& lemmas) = 0;
  /** construct solution
   *
   * This attempts to construct a solution for each function-to-synthesize
   * based on the current set of enumerated values. Returns null if it cannot
   * for some function (for example, if the set of enumerated values is
   * insufficient, or if a non-deterministic strategy aborts).
   *
   * This call may add lemmas to lemmas that should be sent out on an output
   * channel by the caller.
   */
  virtual bool constructSolution(std::vector<Node>& sols,
                                 std::vector<Node>& lemmas) = 0;

 protected:
  /** Pointer to the term database sygus */
  TermDbSygus* d_tds;

  //-----------------------debug printing
  /** print ind indentations on trace c */
  static void indent(const char* c, int ind);
  /** print (pol ? vals : !vals) as a bit-string on trace c  */
  static void print_val(const char* c,
                        std::vector<Node>& vals,
                        bool pol = true);
  //-----------------------end debug printing
  /** the candidates for this class */
  std::vector<Node> d_candidates;
  /** maps a function-to-synthesize to the above information */
  std::map<Node, SygusUnifStrategy> d_strategy;

  /** domain-specific enumerator exclusion techniques
   *
   * Returns true if the value v for e can be excluded based on a
   * domain-specific exclusion technique like the ones below.
   *
   * results : the values of v under the input examples,
   * exp : if this function returns true, then exp contains a (possibly
   * generalize) explanation for why v can be excluded.
   */
  bool getExplanationForEnumeratorExclude(Node e,
                                          Node v,
                                          std::vector<Node>& results,
                                          std::vector<Node>& exp);
  /** returns true if we can exlude values of e based on negative str.contains
   *
   * Values v for e may be excluded if we realize that the value of v under the
   * substitution for some input example will never be contained in some output
   * example. For details on this technique, see NegContainsSygusInvarianceTest
   * in sygus_invariance.h.
   *
   * This function depends on whether e is being used to enumerate values
   * for any node that is conditional in the strategy graph. For example,
   * nodes that are children of ITE strategy nodes are conditional. If any node
   * is conditional, then this function returns false.
   */
  bool useStrContainsEnumeratorExclude(Node e);
  /** cache for the above function */
  std::map<Node, bool> d_use_str_contains_eexc;

  //------------------------------ constructing solutions
  /** implementation-dependent initialize construct solution
   *
   * Called once before each attempt to construct solutions.
   */
  virtual void initializeConstructSol() = 0;
  /** implementation-dependent initialize construct solution
   *
   * Called once before each attempt to construct solution for a
   * function-to-synthesize f.
   */
  virtual void initializeConstructSolFor(Node f) = 0;
  /** implementation-dependent function for construct solution.
   *
   * Construct a solution based on enumerator e for function-to-synthesize of
   * this class with node role nrole in context x.
   *
   * ind is the term depth of the context (for debugging).
   */
  virtual Node constructSol(
      Node f, Node e, NodeRole nrole, int ind, std::vector<Node>& lemmas) = 0;
  /**
   * Heuristically choose the best solved term for enumerator e,
   * currently return the first by default. A solved term is one that
   * suffices to form part of the solution for the given context. For example,
   * x is a solved term in the context "ite(x>0, _, 0)" for PBE problem
   * with I/O pairs { 1 -> 1, 4 -> 4, -1 -> 0 }.
   */
  virtual Node constructBestSolvedTerm(Node e, const std::vector<Node>& solved);
  /**
   * Heuristically choose the best conditional term from conds for condition
   * enumerator ce, random by default.
   */
  virtual Node constructBestConditional(Node ce,
                                        const std::vector<Node>& conds);
  /** Heuristically choose the best string to concatenate from strs to the
  * solution in context x, currently random
  * incr stores the vector of indices that are incremented by this solution in
  * example outputs.
  * total_inc[x] is the sum of incr[x] for each x in strs.
  */
  virtual Node constructBestStringToConcat(
      const std::vector<Node>& strs,
      const std::map<Node, size_t>& total_inc,
      const std::map<Node, std::vector<size_t>>& incr);
  //------------------------------ end constructing solutions
  /** map terms to their sygus size */
  std::map<Node, unsigned> d_termToSize;
  /**
   * Whether to ensure terms selected by the above methods lead to minimal
   * solutions.
   */
  bool d_enableMinimality;
  /** returns the term whose sygus size is minimal among those in terms */
  Node getMinimalTerm(const std::vector<Node>& terms);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_H */
