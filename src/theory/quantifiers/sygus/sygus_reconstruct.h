/*********************                                                        */
/*! \file sygus_reconstruct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for reconstructing terms to match a grammar
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H

#include <map>
#include <vector>

#include "expr/node.h"
#include "expr/sygus_datatype.h"
#include "theory/quantifiers/sygus/rcons_obligation_info.h"
#include "theory/quantifiers/sygus/rcons_type_info.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusReconstruct
 *
 * This class implements an algorithm for reconstructing a given term such that
 * the reconstructed term is equivalent to the original term and its syntax
 * matches a specified grammar.
 *
 * Goal: find a term g in sygus type T that is equivalent to builtin term t.
 *
 * rcons(t, T) : Sol<k_0>
 * {
 *   // a list of triples to reconstruct into Sygus type T, where
 *   // a labeled term is of the form (k, t, s), where k is a skolem of type T,
 *   // t is a builtin term of the type encoded by T, and s is a possibly null
 *   // sygus term of type T representing the solution.
 *   Obs<T>
 *
 *   // We define Term<k> and Sol<k> for each skolem k such that Obs<T> contains
 *   // entries (k, Term<k>, Sol<k>)
 *
 *   CandSols<k> : a list of possible solutions, for each label k. Whenever
 *                 there is a successful match, it's added to this list.
 *   Pool<T> : a list of enumerated terms for each sygus type
 *
 *   let k_0 be a fresh skolem of sygus type T
 *
 *   Obs<T> += {(k_0, t, null)}
 *
 *   Pool<T> = {}
 *
 *   while Sol<k_0> == null
 *     // enumeration phase
 *     for each T
 *       s[z] = nextEnum(T_{z})
 *       if (s[z] is ground)
 *         if exists (k', t', s') in Obs<T> s.t. |=_X t' = toBuiltIn(s[z])
 *           markSolved(k', s[z])
 *         else
 *           let k be a new variable of type : T
 *           Obs<T> += (k, toBuiltIn(s[z]), s[z])
 *       else if no s' in Pool<T> s.t.
 *             rewrite(toBuiltIn(s')) * sigma = rewrite(toBuiltIn(s))
 *           Pool<T> += s[z]
 *           for each (k, t, null) in Obs<T>
 *             Obs' += matchNewObs(k, s[z])
 *     // match phase
 *     while Obs' != {}
 *       Obs'' = {}
 *       for each (k, t, null) in Obs' // s = null for all triples in Obs'
 *         Obs<T> += (k, t, null)
 *         for each s[z] in Pool<T>
 *           Obs'' += matchNewObs(k, s[z])
 *       Obs' = Obs''
 * }
 *
 * matchNewObs(k, s[z]) : Obs'
 * {
 *   u = rewrite(toBuiltIn(s[z]))
 *   if match(u, t) == {toBuiltin(z) -> t'}
 *     if forall t' exists (k'', t'', s'') in Obs<T> s.t. |=_X t'' = t'
 *       markSolved(k, s{z -> s''})
 *     else
 *       let k' be a new variable of type : typeOf(z)
 *       CandSol<k> += s{z -> k'}
 *       Obs'<typeOf(z)> += (k', t', null)
 * }
 *
 * markSolved(k, s)
 * {
 *   if Sol<k> != null
 *     return
 *   if s is not ground
 *     instantiate s with arbitrary sygus datatype values
 *   Sol<k> = s
 *   CandSols<k> += s
 *   S = {k}      // a stack to process
 *   while S != {}
 *     k' = pop(S)
 *     for all k'' in CandSols keys
 *       for all s'[k'] in CandSols<k''>
 *         s'{k' -> Sol<k'>}
 *         if s' contains free variables not in Obs
 *           instantiate s with arbitrary sygus datatype values
 *         if s' is ground
 *           Sol<k''> = s'
 *           push(S, k'')
 * }
 */
class SygusReconstruct : public expr::NotifyMatch
{
 public:
  /**
   * Constructor.
   *
   * @param tds Database for sygus terms
   * @param s Statistics managed for the synth engine
   */
  SygusReconstruct(TermDbSygus* tds, SygusStatistics& s);

  /** reconstruct solution
   *
   * Return (if possible) a sygus encoding of a node that is equivalent to sol
   * and whose syntax matches the grammar corresponding to sygus datatype stn.
   *
   * For example, given:
   *   sol = (* 2 x)
   *   stn = A sygus datatype encoding the grammar
   *           Start -> (c_PLUS Start Start) | c_x | c_0 | c_1
   * This method may return (c_PLUS c_x c_x) and set reconstructed to 1.
   *
   * @param sol The target term
   * @param stn The sygus datatype type encoding the syntax restrictions
   * @param reconstructed The flag to update, set to 1 if we successfully return
   *                      a node, otherwise it is set to -1
   * @param enumLimit A value to limit the effort spent by this class (roughly
   *                  equal to the number of intermediate terms to try)
   * @return The reconstructed sygus term
   */
  Node reconstructSolution(Node sol,
                           TypeNode stn,
                           int& reconstructed,
                           int enumLimit);

 private:
  /** match obligation `k`'s builtin term with pattern `sz`
   *
   * This function matches the builtin term corresponding to the obligation `k`
   * with the pattern `sz`. If the match succeeds, `sz` is added to the set of
   * candidate solutions for `k` and A set of new sub-obligations to satisfy is
   * returned. If there are no sub-obligations are they are all satisfied, then
   * `sz` is considered a solution to obligation `k` and `matchNewObs(k, s)` is
   * called, where `s = s * {z -> sol[z]}`. For example, given:
   *
   * Term = {c_z1 -> (+ 1 1)}
   * CandSols = {}
   * Sol = {}
   *
   * Then calling `matchNewObs(c_z1, (+ c_z2 c_z3))` will result in:
   *
   * Term = {c_z1 -> (+ 1 1), c_z2 -> 1}
   * CandSols = {c_z1 -> {(+ c_z2 c_z2)}, c_z2 -> {}}
   * Sol = {}
   *
   * and will return `{typeOf(c_z2) -> {c_z2}}`.
   *
   * Notice that `c_z3` is replaced by `c_z2` because it has the same
   * corresponding builtin term.
   *
   * @param ob free var whose builtin term we need to match
   * @param sz a pattern to match `ob`s builtin term with
   * @return a set of new obligations to satisfy if the match succeeds
   */
  std::unordered_map<TypeNode,
                     std::unordered_set<Node, NodeHashFunction>,
                     TypeNodeHashFunction>
  matchNewObs(Node ob, Node sz);

  /** mark obligation `k` as solved
   *
   * This function first marks `s` as the complete/constant solution for
   * `ob`. Then it substitutes all instances of `ob` in partial solutions to
   * other obligations with `s`. The function repeats those two steps for each
   * partial solution that gets completed because of the second step. For
   * example, given:
   *
   * CandSols = {
   *  mainOb -> {(+ z1 1)},
   *  z1 -> {(* z2 x)},
   *  z2 -> {2}
   * }
   * Sol = {z2 -> 2}
   *
   * Then calling `markSolved(z2, 2)` will result in:
   *
   * CandSols = {
   *  mainOb -> {(+ z1 1), (+ (* 2 x) 1)},
   *  z1 -> {(* z2 x), (* 2 x)},
   *  z2 -> {2}
   * }
   * Sol = {mainOb -> (+ (* 2 x) 1), z1 -> (* 2 x), z2 -> 2}
   *
   * Note: example uses builtin terms instead of sygus terms for simplicity.
   *
   * @param ob free var to mark as solved and substitute
   * @param sol constant solution to `ob`
   */
  void markSolved(Node k, Node s);

  /**
   * Initialize a sygus enumerator and a candidate rewrite database for each
   * sygus datatype type.
   *
   * @param stn The sygus datatype type encoding the syntax restrictions
   */
  void initialize(TypeNode stn);

  /**
   * Remove solved obligations from `d_unsolvedObs`.
   */
  void removeSolvedObs();

  /**
   * Replace all variables in `n` with ground values of the type.
   *
   * @param n A term containing variables
   * @return `n` with all vars in `n` replaced with ground values
   */
  Node mkGround(Node n) const;

  /**
   * A notification that s is equal to n * { vars -> subs }. This function
   * should return false if we do not wish to be notified of further matches.
   */
  bool notify(Node s,
              Node n,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override;

  /**
   * Reset the state of this SygusReconstruct object.
   */
  void clear();

  /**
   * Return a string representation of an obligation.
   *
   * @param k An obligation
   * @return A string representation of `k`
   */
  std::string ob(Node k) const;

  /**
   * Print all reachable obligations and their candidate solutions from
   * the `root` obligation and its candidate solutions.
   *
   * \note requires enabling "sygus-rcons" trace
   *
   * @param root The root obligation to start from
   */
  void printCandSols(const Node& mainOb) const;

  /**
   * Print the pool of patterns/shape used in the matching phase.
   *
   * \note requires enabling "sygus-rcons" trace
   *
   * @param pool a pool of patterns/shapes to print
   */
  void printPool(const std::unordered_map<TypeNode,
                                          std::vector<Node>,
                                          TypeNodeHashFunction>& pool) const;

  /** pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;

  /** a set of obligations that are not yet satisfied for each sygus datatype */
  std::unordered_map<TypeNode,
                     std::unordered_set<Node, NodeHashFunction>,
                     TypeNodeHashFunction>
      d_unsolvedObs;

  /** a map from an obligation to its reconstruction info */
  std::unordered_map<Node, RConsObligationInfo, NodeHashFunction> d_obInfo;
  /** a map from a sygus datatype type to its reconstruction info */
  std::unordered_map<TypeNode, RConsTypeInfo, TypeNodeHashFunction> d_stnInfo;

  /** a map from an obligation to its sygus solution (if it exists) */
  std::unordered_map<TNode, TNode, TNodeHashFunction> d_sol;

  /** a map from a candidate solution to its sub-obligations */
  std::unordered_map<Node, std::vector<Node>, NodeHashFunction> d_subObs;
  /** a map from a candidate solution to its parent obligation */
  std::unordered_map<Node, Node, NodeHashFunction> d_parentOb;

  /** a cache of sygus variables treated as ground terms by matching */
  std::unordered_map<Node, Node, NodeHashFunction> d_groundVars;

  /** A trie for filtering out redundant terms from the paterns pool */
  expr::MatchTrie d_poolTrie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif  // CVC4__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
