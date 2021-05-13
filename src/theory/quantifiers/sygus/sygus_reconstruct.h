/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for reconstructing terms to match a grammar.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H

#include <map>
#include <vector>

#include "theory/quantifiers/sygus/rcons_obligation_info.h"
#include "theory/quantifiers/sygus/rcons_type_info.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

using ObligationSet = std::unordered_set<Node>;
using TypeObligationSetMap = std::unordered_map<TypeNode, ObligationSet>;

/** SygusReconstruct
 *
 * This class implements an algorithm for reconstructing a given term such that
 * the reconstructed term is equivalent to the original term and its syntax
 * matches a specified grammar.
 *
 * Goal: find a term g in sygus type T_0 that is equivalent to builtin term t_0.
 *
 * rcons(t_0, T_0) returns g
 * {
 *   Obs: A map from sygus types T to a set of triples to reconstruct into T,
 *        where each triple is of the form (k, ts, s), where k is a skolem of
 *        type T, ts is a set of builtin terms of the type encoded by T, and s
 *        is a possibly null sygus term of type T representing the solution.
 *
 *   Sol: A map from skolems k to solutions s in the triples (k, ts, s). That
 *        is, Sol[k] = s.
 *
 *   Terms: A map from skolems k to a set of builtin terms in the triples
 *          (k, ts, s). That is, Terms[k] = ts
 *
 *   CandSols : A map from a skolem k to a set of possible solutions for its
 *              corresponding obligation. Whenever there is a successful match,
 *              it is added to this set.
 *
 *   Pool : A map from a sygus type T to a set of enumerated terms in T.
 *          The terms in this pool are patterns whose builtin analogs are used
 *          for matching against the terms to reconstruct t in (k, t, s).
 *
 *   let k_0 be a fresh skolem of sygus type T_0
 *   Obs[T_0] += (k_0, [t_0], null)
 *
 *   while Sol[k_0] == null
 *     Obs' = {} // map from T to sets of triples pending addition to Obs
 *     // enumeration phase
 *     for each subfield type T of T_0
 *       // enumerated terms may contain variables zs ranging over all terms of
 *       // their type (subfield types of T_0)
 *       s[zs] = nextEnum(T)
 *       if (s[zs] is ground)
 *         builtin = rewrite(toBuiltIn(s[zs]))
 *         // let X be the theory the solver is invoked with
 *         find (k, ts, s) in Obs[T] s.t. |=_X ts[0] = builtin
 *         if no such triple exists
 *           let k be a new variable of type : T
 *           Obs[T] += (k, [builtin], null)
 *         markSolved(k, s[zs])
 *       else if no s' in Pool[T] and matcher sigma s.t.
 *             rewrite(toBuiltIn(s')) * sigma = rewrite(toBuiltIn(s[zs]))
 *         Pool[T] += s[zs]
 *         for each (k, ts, null) in Obs[T]
 *           Obs' += matchNewObs(k, s[zs])
 *     // match phase
 *     while Obs' != {}
 *       Obs'' = {}
 *       for each (k, ts, null) in Obs' // s = null for all triples in Obs'
 *         Obs[T] += (k, ts, null)
 *         for each s[zs] in Pool[T]
 *           Obs'' += matchNewObs(k, s[zs])
 *       Obs' = Obs''
 *   g = Sol[k_0]
 *   instantiate free variables of g with arbitrary sygus datatype values
 * }
 *
 * matchNewObs(k, s[zs]) returns Obs'
 * {
 *   u = rewrite(toBuiltIn(s[zs]))
 *   for each t in Terms[k]
 *     if match(u, t) == {toBuiltin(zs) -> sts}
 *       Sub = {} // substitution map from zs to corresponding new vars ks
 *       for each (z, st) in {zs -> sts}
 *         // let X be the theory the solver is invoked with
 *         if exists (k', ts', s') in Obs[T] !=_X ts'[0] = st
 *           ts' += st
 *           Sub[z] = k'
 *         else
 *           let sk be a new variable of type : typeOf(z)
 *           Sub[z] = sk
 *           Obs'[typeOf(z)] += (sk, [st], null)
 *       if Sol[sk] != null forall (z, sk) in Sub
 *         markSolved(k, s{Sub})
 *       else
 *         CandSol[k] += s{Sub}
 * }
 *
 * markSolved(k, s)
 * {
 *   if Sol[k] != null
 *     return
 *   Sol[k] = s
 *   CandSols[k] += s
 *   Stack = {k}
 *   while Stack != {}
 *     k' = pop(Stack)
 *     for all k'' in CandSols keys
 *       for all s'[k'] in CandSols[k'']
 *         s'{k' -> Sol[k']}
 *         if s' does not contain free variables in Obs
 *           Sol[k''] = s'
 *           push(Stack, k'')
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

  /** Reconstruct solution.
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
                           int8_t& reconstructed,
                           uint64_t enumLimit);

 private:
  /** Match obligation `k`'s builtin term with pattern `sz`.
   *
   * This function matches the builtin term to reconstruct for obligation `k`
   * with the builtin analog of the pattern `sz`. If the match succeeds, `sz` is
   * added to the set of candidate solutions for `k` and a set of new
   * sub-obligations to satisfy is returned. If there are no new sub-obligations
   * to satisfy, then `sz` is considered a solution to obligation `k` and
   * `matchNewObs(k, sz)` is called. For example, given:
   *
   * Obs[typeOf(c_z1)] = {(c_z1, (+ 1 1), null)}
   * Pool[typeOf(c_z1)] = {(c_+ c_z2 c_z3)}
   * CandSols = {}
   *
   * Then calling `matchNewObs(c_z1, (c_+ c_z2 c_z3))` will result in:
   *
   * Obs[typeOf(c_z1)] = {(c_z1, (+ 1 1), null), (c_z4, 1, null)}
   * Pool[typeOf(c_z1)] = {(c_+ c_z2 c_z3)}
   * CandSols = {c_z1 -> {(c_+ c_z4 c_z4)}}
   *
   * and will return `{typeOf(c_z4) -> {c_z4}}`.
   *
   * Notice that `c_z2` and `c_z3` are not returned as new sub-obligations.
   * Instead, `(c_+ c_z2 c_z3)` is instantiated with a new skolem `c_z4`, which
   * is then added to the set of obligations. This is done to allow the reuse of
   * patterns in `Pool`. Also, notice that only one new skolem/sub-obligation is
   * generated. That's because the builtin analogs of `c_z2` and `c_z3` match
   * with the same builtin term `1`.
   *
   * @param k free var whose builtin term we need to match
   * @param sz a pattern to match `ob`s builtin term with
   * @return a set of new obligations to satisfy if the match succeeds
   */
  TypeObligationSetMap matchNewObs(Node k, Node sz);

  /** mark obligation `k` as solved.
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
   * Remove solved obligations from the given set of obligations.
   *
   * @param unsolvedObs A set of obligations containing solved ones
   */
  void removeSolvedObs(TypeObligationSetMap& obs);

  /**
   * Replace all variables in `n` with ground values. Before, calling `match`,
   * `matchNewObs` rewrites the builtin analog of `n` which contains variables.
   * The rewritten term, however, may contain fewer variables:
   *
   * rewrite((ite true z1 z2)) = z1 // n = (c_ite c_true c_z1 c_z2)
   *
   * In such cases, `matchNewObs` replaces the remaining variables (`c_z1`) with
   * obligations and ignores the eliminated ones (`c_z2`). Since the values of
   * the eliminated variables do not matter, they are replaced with some ground
   * values by calling this method.
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
   * Print the pool of patterns/shape used in the matching phase.
   *
   * \note requires enabling "sygus-rcons" trace
   *
   * @param pool a pool of patterns/shapes to print
   */
  void printPool(
      const std::unordered_map<TypeNode, std::vector<Node>>& pool) const;

  /** pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;

  /** a map from an obligation to its reconstruction info */
  std::unordered_map<Node, RConsObligationInfo> d_obInfo;
  /** a map from a sygus datatype type to its reconstruction info */
  std::unordered_map<TypeNode, RConsTypeInfo> d_stnInfo;

  /** a map from an obligation to its sygus solution (if it exists) */
  std::unordered_map<TNode, TNode> d_sol;

  /** a map from a candidate solution to its sub-obligations */
  std::unordered_map<Node, std::vector<Node>> d_subObs;
  /** a map from a candidate solution to its parent obligation */
  std::unordered_map<Node, Node> d_parentOb;

  /** a cache of sygus variables treated as ground terms by matching */
  std::unordered_map<Node, Node> d_sygusVars;

  /** A trie for filtering out redundant terms from the paterns pool */
  expr::MatchTrie d_poolTrie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif  // CVC5__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
