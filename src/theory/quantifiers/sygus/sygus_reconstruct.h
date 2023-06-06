/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "expr/match_trie.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/rcons_obligation.h"
#include "theory/quantifiers/sygus/rcons_type_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

using BuiltinSet = std::unordered_set<Node>;
using TypeBuiltinSetMap = std::unordered_map<TypeNode, BuiltinSet>;
using NodePairMap = std::unordered_map<Node, Node>;

/** SygusReconstruct
 *
 * This class implements an algorithm for reconstructing a given term such that
 * the reconstructed term is equivalent to the original term and its syntax
 * matches a specified grammar.
 *
 * Goal: find a term g in sygus type T0 that is equivalent to builtin term t0.
 *
 * rcons(t0, T0) returns g
 * {
 *   Obs: A set of pairs to reconstruct into T, where each pair is of the form
 *        (k, ts), where k is a skolem of a sygus type T and ts is a set of
 *        builtin terms of the type encoded by T.
 *
 *   Terms: A map from skolems k to a set of builtin terms in the pairs (k, ts).
 *          That is, Terms[k] = ts.
 *
 *   Sol: A map from skolems k to (possibly null) sygus terms of type T
 *        representing solutions to the obligations.
 *
 *   CandSols : A map from a skolem k to a set of possible solutions for its
 *              corresponding obligation. Whenever there is a successful match,
 *              it is added to this set.
 *
 *   Pool : A map from a sygus type T to a set of enumerated terms in T.
 *          The terms in this pool are patterns whose builtin analogs are used
 *          for matching against the terms to reconstruct ts in (k, ts).
 *
 *   let k0 be a fresh skolem of sygus type T0
 *   Obs[T0] += (k0, {t0})
 *
 *   TermsToRecons[T0] = {t0}
 *
 *   while Sol[k0] == null
 *     // map from T to terms pending addition to TermsToRecons
 *     TermsToRecons' = {}
 *     // enumeration phase
 *     for each subfield type T of T0
 *       // enumerated terms may contain variables zs ranging over all terms of
 *       // their type (subfield types of T0)
 *       s[zs] = nextEnum(T)
 *       if (s[zs] is ground)
 *         builtin = rewrite(toBuiltIn(s[zs]))
 *         // let X be the theory the solver is invoked with
 *         find (k, ts) in Obs s.t. |=_X ts[0] = builtin
 *         if no such pair exists
 *           k = newVar(T)
 *           ts = {builtin}
 *           Obs += (k, ts)
 *         markSolved((k, ts), s[zs])
 *       else if no s' in Pool[T] and matcher sigma s.t.
 *             rewrite(toBuiltIn(s')) * sigma = rewrite(toBuiltIn(s[zs]))
 *         Pool[T] += s[zs]
 *         for each t in TermsToRecons[T]
 *           TermsToRecons' += matchNewObs(t, s[zs])
 *     // match phase
 *     while TermsToRecons' != {}
 *       TermsToRecons'' = {}
 *       for each subfield type T of T0
 *         for each t in TermsToRecons'[T]
 *           TermsToRecons[T] += t
 *           for each s[zs] in Pool[T]
 *             TermsToRecons'' += matchNewObs(t, s[zs])
 *         TermsToRecons' = TermsToRecons''
 *   g = Sol[k0]
 *   instantiate free variables of g with arbitrary sygus datatype values
 * }
 *
 * matchNewObs(t, s[zs]) returns TermsToRecons'
 * {
 *   u = rewrite(toBuiltIn(s[zs]))
 *   if match(u, t) == {toBuiltin(zs) -> sts}
 *     Sub = {} // substitution map from zs to corresponding new vars ks
 *     for each (z, st) in {zs -> sts}
 *       // let X be the theory the solver is invoked with
 *       if exists (k, ts) in Obs s.t. |=_X ts[0] = st
 *         ts += st
 *         Sub[z] = k
 *       else
 *         sk = newVar(typeOf(z))
 *         Sub[z] = sk
 *         TermsToRecons'[typeOf(z)] += st
 *     if Sol[sk] != null forall (z, sk) in Sub
 *       markSolved(k, s{Sub})
 *     else
 *       CandSol[k] += s{Sub}
 * }
 *
 * markSolved((k, ts), s)
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
class SygusReconstruct : protected expr::NotifyMatch,
                         protected NodeConverter,
                         protected EnvObj
{
 public:
  /**
   * Constructor.
   *
   * @param env reference to the environment
   * @param tds database for sygus terms
   * @param s statistics managed for the synth engine
   */
  SygusReconstruct(Env& env, TermDbSygus* tds, SygusStatistics& s);

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
   * @param sol the target term
   * @param stn the sygus datatype type encoding the syntax restrictions
   * @param reconstructed the flag to update, set to 1 if we successfully return
   *                      a node, otherwise it is set to -1
   * @param enumLimit a value to limit the effort spent by this class (roughly
   *                  equal to the number of intermediate terms to try)
   * @return the reconstructed sygus term
   */
  Node reconstructSolution(Node sol,
                           TypeNode stn,
                           int8_t& reconstructed,
                           uint64_t enumLimit);

 protected:
  /**
   * Replaces n-ary operators with their binary versions.
   *
   * @param n the term to convert term
   * @return the converted term
   */
  Node postConvert(Node n) override;

 private:
  /**
   * Implements the reconstruction procedure.
   *
   * @param sol the target term
   * @param stn the sygus datatype type encoding the syntax restrictions
   * @param reconstructed the flag to update, set to 1 if we successfully return
   *                      a node, otherwise it is set to -1
   * @param enumLimit a value to limit the effort spent by this class (roughly
   *                  equal to the number of intermediate terms to try)
   */
  void main(Node sol, TypeNode stn, int8_t& reconstructed, uint64_t enumLimit);

  /**
   * Implements the match phase of the reconstruction procedure with the pool
   * prepopulated with sygus datatype type constructors (grammar rules).
   *
   * @param sol the target term
   * @param stn the sygus datatype type encoding the syntax restrictions
   * @param reconstructed the flag to update, set to 1 if we successfully return
   *                      a node, otherwise it is set to -1
   */
  void fast(Node sol, TypeNode stn, int8_t& reconstructed);

  /** Match builtin term `t` with pattern `sz` and create new obligations.
   *
   * This function calls `match` to reconstruct `t` with the builtin analog of
   * the pattern `sz`. If the match succeeds, `sz` is added to the set of
   * candidate solutions for the obligation `ob` corresponding to the builtin
   * term `t` and a set of new sub-terms to reconstruct is returned. If there
   * are no new sub-terms to reconstruct, then `sz` is considered a solution to
   * obligation `ob` and `markSolved(ob, sz)` is called. For example, given:
   *
   * Obs = [(k0, {(+ 1 1)})]
   * Pool[T0] = {(c_+ z1 z2)}
   * CandSols = {}
   *
   * Then calling `matchNewObs((+ 1 1), (c_+ z1 z2))` will result in:
   *
   * Obs = [(k0, {(+ 1 1)}), (k1, {1})]
   * Pool[T0] = {(c_+ z1 z2)}
   * CandSols = {k0 -> {(c_+ k1 k1)}}
   *
   * and will return `{T0 -> {1}}`.
   *
   * Notice that the patterns/shapes in pool are generic, and thus, contain vars
   * `z` as opposed to skolems `k`. Also, notice that `(c_+ z1 z2)` is
   * instantiated with only one skolem `k1`, which is then added to the set of
   * obligations. That's because the builtin analogs of `z1` and `z2` match with
   * the same builtin term `1`.
   *
   * @param t builtin term we need to reconstruct
   * @param sz a pattern to match against `t`
   * @return a set of new builtin terms to reconstruct if the match succeeds
   */
  TypeBuiltinSetMap matchNewObs(Node t, Node sz);

  /** Match builtin term `t` with builtin pattern `tz`.
   *
   * If the match succeeds, `subs` will contain substitions from variables `z`
   * in `tz` to builtin terms such that:
   *
   * |=_X tz * subs = t (where * denotes application of substitution).
   *
   * For example, given:
   * tz = (+ a (* z1 2)) (z1 denotes a free variable)
   * t  = (+ a (* b 2))
   * a call to match may return `false` or `true` with `subs` = {(z1, b)}
   *
   * This method may perform simple pattern-matching or more elaborate
   * procedures. For example, given:
   * tz = (and z1 z2) (z1 and z2 denote free variables)
   * t  = (not (or a b))
   * a call to match may return `false` or `true` with `subs` = {(z1, (not a)),
   * (z2, (not b))}
   *
   * @param t target builtin term to match against
   * @param tz pattern to instantiate
   * @param subs mapping from free vars in `tz` to builtin terms
   * @return whether or not matching `tz` against `t` was successful
   */
  bool match(Node t, Node tz, NodePairMap& subs);

  /** mark obligation `ob` as solved.
   *
   * This function first marks `s` as the complete/constant solution for
   * `ob`. Then it substitutes all instances of `ob` in partial solutions to
   * other obligations with `s`. The function repeats those two steps for each
   * partial solution that gets completed because of the second step. For
   * example, given:
   *
   * CandSols = {
   *   k0 -> {(c_+ k1 c_1)},
   *   k1 -> {(c_* k2 c_x)},
   *   k2 -> {c_2}
   * }
   * Sol = {}
   *
   * Then calling `markSolved(k2, c_2)` will result in:
   *
   * CandSols = {
   *   k0 -> {(c_+ k1 c_1), (c_+ (c_* c_2 c_x) c_1)},
   *   k1 -> {(c_* k2 c_x), (c_* c_2 c_x)},
   *   k2 -> {c_2}
   * }
   * Sol = {
   *   k0 -> (c_+ (c_* c_2 c_x) c_1),
   *   k1 -> (c_* c_2 c_x),
   *   k2 -> c_2
   * }
   *
   * @param ob free var to mark as solved and substitute
   * @param sol solution to `ob`
   */
  void markSolved(RConsObligation* ob, Node s);

  /**
   * Initialize a sygus enumerator and a candidate rewrite database for each
   * sygus datatype type.
   *
   * @param stn The sygus datatype type encoding the syntax restrictions
   */
  void initialize(TypeNode stn);

  /**
   * Remove reconstructed terms from the given set of terms to reconstruct.
   *
   * @param termsToRecons a set of terms to reconstruct possibly containing
   *                      already reconstructed ones
   */
  void removeReconstructedTerms(TypeBuiltinSetMap& termsToRecons);

  /**
   * Replace all variables in `n` with ground values. Before, calling `match`,
   * `matchNewObs` rewrites the builtin analog of `n` which contains variables.
   * The rewritten term, however, may contain fewer variables:
   *
   * rewrite((ite true z1 z2)) = z1 // n = (c_ite c_true z1 z2)
   *
   * In such cases, `matchNewObs` replaces the remaining variables (`z1`) with
   * obligations and ignores the eliminated ones (`z2`). Since the values of the
   * eliminated variables do not matter, they are replaced with some ground
   * values by calling this method.
   *
   * @param n a term containing variables
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
   */
  void printPool() const;

  /** pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;

  /** a list of obligations to solve */
  std::vector<std::unique_ptr<RConsObligation>> d_obs;
  /** a map from a sygus datatype type to its reconstruction info */
  std::unordered_map<TypeNode, RConsTypeInfo> d_stnInfo;

  /** a map from an obligation's skolem to its sygus solution (if it exists) */
  std::unordered_map<TNode, TNode> d_sol;

  /** a map from a candidate solution to its sub-obligations */
  std::unordered_map<Node, std::vector<RConsObligation*>> d_subObs;
  /** a map from a candidate solution to its parent obligation */
  std::unordered_map<Node, RConsObligation*> d_parentOb;

  /** a cache of sygus variables treated as ground terms by matching */
  std::unordered_map<Node, Node> d_sygusVars;

  /** a set of unique (up to rewriting) patterns/shapes in the grammar used by
   * matching */
  std::unordered_map<TypeNode, std::vector<Node>> d_pool;
  /** A trie for filtering out redundant terms from the paterns pool */
  expr::MatchTrie d_poolTrie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif  // CVC5__THEORY__QUANTIFIERS__SYGUS_RECONSTRUCT_H
