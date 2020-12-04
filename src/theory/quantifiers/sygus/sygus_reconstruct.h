/*********************                                                        */
/*! \file sygus_reconstruct.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_stats.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct Obligation
{
  Node d_builtinTerm;
  TypeNode d_sygusType;
  Obligation(Node builtinTerm, TypeNode sygusType)
      : d_builtinTerm(builtinTerm), d_sygusType(sygusType)
  {
  }

  Node builtinTerm() const { return d_builtinTerm; }

  TypeNode sygusType() const { return d_sygusType; }
};

struct ObligationInfo
{
  Node d_var;
  Node d_sol;
  std::vector<Node> d_eqClass;

  ObligationInfo() : d_var(Node::null()), d_sol(Node::null()), d_eqClass() {}

  explicit ObligationInfo(Node var)
      : d_var(var), d_sol(Node::null()), d_eqClass()
  {
  }

  Node var() const { return d_var; }
  Node sol() const { return d_sol; }
  void setSol(Node sol) { d_sol = sol; }
  std::vector<Node>& eqClass() { return d_eqClass; }
  const std::vector<Node>& eqClass() const { return d_eqClass; }

  void addToEqClass(Node n) { d_eqClass.push_back(n); }

  bool isSatisfied() const { return d_sol != Node::null(); }
};

inline bool operator<(const Obligation& left, const Obligation& right)
{
  return left.builtinTerm() < right.builtinTerm()
         || (!(right.builtinTerm() < left.builtinTerm())
             && left.sygusType() < right.sygusType());
}

inline bool operator==(const Obligation& left, const Obligation& right)
{
  return left.builtinTerm() == right.builtinTerm()
         && left.sygusType() == right.sygusType();
}

inline std::ostream& operator<<(std::ostream& out, Obligation ob)
{
  out << "ob<" << ob.builtinTerm() << ", " << ob.sygusType() << ">";
  return out;
}

/** SygusReconstruct
 * TODO(abdoo8080): add documentation
 * This class implements an algorithm for reconstruction...
 *
 *
 *

Goal: find a term g in sygus type T that is equivalent to builtin term t.

rcons( t, T )
{

  // a list of labeled terms to reconstruct into Sygus type T, where
  // a labelled term is of the form "k : t" where k is a skolem of type T, and
  // t is a builtin term of the type encoded by T.
  Obs<T>

  CandSols<k> : a list of possible solutions, for each label k. Whenever there is a successful match, it's added to this list.
  Pool<T> : a list of enumerated terms for each sygus type

  let k be a fresh skolem of sygus type T

  Obs<T> += {k : t}

  for each T
    Pool<T> = ... initial set of terms corresponding to generalizations of each
rule in T...

  while true
    // enumeration phase
    for each T
      s[z] = nextEnum(T_{z})
      if s[z] is not subsumed (there is no s' in Pool<T> such that s' * sigma = s)
        if there exists an r in pool<T> s.t. |=_T s[z] = r
          CandSol<s[z]> ~ CandSol<r>
        pool<T> += s[z]
        for each k : t in Obs<T>
          Obs' += matchNewObs(k : t, s[z])
    // match phase
    while Obs' != {}
      Obs'' = {}
      for each T, for each k : t in Obs'<T>
        Obs<T> += k
        for each s[z] in Pool<T>
          Obs'' += matchNewObs(k:t, s[z])
      Obs' = Obs''

}

matchNewObs(k : t, s[z]) : Obs'
{
  u = rewrite(toBuiltIn(s[z]))
  if u = t // u is a ground term (only concrete variables)
    markSolved( k, s[z] )
    if (Sol<k_0> != null)
      exit with Sol<k_0>
  else if match(u, t) == {toBuiltin(z) -> t'}
    let k' be a new variable of type : typeOf(z)
    CandSol<k> += s[k']
    Obs'<typeOf(z)> += k' : t' // could be duplicate
}

Sol<k> : solution for label k, null otherwise

markSolved ( k, s )
{
  Sol<k> = s
  S = {k}      // a stack to process
  while S != {}
    k' = pop(S)
    for all k'' in CandSol keys
      for all s'[k'] in CandSol<k''>
        s'{k' -> Sol<k'>}
        if s' is ground
          Sol<k''> = s'
          push(S, k'')
}

 *
 */
class SygusReconstruct : public expr::NotifyMatch
{
 public:
  SygusReconstruct(TermDbSygus* tds, SygusStatistics& s);
  ~SygusReconstruct() {}
  /** reconstruct solution
   *
   * Returns (if possible) a sygus encoding of a node that is equivalent to sol
   * and whose syntax matches the grammar corresponding to sygus datatype stn.
   * The value reconstructed is set to 1 if we successfully return a node,
   * otherwise it is set to -1.
   *
   * @param sol The target term.
   * @param stn The sygus datatype type encoding the syntax restrictions,
   * @param reconstructed The flag to update, indicating the status of the
   * reconstruciton,
   * @param enumLimit A value to limit the effort spent by this class (roughly
   * equal to the number of intermediate terms to try).
   * @return The reconstructed sygus term.
   *
   * For example, given:
   *   sol = (* 2 x)
   *   stn = A sygus datatype encoding the grammar
   *           Start -> (c_PLUS Start Start) | c_x | c_0 | c_1
   * This method may return (c_PLUS c_x c_x) and set reconstructed to 1.
   */
  Node reconstructSolution(Node sol,
                           TypeNode stn,
                           int& reconstructed,
                           int enumLimit);

 private:
  void cleanup();

  // void init(TypeNode stn, std::map<TypeNode, std::vector<Node>>& pool);

  std::map<TypeNode, std::set<Node>> matchNewObs(Obligation ob, Node sz);

  void substituteOb(Obligation ob, Node sol);

  /** \brief mark obligation ob as solved.
   *
   * \par This function first marks `sol` as the complete/constant solution for
   * `ob`. Then it substitutes all instances of `ob` in partial solutions to
   * other obligations with `sol`. The function repeats those two steps for each
   * partial solution that gets completed because of the second step. For
   * example, given:
   *
   * \note example uses builtin terms instead of sygus terms for simplicity
   *
   * \code{.unparsed}
   * CandSol = {
   *  main_ob -> {(+ z1 1)},
   *  z1 -> {(* z2 x)},
   *  z2 -> {2}
   * }
   * Sol = {z2 -> 2}
   * \endcode
   *
   * \par Then calling markSolved(z2, 2) will result in:
   *
   * \code{.unparsed}
   * CandSol = {
   *  main_ob -> {(+ z1 1), (+ (* 2 x) 1)},
   *  z1 -> {(* z2 x), (* 2 x)},
   *  z2 -> {2}
   * }
   * Sol = {main_ob -> (+ (* 2 x) 1), z1 -> (* 2 x), z2 -> 2}
   * \endcode
   *
   * @param ob free var to mark as solved and substitute
   * @param sol constant solution to `ob`
   */
  void markSolved(Obligation ob, Node sol);

  void printEqClasses();

  void printPool(std::map<TypeNode, std::vector<Node>> pool);

  // TypeNode clone(TypeNode stn);

  Node nextEnum(TypeNode stn);

  bool notify(Node s,
              Node n,
              std::vector<Node>& vars,
              std::vector<Node>& subs) override;

  /** pointer to the sygus term database */
  TermDbSygus* d_tds;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;

  std::map<Node, Node> d_subs;

  std::map<Obligation, std::set<Node>> d_watchSet;
  /** a mapping from a obligations (encoded as free vars) to their sygus
   * solution representing `Sol` in the algorithm at the top */
  std::unordered_map<Node, Node, NodeHashFunction> d_sol;

  // std::map<TypeNode, std::set<Node>> d_activeObs;
  /** Sygus terms enumerator for each Sygus type (grammar non-terminal) */
  std::map<TypeNode, std::unique_ptr<SygusEnumerator>> d_enumerators;
  std::map<Obligation, ObligationInfo> d_obInfos;
  std::map<TypeNode, std::set<Node>> d_obs;
  /** an always up to date version of d_obs. Used to ensure the same obligation
   is not generated more than once between consequtive calls to matchNewObs. */
  std::map<TypeNode, std::set<Node>> d_obDb;
  std::map<Node, std::vector<Obligation>> d_children;
  expr::MatchTrie d_poolTrie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
