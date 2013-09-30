/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of algorithm suggested by Deharbe, Fontaine,
 ** Merz, and Paleo, "Exploiting symmetry in SMT problems," CADE 2011
 **
 ** Implementation of algorithm suggested by Deharbe, Fontaine, Merz,
 ** and Paleo, "Exploiting symmetry in SMT problems," CADE 2011.
 **
 ** From the paper:
 **
 ** <pre>
 **   \f$ P := guess\_permutations(\phi) \f$
 **   foreach \f$ {c_0, ..., c_n} \in P \f$ do
 **     if \f$ invariant\_by\_permutations(\phi, {c_0, ..., c_n}) \f$ then
 **       T := \f$ select\_terms(\phi, {c_0, ..., c_n}) \f$
 **       cts := \f$ \emptyset \f$
 **       while T != \f$ \empty \wedge |cts| <= n \f$ do
 **         \f$ t := select\_most\_promising\_term(T, \phi) \f$
 **         \f$ T := T \setminus {t} \f$
 **         cts := cts \f$ \cup used\_in(t, {c_0, ..., c_n}) \f$
 **         let \f$ c \in {c_0, ..., c_n} \setminus cts \f$
 **         cts := cts \f$ \cup {c} \f$
 **         if cts != \f$ {c_0, ..., c_n} \f$ then
 **           \f$ \phi := \phi \wedge ( \vee_{c_i \in cts} t = c_i ) \f$
 **         end
 **       end
 **     end
 **   end
 **   return \f$ \phi \f$
 ** </pre>
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__SYMMETRY_BREAKER_H
#define __CVC4__THEORY__UF__SYMMETRY_BREAKER_H

#include <iostream>
#include <list>
#include <vector>

#include "expr/node.h"
#include "expr/node_builder.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace uf {

class SymmetryBreaker : public context::ContextNotifyObj {

  class Template {
    Node d_template;
    NodeBuilder<> d_assertions;
    std::hash_map<TNode, std::set<TNode>, TNodeHashFunction> d_sets;
    std::hash_map<TNode, TNode, TNodeHashFunction> d_reps;

    TNode find(TNode n);
    bool matchRecursive(TNode t, TNode n);

  public:
    Template();
    bool match(TNode n);
    std::hash_map<TNode, std::set<TNode>, TNodeHashFunction>& partitions() { return d_sets; }
    Node assertions() {
      switch(d_assertions.getNumChildren()) {
      case 0: return Node::null();
      case 1: return d_assertions[0];
      default: return Node(d_assertions);
      }
    }
    void reset();
  };/* class SymmetryBreaker::Template */

public:

  typedef std::set<TNode> Permutation;
  typedef std::set<Permutation> Permutations;
  typedef TNode Term;
  typedef std::list<Term> Terms;
  typedef std::set<Term> TermEq;
  typedef std::hash_map<Term, TermEq, TNodeHashFunction> TermEqs;

private:

  /**
   * This class wasn't initially built to be incremental.  It should
   * be attached to a UserContext so that it clears everything when
   * a pop occurs.  This "assertionsToRerun" is a set of assertions to
   * feed back through assertFormula() when we started getting things
   * again.  It's not just a matter of effectiveness, but also soundness;
   * if some assertions (still in scope) are not seen by a symmetry-breaking
   * round, then some symmetries that don't actually exist might be broken,
   * leading to unsound results!
   */
  context::CDList<Node> d_assertionsToRerun;
  bool d_rerunningAssertions;

  std::vector<Node> d_phi;
  std::set<TNode> d_phiSet;
  Permutations d_permutations;
  Terms d_terms;
  Template d_template;
  std::hash_map<Node, Node, NodeHashFunction> d_normalizationCache;
  TermEqs d_termEqs;

  void clear();
  void rerunAssertionsIfNecessary();

  void guessPermutations();
  bool invariantByPermutations(const Permutation& p);
  void selectTerms(const Permutation& p);
  Terms::iterator selectMostPromisingTerm(Terms& terms);
  void insertUsedIn(Term term, const Permutation& p, std::set<Node>& cts);
  Node normInternal(TNode phi);
  Node norm(TNode n);

  // === STATISTICS ===
  /** number of new clauses that come from the SymmetryBreaker */
  KEEP_STATISTIC(IntStat,
                 d_clauses,
                 "theory::uf::symmetry_breaker::clauses", 0);
  /** number of new clauses that come from the SymmetryBreaker */
  KEEP_STATISTIC(IntStat,
                 d_units,
                 "theory::uf::symmetry_breaker::units", 0);
  /** number of potential permutation sets we found */
  KEEP_STATISTIC(IntStat,
                 d_permutationSetsConsidered,
                 "theory::uf::symmetry_breaker::permutationSetsConsidered", 0);
  /** number of invariant permutation sets we found */
  KEEP_STATISTIC(IntStat,
                 d_permutationSetsInvariant,
                 "theory::uf::symmetry_breaker::permutationSetsInvariant", 0);
  /** time spent in invariantByPermutations() */
  KEEP_STATISTIC(TimerStat,
                 d_invariantByPermutationsTimer,
                 "theory::uf::symmetry_breaker::timers::invariantByPermutations");
  /** time spent in selectTerms() */
  KEEP_STATISTIC(TimerStat,
                 d_selectTermsTimer,
                 "theory::uf::symmetry_breaker::timers::selectTerms");
  /** time spent in initial round of normalization */
  KEEP_STATISTIC(TimerStat,
                 d_initNormalizationTimer,
                 "theory::uf::symmetry_breaker::timers::initNormalization");

protected:

  void contextNotifyPop() {
    Debug("ufsymm") << "UFSYMM: clearing state due to pop" << std::endl;
    clear();
  }

public:

  SymmetryBreaker(context::Context* context);
  ~SymmetryBreaker() throw() {}
  void assertFormula(TNode phi);
  void apply(std::vector<Node>& newClauses);

};/* class SymmetryBreaker */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, const ::CVC4::theory::uf::SymmetryBreaker::Permutation& p);

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__SYMMETRY_BREAKER_H */
