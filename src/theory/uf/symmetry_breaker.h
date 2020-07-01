/*********************                                                        */
/*! \file symmetry_breaker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

#ifndef CVC4__THEORY__UF__SYMMETRY_BREAKER_H
#define CVC4__THEORY__UF__SYMMETRY_BREAKER_H

#include <iostream>
#include <list>
#include <unordered_map>
#include <vector>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "smt/smt_statistics_registry.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace uf {

class SymmetryBreaker : public context::ContextNotifyObj {

  class Template {
    Node d_template;
    NodeBuilder<> d_assertions;
    std::unordered_map<TNode, std::set<TNode>, TNodeHashFunction> d_sets;
    std::unordered_map<TNode, TNode, TNodeHashFunction> d_reps;

    TNode find(TNode n);
    bool matchRecursive(TNode t, TNode n);

  public:
    Template();
    bool match(TNode n);
    std::unordered_map<TNode, std::set<TNode>, TNodeHashFunction>& partitions() { return d_sets; }
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
  typedef std::unordered_map<Term, TermEq, TNodeHashFunction> TermEqs;

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
  std::unordered_map<Node, Node, NodeHashFunction> d_normalizationCache;
  TermEqs d_termEqs;
  TermEqs d_termEqsOnly;

  void clear();
  void rerunAssertionsIfNecessary();

  void guessPermutations();
  bool invariantByPermutations(const Permutation& p);
  void selectTerms(const Permutation& p);
  Terms::iterator selectMostPromisingTerm(Terms& terms);
  void insertUsedIn(Term term, const Permutation& p, std::set<Node>& cts);
  Node normInternal(TNode phi, size_t level);
  Node norm(TNode n);

  std::string d_name;
  
  // === STATISTICS ===
  /** number of new clauses that come from the SymmetryBreaker */
  struct Statistics {
    /** number of new clauses that come from the SymmetryBreaker */
    IntStat d_clauses;
    IntStat d_units;
    /** number of potential permutation sets we found */
    IntStat d_permutationSetsConsidered;
    /** number of invariant permutation sets we found */
    IntStat d_permutationSetsInvariant;
    /** time spent in invariantByPermutations() */
    TimerStat d_invariantByPermutationsTimer;
    /** time spent in selectTerms() */
    TimerStat d_selectTermsTimer;
    /** time spent in initial round of normalization */
    TimerStat d_initNormalizationTimer;

    Statistics(std::string name);
    ~Statistics();
  };

  Statistics d_stats;

 protected:
  void contextNotifyPop() override
  {
    Debug("ufsymm") << "UFSYMM: clearing state due to pop" << std::endl;
    clear();
  }

 public:
  SymmetryBreaker(context::Context* context, std::string name = "");

  void assertFormula(TNode phi);
  void apply(std::vector<Node>& newClauses);

};/* class SymmetryBreaker */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */

std::ostream& operator<<(std::ostream& out, const ::CVC4::theory::uf::SymmetryBreaker::Permutation& p);

}/* CVC4 namespace */

#endif /* CVC4__THEORY__UF__SYMMETRY_BREAKER_H */
