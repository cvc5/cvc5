/*********************                                                        */
/*! \file theory_uf_tim.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.
 **
 ** This is a basic implementation of the Theory of Uninterpreted Functions
 ** with Equality.  It is based on the Nelson-Oppen algorithm given in
 ** "Fast Decision Procedures Based on Congruence Closure"
 **  (http://portal.acm.org/ft_gateway.cfm?id=322198&type=pdf)
 ** This has been extended to work in a context-dependent way.
 ** This interacts heavily with the data-structures given in ecdata.h .
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__TIM__THEORY_UF_TIM_H
#define CVC4__THEORY__UF__TIM__THEORY_UF_TIM_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"

#include "context/context.h"
#include "context/cdo.h"
#include "context/cdlist.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/tim/ecdata.h"

namespace CVC4 {
namespace theory {
namespace uf {
namespace tim {

class TheoryUFTim : public Theory {

private:

  /**
   * List of all of the non-negated literals from the assertion queue.
   * This is used only for conflict generation.
   * This differs from pending as the program generates new equalities that
   * are not in this list.
   * This will probably be phased out in future version.
   */
  context::CDList<Node> d_assertions;

  /**
   * List of pending equivalence class merges.
   *
   * Tricky part:
   * Must keep a hard link because new equality terms are created and appended
   * to this list.
   */
  context::CDList<Node> d_pending;

  /** Index of the next pending equality to merge. */
  context::CDO<unsigned> d_currentPendingIdx;

  /** List of all disequalities this theory has seen. */
  context::CDList<Node> d_disequality;

  /**
   * List of all of the terms that are registered in the current context.
   * When registerTerm is called on a term we want to guarentee that there
   * is a hard link to the term for the duration of the context in which
   * register term is called.
   * This invariant is enough for us to use soft links where we want is the
   * current implementation as well as making ECAttr() not context dependent.
   * Soft links used both in ECData, and Link.
   */
  context::CDList<Node> d_registered;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUFTim(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation);

  /** Destructor for the TheoryUF object. */
  ~TheoryUFTim();

  /**
   * Registers a previously unseen [in this context] node n.
   * For TheoryUF, this sets up and maintains invaraints about
   * equivalence class data-structures.
   *
   * Overloads a void registerTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void registerTerm(TNode n);

  /**
   * Currently this does nothing.
   *
   * Overloads a void preRegisterTerm(TNode n); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void preRegisterTerm(TNode n);

  /**
   * Checks whether the set of literals provided to the theory is consistent.
   *
   * If this is called at any effort level, it computes the congruence closure
   * of all of the positive literals in the context.
   *
   * If this is called at full effort it checks if any of the negative literals
   * are inconsistent with the congruence closure.
   *
   * Overloads  void check(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void check(Effort level);

  void presolve() {
    // do nothing
  }

  /**
   * Propagates theory literals. Currently does nothing.
   *
   * Overloads void propagate(Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void propagate(Effort level) {}

  /**
   * Explains a previously reported conflict. Currently does nothing.
   *
   * Overloads void explain(TNode n, Effort level); from theory.h.
   * See theory/theory.h for more information about this method.
   */
  void explain(TNode n) {}

  std::string identify() const { return std::string("TheoryUFTim"); }

private:
  /**
   * Checks whether 2 nodes are already in the same equivalence class tree.
   * This should only be used internally, and it should only be called when
   * the only thing done with the equivalence classes is an equality check.
   *
   * @returns true iff ccFind(x) == ccFind(y);
   */
  bool sameCongruenceClass(TNode x, TNode y);

  /**
   * Checks whether Node x and Node y are currently congruent
   * using the equivalence class data structures.
   * @returns true iff
   *    |x| = n = |y| and
   *    x.getOperator() == y.getOperator() and
   *    forall 1 <= i < n : ccFind(x[i]) == ccFind(y[i])
   */
  bool equiv(TNode x, TNode y);

  /**
   * Merges 2 equivalence classes, checks wether any predecessors need to
   * be set equal to complete congruence closure.
   * The class with the smaller class size will be merged.
   * @pre ecX->isClassRep()
   * @pre ecY->isClassRep()
   */
  void ccUnion(ECData* ecX, ECData* ecY);

  /**
   * Returns the representative of the equivalence class.
   * May modify the find pointers associated with equivalence classes.
   */
  ECData* ccFind(ECData* x);

  /** Performs Congruence Closure to reflect the new additions to d_pending. */
  void merge();

  /** Constructs a conflict from an inconsistent disequality. */
  Node constructConflict(TNode diseq);

};/* class TheoryUFTim */


/**
 * Cleanup function for ECData. This will be used for called whenever
 * a ECAttr is being destructed.
 */
struct ECCleanupStrategy {
  static void cleanup(ECData* ec) {
    Debug("ufgc") << "cleaning up ECData " << ec << "\n";
    ec->deleteSelf();
  }
};/* struct ECCleanupStrategy */

/** Unique name to use for constructing ECAttr. */
struct ECAttrTag {};

/**
 * ECAttr is the attribute that maps a node to an equivalence class.
 */
typedef expr::Attribute<ECAttrTag, ECData*, ECCleanupStrategy> ECAttr;

}/* CVC4::theory::uf::tim namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__UF__TIM__THEORY_UF_TIM_H */
