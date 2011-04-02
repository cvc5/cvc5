/*********************                                                        */
/*! \file unate_propagator.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief ArithUnatePropagator constructs implications of the form
 ** "if x < c and c < b, then x < b" (where c and b are constants).
 **
 ** ArithUnatePropagator detects unate implications amongst the atoms
 ** associated with the theory of arithmetic and informs the SAT solver of the
 ** implication. A unate implication is an implication of the form:
 **   "if x < c and c < b, then x < b" (where c and b are constants).
 ** Unate implications are always 2-SAT clauses.
 ** ArithUnatePropagator sends the implications to the SAT solver in an
 ** online fashion.
 ** This means that atoms may be added during solving or before.
 **
 ** ArithUnatePropagator maintains sorted lists containing all atoms associated
 ** for each unique left hand side, the "x" in the inequality "x < c".
 ** The lists are sorted by the value of the right hand side which must be a
 ** rational constant.
 **
 ** ArithUnatePropagator tries to send out a minimal number of additional
 ** lemmas per atom added.  Let (x < a), (x < b), (x < c) be arithmetic atoms s.t.
 ** a < b < c.
 ** If the the order of adding the atoms is (x < a), (x < b), and (x < c), then
 ** then set of all lemmas added is:
 **   {(=> (x<a) (x < b)), (=> (x<b) (x < c))}
 ** If the order is changed to (x < a), (x < c), and (x < b), then
 ** the final set of implications emitted is:
 **   {(=> (x<a) (x < c)), (=> (x<a) (x < b)), (=> (x<b) (x < c))}
 **
 ** \todo document this file
 **/



#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H

#include "expr/node.h"
#include "context/context.h"

#include "theory/output_channel.h"
#include "theory/arith/ordered_set.h"

#include <ext/hash_map>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithUnatePropagator {
private:
  typedef std::queue<Node> LemmaQueue;
  /** Unate implication queue */
  LemmaQueue d_lemmas;

  struct OrderedSetTriple {
    OrderedSet d_leqSet;
    OrderedSet d_eqSet;
    OrderedSet d_geqSet;
  };

  /** TODO: justify making this a TNode. */
  typedef __gnu_cxx::hash_map<Node, OrderedSetTriple, NodeHashFunction> NodeToOrderedSetMap;
  NodeToOrderedSetMap d_orderedListMap;

public:
  ArithUnatePropagator(context::Context* cxt);

  /**
   * Adds an atom to the propagator.
   * Any resulting lemmas will be output via d_arithOut.
   */
  void addAtom(TNode atom);

  /** Returns true if v has been added as a left hand side in an atom */
  bool hasAnyAtoms(TNode v);

  bool hasMoreLemmas() const { return !d_lemmas.empty(); }

  Node getNextLemma() {
    Node lemma = d_lemmas.front();
    d_lemmas.pop();
    return lemma;
  }
private:
  void addLemma(Node lemma) {
    d_lemmas.push(lemma);
  }


  OrderedSetTriple& getOrderedSetTriple(TNode left);
  OrderedSet& getEqSet(TNode left);
  OrderedSet& getLeqSet(TNode left);
  OrderedSet& getGeqSet(TNode left);


  /** Sends an implication (=> a b) to the PropEngine via d_arithOut. */
  void addImplication(TNode a, TNode b);

  /** Check to make sure an lhs has been properly set-up. */
  bool leftIsSetup(TNode left);

  /** Initializes the lists associated with a unique lhs. */
  void setupLefthand(TNode left);


  /**
   * The addImplicationsUsingKAndJList(...)
   * functions are the work horses of ArithUnatePropagator.
   * These take an atom of the kind K that has just been added
   * to its associated list, and the ordered list of Js associated with the lhs,
   * and uses these to deduce unate implications.
   * (K and J vary over EQUAL, LEQ, and GEQ.)
   *
   * Input:
   * atom - the atom being inserted of kind K
   * Jset - the list of atoms of kind J associated with the lhs.
   *
   * Unfortunately, these tend to be an absolute bear to read because
   * of all of the special casing and C++ iterator manipulation required.
   */

  void addImplicationsUsingEqualityAndEqualityList(TNode eq, OrderedSet& eqSet);
  void addImplicationsUsingEqualityAndLeqList(TNode eq, OrderedSet& leqSet);
  void addImplicationsUsingEqualityAndGeqList(TNode eq, OrderedSet& geqSet);

  void addImplicationsUsingLeqAndEqualityList(TNode leq, OrderedSet& eqSet);
  void addImplicationsUsingLeqAndLeqList(TNode leq, OrderedSet& leqSet);
  void addImplicationsUsingLeqAndGeqList(TNode leq, OrderedSet& geqSet);

  void addImplicationsUsingGeqAndEqualityList(TNode geq, OrderedSet& eqSet);
  void addImplicationsUsingGeqAndLeqList(TNode geq, OrderedSet& leqSet);
  void addImplicationsUsingGeqAndGeqList(TNode geq, OrderedSet& geqSet);

};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
