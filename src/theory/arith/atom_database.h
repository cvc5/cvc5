/*********************                                                        */
/*! \file atom_database.h
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
 ** \brief ArithAtomDatabase keeps a database of the arithmetic atoms.
 ** Importantly, ArithAtomDatabase also handles unate propagations,
 ** i.e. it constructs implications of the form
 ** "if x < c and c < b, then x < b" (where c and b are constants).
 **
 ** ArithAtomDatabase detects unate implications amongst the atoms
 ** associated with the theory of arithmetic and informs the SAT solver of the
 ** implication. A unate implication is an implication of the form:
 **   "if x < c and c < b, then x < b" (where c and b are constants).
 ** Unate implications are always 2-SAT clauses.
 ** ArithAtomDatabase sends the implications to the SAT solver in an
 ** online fashion.
 ** This means that atoms may be added during solving or before.
 **
 ** ArithAtomDatabase maintains sorted lists containing all atoms associated
 ** for each unique left hand side, the "x" in the inequality "x < c".
 ** The lists are sorted by the value of the right hand side which must be a
 ** rational constant.
 **
 ** ArithAtomDatabase tries to send out a minimal number of additional
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

#ifndef __CVC4__THEORY__ARITH__ARITH_ATOM_DATABASE_H
#define __CVC4__THEORY__ARITH__ARITH_ATOM_DATABASE_H

#include "expr/node.h"
#include "context/context.h"

#include "theory/output_channel.h"
#include "theory/arith/ordered_set.h"

#include <ext/hash_map>

namespace CVC4 {
namespace theory {
namespace arith {

class ArithAtomDatabase {
private:
  /**
   * OutputChannel for the theory of arithmetic.
   * The propagator uses this to pass implications back to the SAT solver.
   */
  OutputChannel& d_arithOut;

  struct VariablesSets {
    BoundValueSet d_boundValueSet;
    EqualValueSet d_eqValueSet;
  };

  typedef __gnu_cxx::hash_map<TNode, VariablesSets, NodeHashFunction> NodeToSetsMap;
  NodeToSetsMap d_setsMap;

public:
  ArithAtomDatabase(context::Context* cxt, OutputChannel& arith);

  /**
   * Adds an atom to the propagator.
   * Any resulting lemmas will be output via d_arithOut.
   */
  void addAtom(TNode atom);

  /** Returns true if v has been added as a left hand side in an atom */
  bool hasAnyAtoms(TNode v) const;

  bool containsLiteral(TNode lit) const;
  bool containsAtom(TNode atom) const;
  bool containsEquality(TNode atom) const;
  bool containsLeq(TNode atom) const;
  bool containsGeq(TNode atom) const;



private:
  VariablesSets& getVariablesSets(TNode left);
  BoundValueSet& getBoundValueSet(TNode left);
  EqualValueSet& getEqualValueSet(TNode left);

  const VariablesSets& getVariablesSets(TNode left) const;
  const BoundValueSet& getBoundValueSet(TNode left) const;
  const EqualValueSet& getEqualValueSet(TNode left) const;

  /** Sends an implication (=> a b) to the PropEngine via d_arithOut. */
  void addImplication(TNode a, TNode b);

  /** Check to make sure an lhs has been properly set-up. */
  bool leftIsSetup(TNode left) const;

  /** Initializes the lists associated with a unique lhs. */
  void setupLefthand(TNode left);


  /**
   * The addImplicationsUsingKAndJList(...)
   * functions are the work horses of the unate part of ArithAtomDatabase.
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

  void addImplicationsUsingEqualityAndEqualityValues(TNode eq);
  void addImplicationsUsingEqualityAndBoundValues(TNode eq);

  void addImplicationsUsingLeqAndEqualityValues(TNode leq);
  void addImplicationsUsingLeqAndBoundValues(TNode leq);

  void addImplicationsUsingGeqAndEqualityValues(TNode geq);
  void addImplicationsUsingGeqAndBoundValues(TNode geq);

  bool hasBoundValueEntry(TNode n);

  Node getImpliedUpperBoundUsingLeq(TNode leq, bool weaker) const;
  Node getImpliedUpperBoundUsingLT(TNode lt, bool weaker) const;

  Node getImpliedLowerBoundUsingGeq(TNode geq, bool weaker) const;
  Node getImpliedLowerBoundUsingGT(TNode gt, bool weaker) const;

public:
  Node getBestImpliedUpperBound(TNode upperBound) const;
  Node getBestImpliedLowerBound(TNode lowerBound) const;


  Node getWeakerImpliedUpperBound(TNode upperBound) const;
  Node getWeakerImpliedLowerBound(TNode lowerBound) const;
};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARITH_ATOM_DATABASE_H */
