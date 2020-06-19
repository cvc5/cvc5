/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANT_UTIL_H
#define CVC4__THEORY__QUANT_UTIL_H

#include <iostream>
#include <map>
#include <vector>

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers {
  class TermDb;
  class TermUtil;
}

/** QuantifiersModule class
*
* This is the virtual class for defining subsolvers of the quantifiers theory.
* It has a similar interface to a Theory object.
*/
class QuantifiersModule {
 public:
  /** effort levels for quantifiers modules check */
  enum QEffort
  {
    // conflict effort, for conflict-based instantiation
    QEFFORT_CONFLICT,
    // standard effort, for heuristic instantiation
    QEFFORT_STANDARD,
    // model effort, for model-based instantiation
    QEFFORT_MODEL,
    // last call effort, for last resort techniques
    QEFFORT_LAST_CALL,
    // none
    QEFFORT_NONE,
  };

 public:
  QuantifiersModule( QuantifiersEngine* qe ) : d_quantEngine( qe ){}
  virtual ~QuantifiersModule(){}
  /** Presolve.
   *
   * Called at the beginning of check-sat call.
   */
  virtual void presolve() {}
  /** Needs check.
   *
   * Returns true if this module wishes a call to be made
   * to check(e) during QuantifiersEngine::check(e).
   */
  virtual bool needsCheck( Theory::Effort e ) { return e>=Theory::EFFORT_LAST_CALL; }
  /** Needs model.
   *
   * Whether this module needs a model built during a
   * call to QuantifiersEngine::check(e)
   * It returns one of QEFFORT_* from quantifiers_engine.h,
   * which specifies the quantifiers effort in which it requires the model to
   * be built.
   */
  virtual QEffort needsModel(Theory::Effort e);
  /** Reset.
   *
   * Called at the beginning of QuantifiersEngine::check(e).
   */
  virtual void reset_round( Theory::Effort e ){}
  /** Check.
   *
   *   Called during QuantifiersEngine::check(e) depending
   *   if needsCheck(e) returns true.
   */
  virtual void check(Theory::Effort e, QEffort quant_e) = 0;
  /** Check complete?
   *
   * Returns false if the module's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   *
   * This is called just before the quantifiers engine will return
   * with no lemmas added during a LAST_CALL effort check.
   */
  virtual bool checkComplete() { return true; }
  /** Check was complete for quantified formula q
   *
   * If for each quantified formula q, some module returns true for
   * checkCompleteFor( q ),
   * and no lemmas are added by the quantifiers theory, then we may answer
   * "sat", unless
   * we are incomplete for other reasons.
   */
  virtual bool checkCompleteFor( Node q ) { return false; }
  /** Check ownership
   *
   * Called once for new quantified formulas that are registered by the
   * quantifiers theory. The primary purpose of this function is to establish
   * if this module is the owner of quantified formula q.
   */
  virtual void checkOwnership(Node q) {}
  /** Register quantifier
   *
   * Called once for new quantified formulas q that are pre-registered by the
   * quantifiers theory, after internal ownership of quantified formulas is
   * finalized. This does context-independent initialization of this module
   * for quantified formula q.
   */
  virtual void registerQuantifier(Node q) {}
  /** Pre-register quantifier
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory, after
   * internal ownership of quantified formulas is finalized.
   */
  virtual void preRegisterQuantifier(Node q) {}
  /** Assert node.
   *
   * Called when a quantified formula q is asserted to the quantifiers theory
   */
  virtual void assertNode(Node q) {}
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  //----------------------------general queries
  /** get currently used the equality engine */
  eq::EqualityEngine* getEqualityEngine() const;
  /** are n1 and n2 equal in the current used equality engine? */
  bool areEqual(TNode n1, TNode n2) const;
  /** are n1 and n2 disequal in the current used equality engine? */
  bool areDisequal(TNode n1, TNode n2) const;
  /** get the representative of n in the current used equality engine */
  TNode getRepresentative(TNode n) const;
  /** get quantifiers engine that owns this module */
  QuantifiersEngine* getQuantifiersEngine() const;
  /** get currently used term database */
  quantifiers::TermDb* getTermDatabase() const;
  /** get currently used term utility object */
  quantifiers::TermUtil* getTermUtil() const;
  //----------------------------end general queries
 protected:
  /** pointer to the quantifiers engine that owns this module */
  QuantifiersEngine* d_quantEngine;
};/* class QuantifiersModule */

/** Quantifiers utility
*
* This is a lightweight version of a quantifiers module that does not implement
* methods
* for checking satisfiability.
*/
class QuantifiersUtil {
public:
  QuantifiersUtil(){}
  virtual ~QuantifiersUtil(){}
  /* reset
  * Called at the beginning of an instantiation round
  * Returns false if the reset failed. When reset fails, the utility should have
  * added a lemma via a call to qe->addLemma. TODO: improve this contract #1163
  */
  virtual bool reset( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier(Node q) = 0;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  /** Check complete?
   *
   * Returns false if the utility's reasoning was globally incomplete
   * (e.g. "sat" must be replaced with "incomplete").
   */
  virtual bool checkComplete() { return true; }
};

class QuantPhaseReq
{
private:
  /** helper functions compute phase requirements */
  void computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs );
public:
  QuantPhaseReq(){}
  QuantPhaseReq( Node n, bool computeEq = false );
  ~QuantPhaseReq(){}
  void initialize( Node n, bool computeEq );
  /** is phase required */
  bool isPhaseReq( Node lit ) { return d_phase_reqs.find( lit )!=d_phase_reqs.end(); }
  /** get phase requirement */
  bool getPhaseReq( Node lit ) { return d_phase_reqs.find( lit )==d_phase_reqs.end() ? false : d_phase_reqs[ lit ]; }
  /** phase requirements for each quantifier for each instantiation literal */
  std::map< Node, bool > d_phase_reqs;
  std::map< Node, bool > d_phase_reqs_equality;
  std::map< Node, Node > d_phase_reqs_equality_term;

  static void getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
  static void getEntailPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol );
};

/** EqualityQuery
* This is a wrapper class around equality engine.
*/
class EqualityQuery : public QuantifiersUtil {
public:
  EqualityQuery(){}
  virtual ~EqualityQuery(){};
  /** extends engine */
  virtual bool extendsEngine() { return false; }
  /** contains term */
  virtual bool hasTerm( Node a ) = 0;
  /** get the representative of the equivalence class of a */
  virtual Node getRepresentative( Node a ) = 0;
  /** returns true if a and b are equal in the current context */
  virtual bool areEqual( Node a, Node b ) = 0;
  /** returns true is a and b are disequal in the current context */
  virtual bool areDisequal( Node a, Node b ) = 0;
  /** get the equality engine associated with this query */
  virtual eq::EqualityEngine* getEngine() = 0;
  /** get the equivalence class of a */
  virtual void getEquivalenceClass( Node a, std::vector< Node >& eqc ) = 0;
  /** get the term that exists in EE that is congruent to f with args (f is
   * returned by TermDb::getMatchOperator(...)) */
  virtual TNode getCongruentTerm( Node f, std::vector< TNode >& args ) = 0;
};/* class EqualityQuery */

/** Types of bounds that can be inferred for quantified formulas */
enum BoundVarType
{
  // a variable has a finite bound because it has finite cardinality
  BOUND_FINITE,
  // a variable has a finite bound because it is in an integer range, e.g.
  //   forall x. u <= x <= l => P(x)
  BOUND_INT_RANGE,
  // a variable has a finite bound because it is a member of a set, e.g.
  //   forall x. x in S => P(x)
  BOUND_SET_MEMBER,
  // a variable has a finite bound because only a fixed set of terms are
  // relevant for it in the domain of the quantified formula, e.g.
  //   forall x. ( x = t1 OR ... OR x = tn ) => P(x)
  BOUND_FIXED_SET,
  // a bound has not been inferred for the variable
  BOUND_NONE
};
}
}

#endif /* CVC4__THEORY__QUANT_UTIL_H */
