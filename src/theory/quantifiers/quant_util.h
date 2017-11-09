/*********************                                                        */
/*! \file quant_util.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief quantifier util
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANT_UTIL_H
#define __CVC4__THEORY__QUANT_UTIL_H

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
  virtual unsigned needsModel( Theory::Effort e );
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
  virtual void check( Theory::Effort e, unsigned quant_e ) = 0;
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
  /** Pre register quantifier.
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory.
   */
  virtual void preRegisterQuantifier( Node q ) { }
  /** Register quantifier
   *
   * Called once for new quantified formulas that are
   * pre-registered by the quantifiers theory, after
   * internal ownership of quantified formulas is finalized.
   */
  virtual void registerQuantifier( Node q ) = 0;
  /** Assert node.
   *
   * Called when a quantified formula q is asserted to the quantifiers theory
   */
  virtual void assertNode(Node q) {}
  /* Get the next decision request.
   *
   * Identical to Theory::getNextDecisionRequest(...)
   */
  virtual Node getNextDecisionRequest( unsigned& priority ) { return TNode::null(); }
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
  //----------------------------general queries
  /** get currently used the equality engine */
  eq::EqualityEngine * getEqualityEngine();
  /** are n1 and n2 equal in the current used equality engine? */
  bool areEqual( TNode n1, TNode n2 );
  /** are n1 and n2 disequal in the current used equality engine? */
  bool areDisequal(TNode n1, TNode n2);
  /** get the representative of n in the current used equality engine */
  TNode getRepresentative( TNode n );
  /** get quantifiers engine that owns this module */
  QuantifiersEngine* getQuantifiersEngine() { return d_quantEngine; }
  /** get currently used term database */
  quantifiers::TermDb * getTermDatabase();
  /** get currently used term utility object */
  quantifiers::TermUtil * getTermUtil();
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
  * added a lemma
  * via a call to qe->addLemma. TODO: improve this contract #1163
  */
  virtual bool reset( Theory::Effort e ) = 0;
  /* Called for new quantifiers */
  virtual void registerQuantifier(Node q) = 0;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  virtual std::string identify() const = 0;
};

/** Arithmetic utilities regarding monomial sums.
 *
 * Note the following terminology:
 *
 *   We say Node c is a {monomial constant} (or m-constant) if either:
 *   (a) c is a constant Rational, or
 *   (b) c is null.
 *
 *   We say Node v is a {monomial variable} (or m-variable) if either:
 *   (a) v.getType().isReal() and v is not a constant, or
 *   (b) v is null.
 *
 *   For m-constant or m-variable t, we write [t] to denote 1 if t.isNull() and
 *   t otherwise.
 *
 *   A monomial m is a pair ( mvariable, mconstant ) of the form ( v, c ), which
 *   is interpreted as [c]*[v].
 *
 *   A {monmoial sum} msum is represented by a std::map< Node, Node > having
 *   key-value pairs of the form ( mvariable, mconstant ).
 *   It is interpreted as:
 *   [msum] = sum_{( v, c ) \in msum } [c]*[v]
 *   It is critical that this map is ordered so that operations like adding
 *   two monomial sums can be done efficiently. The ordering itself is not 
 *   important, and currently corresponds to the default ordering on Nodes.
 *
 * The following has utilities involving monmoial sums.
 *
 */
class QuantArith
{
public:
 /** get monomial
  *
  * If n = n[0]*n[1] where n[0] is constant and n[1] is not,
  * this function returns true, sets c to n[0] and v to n[1].
  */
 static bool getMonomial(Node n, Node& c, Node& v);

 /** get monomial
  *
  * If this function returns true, it adds the ( m-constant, m-variable )
  * pair corresponding to the monomial representation of n to the
  * monomial sum msum.
  *
  * This function returns false if the m-variable of n is already
  * present in n.
  */
 static bool getMonomial(Node n, std::map<Node, Node>& msum);

 /** get monomial sum for real-valued term n
  *
  * If this function returns true, it sets msum to a monmoial sum such that
  *   [msum] is equivalent to n
  *
  * This function may return false if n is not a sum of monomials
  * whose variables are pairwise unique.
  * If term n is in rewritten form, this function should always return true.
  */
 static bool getMonomialSum(Node n, std::map<Node, Node>& msum);

 /** get monmoial sum literal for literal lit
  *
  * If this function returns true, it sets msum to a monmoial sum such that
  *   [msum] <k> 0  is equivalent to lit[0] <k> lit[1]
  * where k is the Kind of lit, one of { EQUAL, GEQ }.
  *
  * This function may return false if either side of lit is not a sum
  * of monomials whose variables are pairwise unique on that side.
  * If literal lit is in rewritten form, this function should always return
  * true.
  */
 static bool getMonomialSumLit(Node lit, std::map<Node, Node>& msum);

 /** make node for monomial sum
  *
  * Make the Node corresponding to the interpretation of msum, [msum], where:
  *   [msum] = sum_{( v, c ) \in msum } [c]*[v]
  */
 static Node mkNode(std::map<Node, Node>& msum);

 /** make coefficent term
  *
  * Input coeff is a m-constant.
  * Returns the term t if coeff.isNull() or coeff*t otherwise.
  */
 static Node mkCoeffTerm(Node coeff, Node t);

 /** isolate variable v in constraint ([msum] <k> 0)
  *
  * If this function returns a value ret where ret != 0, then
  * veq_c is set to m-constant, and val is set to a term such that:
  *    If ret=1, then ([veq_c] * v <k> val) is equivalent to [msum] <k> 0.
  *   If ret=-1, then (val <k> [veq_c] * v) is equivalent to [msum] <k> 0.
  *   If veq_c is non-null, then it is a positive constant Rational.
  * The returned value of veq_c is only non-null if v has integer type.
  *
  * This function returns 0 indicating a failure if msum does not contain
  * a (non-zero) monomial having mvariable v.
  */
 static int isolate(
     Node v, std::map<Node, Node>& msum, Node& veq_c, Node& val, Kind k);

 /** isolate variable v in constraint ([msum] <k> 0)
  *
  * If this function returns a value ret where ret != 0, then veq
  * is set to a literal that is equivalent to ([msum] <k> 0), and:
  *    If ret=1, then veq is of the form ( v <k> val) if veq_c.isNull(),
  *                   or ([veq_c] * v <k> val) if !veq_c.isNull().
  *   If ret=-1, then veq is of the form ( val <k> v) if veq_c.isNull(),
  *                   or (val <k> [veq_c] * v) if !veq_c.isNull().
  * If doCoeff = false or v does not have Integer type, then veq_c is null.
  *
  * This function returns 0 indiciating a failure if msum does not contain
  * a (non-zero) monomial having variable v, or if veq_c must be non-null
  * for an integer constraint and doCoeff is false.
  */
 static int isolate(Node v,
                    std::map<Node, Node>& msum,
                    Node& veq,
                    Kind k,
                    bool doCoeff = false);

 /** solve equality lit for variable
  *
  * If return value ret is non-null, then:
  *    v = ret is equivalent to lit.
  *
  * This function may return false if lit does not contain v,
  * or if lit is an integer equality with a coefficent on v,
  * e.g. 3*v = 7.
  */
 static Node solveEqualityFor(Node lit, Node v);

 /** decompose real-valued term n
 *
 * If this function returns true, then
 *   ([coeff]*v + rem) is equivalent to n
 * where coeff is non-zero m-constant.
 *
 * This function will return false if n is not a monomial sum containing
 * a monomial with factor v.
 */
 static bool decompose(Node n, Node v, Node& coeff, Node& rem);

 /** return the rewritten form of (UMINUS t) */
 static Node negate(Node t);

 /** return the rewritten form of (PLUS t (CONST_RATIONAL i)) */
 static Node offset(Node t, int i);

 /** debug print for a monmoial sum, prints to Trace(c) */
 static void debugPrintMonomialSum(std::map<Node, Node>& msum, const char* c);
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

}
}

#endif /* __CVC4__THEORY__QUANT_UTIL_H */
