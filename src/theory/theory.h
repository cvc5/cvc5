/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Base of the theory interface.
 **
 ** Base of the theory interface.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_H
#define __CVC4__THEORY__THEORY_H

#include "expr/node.h"
#include "expr/attribute.h"
#include "theory/valuation.h"
#include "theory/output_channel.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "util/options.h"

#include <string>
#include <iostream>

namespace CVC4 {

class TheoryEngine;

namespace theory {

/** Tag for the "newFact()-has-been-called-in-this-context" flag on Nodes */
struct AssertedAttrTag {};
/** The "newFact()-has-been-called-in-this-context" flag on Nodes */
typedef CVC4::expr::CDAttribute<AssertedAttrTag, bool> Asserted;

/**
 * Base class for T-solvers.  Abstract DPLL(T).
 *
 * This is essentially an interface class.  The TheoryEngine has
 * pointers to Theory.  Note that only one specific Theory type (e.g.,
 * TheoryUF) can exist per NodeManager, because of how the
 * RegisteredAttr works.  (If you need multiple instances of the same
 * theory, you'll have to write a multiplexed theory that dispatches
 * all calls to them.)
 */
class Theory {
private:

  friend class ::CVC4::TheoryEngine;

  // Disallow default construction, copy, assignment.
  Theory() CVC4_UNUSED;
  Theory(const Theory&) CVC4_UNUSED;
  Theory& operator=(const Theory&) CVC4_UNUSED;

  /**
   * A unique integer identifying the theory
   */
  TheoryId d_id;

  /**
   * The context for the Theory.
   */
  context::Context* d_context;

  /**
   * The assertFact() queue.
   *
   * These can not be TNodes as some atoms (such as equalities) are sent
   * across theories without being stored in a global map.
   */
  context::CDList<Node> d_facts;

  /** Index into the head of the facts list */
  context::CDO<unsigned> d_factsHead;

protected:

  /**
   * Construct a Theory.
   */
  Theory(TheoryId id, context::Context* ctxt, OutputChannel& out, Valuation valuation) throw() :
    d_id(id),
    d_context(ctxt),
    d_facts(ctxt),
    d_factsHead(ctxt, 0),
    d_out(&out),
    d_valuation(valuation) {
  }

  /**
   * This is called at shutdown time by the TheoryEngine, just before
   * destruction.  It is important because there are destruction
   * ordering issues between PropEngine and Theory (based on what
   * hard-links to Nodes are outstanding).  As the fact queue might be
   * nonempty, we ensure here that it's clear.  If you overload this,
   * you must make an explicit call here to this->Theory::shutdown()
   * too.
   */
  virtual void shutdown() { }

  /**
   * The output channel for the Theory.
   */
  OutputChannel* d_out;

  /**
   * The valuation proxy for the Theory to communicate back with the
   * theory engine (and other theories).
   */
  Valuation d_valuation;

  /**
   * Returns the next atom in the assertFact() queue.  Guarantees that
   * registerTerm() has been called on the theory specific subterms.
   *
   * @return the next atom in the assertFact() queue.
   */
  TNode get() {
    Assert( !done(), "Theory::get() called with assertion queue empty!" );
    TNode fact = d_facts[d_factsHead];
    d_factsHead = d_factsHead + 1;
    Debug("theory") << "Theory::get() => " << fact
                    << "(" << d_facts.size() << " left)" << std::endl;
    d_out->newFact(fact);
    return fact;
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the beginning of the fact queue
   */
  context::CDList<Node>::const_iterator facts_begin() const {
    return d_facts.begin();
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the end of the fact queue
   */
  context::CDList<Node>::const_iterator facts_end() const {
    return d_facts.end();
  }

public:

  static inline TheoryId theoryOf(TypeNode typeNode) {
    if (typeNode.getKind() == kind::TYPE_CONSTANT) {
      return typeConstantToTheoryId(typeNode.getConst<TypeConstant>());
    } else {
      return kindToTheoryId(typeNode.getKind());
    }
  }

  /**
   * Returns the theory responsible for the node.
   */
  static inline TheoryId theoryOf(TNode node) {
    if (node.getMetaKind() == kind::metakind::VARIABLE || node.getMetaKind() == kind::metakind::CONSTANT) {
      // Constants, variables, 0-ary constructors
      return theoryOf(node.getType());
    } else {
      // Regular nodes
      return kindToTheoryId(node.getKind());
    }
  }

  /**
   * Checks if the node is a leaf node of this theory
   */
  inline bool isLeaf(TNode node) const {
    return node.getNumChildren() == 0 || theoryOf(node) != d_id;
  }

  /**
   * Checks if the node is a leaf node of a theory.
   */
  inline static bool isLeafOf(TNode node, TheoryId theoryId) {
    return node.getNumChildren() == 0 || theoryOf(node) != theoryId;
  }

  /**
   * Returns true if the assertFact queue is empty
   */
  bool done() throw() {
    return d_factsHead == d_facts.size();
  }

  /**
   * Destructs a Theory.  This implementation does nothing, but we
   * need a virtual destructor for safety in case subclasses have a
   * destructor.
   */
  virtual ~Theory() {
  }

  /**
   * Subclasses of Theory may add additional efforts.  DO NOT CHECK
   * equality with one of these values (e.g. if STANDARD xxx) but
   * rather use range checks (or use the helper functions below).
   * Normally we call QUICK_CHECK or STANDARD; at the leaves we call
   * with MAX_EFFORT.
   */
  enum Effort {
    MIN_EFFORT = 0,
    QUICK_CHECK = 10,
    STANDARD = 50,
    FULL_EFFORT = 100
  };/* enum Effort */

  // simple, useful predicates for effort values
  static inline bool minEffortOnly(Effort e) CVC4_CONST_FUNCTION
    { return e == MIN_EFFORT; }
  static inline bool quickCheckOrMore(Effort e) CVC4_CONST_FUNCTION
    { return e >= QUICK_CHECK; }
  static inline bool quickCheckOnly(Effort e) CVC4_CONST_FUNCTION
    { return e >= QUICK_CHECK && e <  STANDARD; }
  static inline bool standardEffortOrMore(Effort e) CVC4_CONST_FUNCTION
    { return e >= STANDARD; }
  static inline bool standardEffortOnly(Effort e) CVC4_CONST_FUNCTION
    { return e >= STANDARD && e <  FULL_EFFORT; }
  static inline bool fullEffort(Effort e) CVC4_CONST_FUNCTION
    { return e >= FULL_EFFORT; }

  /**
   * Get the id for this Theory.
   */
  TheoryId getId() const {
    return d_id;
  }

  /**
   * Get the context associated to this Theory.
   */
  context::Context* getContext() const {
    return d_context;
  }

  /**
   * Set the output channel associated to this theory.
   */
  void setOutputChannel(OutputChannel& out) {
    d_out = &out;
  }

  /**
   * Get the output channel associated to this theory.
   */
  OutputChannel& getOutputChannel() {
    return *d_out;
  }

  /**
   * Pre-register a term.  Done one time for a Node, ever.
   */
  virtual void preRegisterTerm(TNode) { }

  /**
   * Register a term.
   *
   * When get() is called to get the next thing off the theory queue,
   * setup() is called on its subterms (in TheoryEngine).  Then setup()
   * is called on this node.
   *
   * This is done in a "context escape" -- that is, at context level 0.
   * setup() MUST NOT MODIFY context-dependent objects that it hasn't
   * itself just created.
   */
  virtual void registerTerm(TNode) { }

  /**
   * Assert a fact in the current context.
   */
  void assertFact(TNode node) {
    Debug("theory") << "Theory::assertFact(" << node << ")" << std::endl;
    d_facts.push_back(node);
  }

  /**
   * This method is called to notify a theory that the node n should
   * be considered a "shared term" by this theory
   */
  virtual void addSharedTerm(TNode n) { }

  /**
   * This method is called by the shared term manager when a shared
   * term lhs which this theory cares about (either because it
   * received a previous addSharedTerm call with lhs or because it
   * received a previous notifyEq call with lhs as the second
   * argument) becomes equal to another shared term rhs.  This call
   * also serves as notice to the theory that the shared term manager
   * now considers rhs the representative for this equivalence class
   * of shared terms, so future notifications for this class will be
   * based on rhs not lhs.
   */
  virtual void notifyEq(TNode lhs, TNode rhs) { }

  /**
   * Check the current assignment's consistency.
   *
   * An implementation of check() is required to either:
   * - return a conflict on the output channel,
   * - be interrupted,
   * - throw an exception
   * - or call get() until done() is true.
   */
  virtual void check(Effort level = FULL_EFFORT) { }

  /**
   * T-propagate new literal assignments in the current context.
   */
  virtual void propagate(Effort level = FULL_EFFORT) { }

  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).  Report
   * explanations to an output channel.
   */
  virtual void explain(TNode n) {
    Unimplemented("Theory %s propagated a node but doesn't implement the "
                  "Theory::explain() interface!", identify().c_str());
  }

  /**
   * Return the value of a node (typically used after a ).  If the
   * theory supports model generation but has no value for this node,
   * it should return Node::null().  If the theory doesn't support
   * model generation at all, or usually would but doesn't in its
   * current state, it should throw an exception saying so.
   *
   * The TheoryEngine is passed in so that you can recursively request
   * values for the Node's children.  This is important because the
   * TheoryEngine takes care of simple cases (metakind CONSTANT,
   * Boolean-valued VARIABLES, ...) and can dispatch to other theories
   * if that's necessary.  Only call your own getValue() recursively
   * if you *know* that you are responsible handle the Node you're
   * asking for; other theories can use your types, so be careful
   * here!  To be safe, it's best to delegate back to the
   * TheoryEngine (by way of the Valuation proxy object, which avoids
   * direct dependence on TheoryEngine).
   *
   * Usually, you need to handle at least the two cases of EQUAL and
   * VARIABLE---EQUAL in case a value of yours is on the LHS of an
   * EQUAL, and VARIABLE for variables of your types.  You also need
   * to support any operators that can survive your rewriter.  You
   * don't need to handle constants, as they are handled by the
   * TheoryEngine.
   *
   * There are some gotchas here.  The user may be requesting the
   * value of an expression that wasn't part of the satisfiable
   * assertion, or has been declared since.  If you don't have a value
   * and suspect this situation is the case, return Node::null()
   * rather than throwing an exception.
   */
  virtual Node getValue(TNode n) {
    Unimplemented("Theory %s doesn't support Theory::getValue interface",
                  identify().c_str());
    return Node::null();
  }

  /**
   * The theory should only add (via .operator<< or .append()) to the
   * "learned" builder.  It is a conjunction to add to the formula at
   * the top-level and may contain other theories' contributions.
   */
  virtual void staticLearning(TNode in, NodeBuilder<>& learned) { }

  /**
   * A Theory is called with presolve exactly one time per user
   * check-sat.  presolve() is called after preregistration,
   * rewriting, and Boolean propagation, (other theories'
   * propagation?), but the notified Theory has not yet had its
   * check() or propagate() method called.  A Theory may empty its
   * assertFact() queue using get().  A Theory can raise conflicts,
   * add lemmas, and propagate literals during presolve().
   */
  virtual void presolve() { }

  /**
   * Notification sent to the theory wheneven the search restarts.
   * Serves as a good time to do some clean-up work, and you can
   * assume you're at DL 0 for the purposes of Contexts.  This function
   * should not use the output channel.
   */
  virtual void notifyRestart() { }

  /**
   * Identify this theory (for debugging, dynamic configuration,
   * etc..)
   */
  virtual std::string identify() const = 0;

};/* class Theory */

std::ostream& operator<<(std::ostream& os, Theory::Effort level);

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out,
                                const CVC4::theory::Theory& theory) {
  return out << theory.identify();
}

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
