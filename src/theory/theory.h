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
#include "expr/command.h"
#include "theory/valuation.h"
#include "theory/substitutions.h"
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

/**
 * Information about an assertion for the theories.
 */
struct Assertion {

  /** The assertion */
  Node assertion;
  /** Has this assertion been preregistered with this theory */
  bool isPreregistered;

  Assertion(TNode assertion, bool isPreregistered)
  : assertion(assertion), isPreregistered(isPreregistered) {}

  /**
   * Convert the assertion to a TNode.
   */
  operator TNode () const {
    return assertion;
  }

  /**
   * Convert the assertion to a Node.
   */
  operator Node () const {
    return assertion;
  }
};

/**
 * A pair of terms a theory cares about.
 */
struct CarePair {
  TNode a, b;
  TheoryId theory;
  CarePair(TNode a, TNode b, TheoryId theory) 
  : a(a), b(b), theory(theory) {}
};

/**
 * A set of care pairs.
 */
typedef std::vector<CarePair> CareGraph;

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
   * An integer identifying the type of the theory
   */
  TheoryId d_id;

  /**
   * The context for the Theory.
   */
  context::Context* d_context;

  /**
   * The user context for the Theory.
   */
  context::UserContext* d_userContext;

  /**
   * The assertFact() queue.
   *
   * These can not be TNodes as some atoms (such as equalities) are sent
   * across theories without being stored in a global map.
   */
  context::CDList<Assertion> d_facts;

  /** Index into the head of the facts list */
  context::CDO<unsigned> d_factsHead;

  /**
   * Add shared term to the theory.
   */
  void addSharedTermInternal(TNode node);

  /**
   * Indices for splitting on the shared terms.
   */
  context::CDO<unsigned> d_sharedTermsIndex;

protected:

  /** 
   * A list of shared terms that the theory has.
   */
  context::CDList<TNode> d_sharedTerms;

  /**
   * Construct a Theory.
   */
  Theory(TheoryId id, context::Context* context, context::UserContext* userContext,
         OutputChannel& out, Valuation valuation) throw() :
    d_id(id),
    d_context(context),
    d_userContext(userContext),
    d_facts(context),
    d_factsHead(context, 0),
    d_sharedTermsIndex(context, 0),
    d_sharedTerms(context),
    d_out(&out),
    d_valuation(valuation)
  {
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
   * Returns the next assertion in the assertFact() queue.
   *
   * @return the next assertion in the assertFact() queue
   */
  Assertion get() {
    Assert( !done(), "Theory`() called with assertion queue empty!" );

    // Get the assertion
    Assertion fact = d_facts[d_factsHead];
    d_factsHead = d_factsHead + 1;
    Trace("theory") << "Theory::get() => " << fact << " (" << d_facts.size() - d_factsHead << " left)" << std::endl;
    if(Dump.isOn("state")) {
      Dump("state") << AssertCommand(fact.assertion.toExpr()) << std::endl;
    }
        
    return fact;
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the beginning of the fact queue
   */
  context::CDList<Assertion>::const_iterator facts_begin() const {
    return d_facts.begin();
  }

  /**
   * Provides access to the facts queue, primarily intended for theory
   * debugging purposes.
   *
   * @return the iterator to the end of the fact queue
   */
  context::CDList<Assertion>::const_iterator facts_end() const {
    return d_facts.end();
  }

  /**
   * The theory that owns the uninterpreted sort.
   */
  static TheoryId d_uninterpretedSortOwner;

public:

  /**
   * Return the ID of the theory responsible for the given type.
   */
  static inline TheoryId theoryOf(TypeNode typeNode) {
    TheoryId id;
    if (typeNode.getKind() == kind::TYPE_CONSTANT) {
      id = typeConstantToTheoryId(typeNode.getConst<TypeConstant>());
    } else {
      id = kindToTheoryId(typeNode.getKind());
    }
    if (id == THEORY_BUILTIN) {
      return d_uninterpretedSortOwner;
    }
    return id;
  }


  /**
   * Returns the ID of the theory responsible for the given node.
   */
  static inline TheoryId theoryOf(TNode node) {
    // Constants, variables, 0-ary constructors
    if (node.getMetaKind() == kind::metakind::VARIABLE || node.getMetaKind() == kind::metakind::CONSTANT) {
      return theoryOf(node.getType());
    }
    // Equality is owned by the theory that owns the domain
    if (node.getKind() == kind::EQUAL) {
      return theoryOf(node[0].getType());
    }
    // Regular nodes are owned by the kind
    return kindToTheoryId(node.getKind());
  }

  /**
   * Set the owner of the uninterpreted sort.
   */
  static void setUninterpretedSortOwner(TheoryId theory) {
    d_uninterpretedSortOwner = theory;
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
   * with FULL_EFFORT.
   */
  enum Effort {
    MIN_EFFORT = 0,
    QUICK_CHECK = 10,
    STANDARD = 50,
    FULL_EFFORT = 100,
    COMBINATION = 150
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
    { return e == FULL_EFFORT; }
  static inline bool combination(Effort e) CVC4_CONST_FUNCTION 
    { return e == COMBINATION; }

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
   * Get the context associated to this Theory.
   */
  context::UserContext* getUserContext() const {
    return d_userContext;
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
   * Assert a fact in the current context.
   */
  void assertFact(TNode assertion, bool isPreregistered) {
    Trace("theory") << "Theory<" << getId() << ">::assertFact[" << d_context->getLevel() << "](" << assertion << ", " << (isPreregistered ? "true" : "false") << ")" << std::endl;
    d_facts.push_back(Assertion(assertion, isPreregistered));
  }

  /**
   * This method is called to notify a theory that the node n should
   * be considered a "shared term" by this theory
   */
  virtual void addSharedTerm(TNode n) { }

  /**
   * The function should compute the care graph over the shared terms.
   * The default function returns all the pairs among the shared variables.
   */
  virtual void computeCareGraph(CareGraph& careGraph);

  /**
   * Return the status of two terms in the current context. Should be implemented in 
   * sub-theories to enable more efficient theory-combination.
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b) { return EQUALITY_UNKNOWN; }

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
   * (which was previously propagated by this theory).
   */
  virtual Node explain(TNode n) {
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
   * Statically learn from assertion "in," which has been asserted
   * true at the top level.  The theory should only add (via
   * ::operator<< or ::append()) to the "learned" builder---it should
   * *never* clear it.  It is a conjunction to add to the formula at
   * the top-level and may contain other theories' contributions.
   */
  virtual void staticLearning(TNode in, NodeBuilder<>& learned) { }

  enum SolveStatus {
    /** Atom has been solved  */
    SOLVE_STATUS_SOLVED,
    /** Atom has not been solved */
    SOLVE_STATUS_UNSOLVED,
    /** Atom is inconsistent */
    SOLVE_STATUS_CONFLICT
  };

  /**
   * Given a literal, add the solved substitutions to the map, if any.
   * The method should return true if the literal can be safely removed.
   */
  virtual SolveStatus solve(TNode in, SubstitutionMap& outSubstitutions) {
    if (in.getKind() == kind::EQUAL) {
      if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
        outSubstitutions.addSubstitution(in[0], in[1]);
        return SOLVE_STATUS_SOLVED;
      }
      if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
        outSubstitutions.addSubstitution(in[1], in[0]);
        return SOLVE_STATUS_SOLVED;
      }
      if (in[0].getMetaKind() == kind::metakind::CONSTANT && in[1].getMetaKind() == kind::metakind::CONSTANT) {
        if (in[0] != in[1]) {
          return SOLVE_STATUS_CONFLICT;
        }
      }
    }

    return SOLVE_STATUS_UNSOLVED;
  }

  /**
   * Given an atom of the theory coming from the input formula, this
   * method can be overridden in a theory implementation to rewrite
   * the atom into an equivalent form.  This is only called just
   * before an input atom to the engine.
   */
  virtual Node preprocess(TNode atom) { return atom; }

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
   * A Theory is called with postsolve exactly one time per user
   * check-sat.  postsolve() is called after the query has completed
   * (regardless of whether sat, unsat, or unknown), and after any
   * model-querying related to the query has been performed.
   * After this call, the theory will not get another check() or
   * propagate() call until presolve() is called again.  A Theory
   * cannot raise conflicts, add lemmas, or propagate literals during
   * postsolve().
   */
  virtual void postsolve() { }

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

  /** A set of theories */
  typedef uint32_t Set;

  /** A set of all theories */
  static const Set AllTheories = (1 << theory::THEORY_LAST) - 1;

  /** Add the theory to the set. If no set specified, just returns a singleton set */
  static inline Set setInsert(TheoryId theory, Set set = 0) {
    return set | (1 << theory);
  }

  /** Check if the set contains the theory */
  static inline bool setContains(TheoryId theory, Set set) {
    return set & (1 << theory);
  }

  static inline Set setComplement(Set a) {
    return (~a) & AllTheories;
  }

  static inline Set setIntersection(Set a, Set b) {
    return a & b;
  } 

  static inline Set setUnion(Set a, Set b) {
    return a | b;
  }

  /** a - b  */
  static inline Set setDifference(Set a, Set b) {
    return ((~b) & AllTheories) & a;
  }

  static inline std::string setToString(theory::Theory::Set theorySet) {
    std::stringstream ss;
    ss << "[";
    for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
      if (theory::Theory::setContains((theory::TheoryId)theoryId, theorySet)) {
        ss << (theory::TheoryId) theoryId << " ";
      }
    }
    ss << "]";
    return ss.str();
  }

};/* class Theory */

std::ostream& operator<<(std::ostream& os, Theory::Effort level);

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out,
                                const CVC4::theory::Theory& theory) {
  return out << theory.identify();
}

inline std::ostream& operator << (std::ostream& out, theory::Theory::SolveStatus status) {
  switch (status) {
  case theory::Theory::SOLVE_STATUS_SOLVED:
    out << "SOLVE_STATUS_SOLVED"; break;
  case theory::Theory::SOLVE_STATUS_UNSOLVED:
    out << "SOLVE_STATUS_UNSOLVED"; break;
  case theory::Theory::SOLVE_STATUS_CONFLICT:
    out << "SOLVE_STATUS_CONFLICT"; break;
  default:
    Unhandled();
  }
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
