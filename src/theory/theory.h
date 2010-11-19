/*********************                                                        */
/*! \file theory.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, taking, barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include "theory/output_channel.h"
#include "context/context.h"

#include <deque>
#include <list>

#include <string>
#include <iostream>

namespace CVC4 {

class TheoryEngine;

namespace theory {

// rewrite cache support
template <bool topLevel> struct PreRewriteCacheTag {};
typedef expr::Attribute<PreRewriteCacheTag<true>, Node> PreRewriteCacheTop;
typedef expr::Attribute<PreRewriteCacheTag<false>, Node> PreRewriteCache;
template <bool topLevel> struct PostRewriteCacheTag {};
typedef expr::Attribute<PostRewriteCacheTag<true>, Node> PostRewriteCacheTop;
typedef expr::Attribute<PostRewriteCacheTag<false>, Node> PostRewriteCache;

/**
 * Instances of this class serve as response codes from
 * Theory::preRewrite() and Theory::postRewrite().  Instances of
 * derived classes RewriteComplete(n), RewriteAgain(n), and
 * FullRewriteNeeded(n) should be used, giving self-documenting
 * rewrite behavior.
 */
class RewriteResponse {
protected:
  enum Status { DONE, REWRITE, REWRITE_FULL };

  RewriteResponse(Status s, Node n) : d_status(s), d_node(n) {}

private:
  const Status d_status;
  const Node d_node;

public:
  bool isDone() const { return d_status == DONE; }
  bool needsMoreRewriting() const { return d_status != DONE; }
  bool needsFullRewriting() const { return d_status == REWRITE_FULL; }
  Node getNode() const { return d_node; }
};/* class RewriteResponse */

/**
 * Signal that (pre,post)rewriting of the Node is complete at n.  Note
 * that if theory A returns this, and the Node is in another theory B,
 * theory B will still be called on to pre- or postrewrite it.
 */
class RewriteComplete : public RewriteResponse {
public:
  RewriteComplete(Node n) : RewriteResponse(DONE, n) {}
};/* class RewriteComplete */

/**
 * Return n, but request additional rewriting of it; if this is
 * returned from preRewrite(), this re-preRewrite()'s the Node.  If
 * this is returned from postRewrite(), this re-postRewrite()'s the
 * Node, but does NOT re-preRewrite() it, nor does it rewrite the
 * Node's children.
 *
 * Note that this is the behavior if a theory returns
 * RewriteComplete() for a Node belonging to another theory.
 */
class RewriteAgain : public RewriteResponse {
public:
  RewriteAgain(Node n) : RewriteResponse(REWRITE, n) {}
};/* class RewriteAgain */

/**
 * Return n, but request an additional complete rewriting pass over
 * it.  This has the same behavior as RewriteAgain() for
 * pre-rewriting.  However, in post-rewriting, FullRewriteNeeded will
 * _completely_ pre- and post-rewrite the term and the term's children
 * (though it will use the cache to elide what calls it can).  Use
 * with caution; it has bad effects on performance.  This might be
 * useful if theory A rewrites a term into something quite different,
 * and certain child nodes might belong to another theory whose normal
 * form is unknown to theory A.  For example, if the builtin theory
 * post-rewrites (DISTINCT a b c) into pairwise NOT EQUAL expressions,
 * the theories owning a, b, and c might need to rewrite that EQUAL.
 * (This came up, but the fix was to rewrite DISTINCT in
 * pre-rewriting, obviating the problem.  See bug #168.)
 */
class FullRewriteNeeded : public RewriteResponse {
public:
  FullRewriteNeeded(Node n) : RewriteResponse(REWRITE_FULL, n) {}
};/* class FullRewriteNeeded */

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

  /**
   * Disallow default construction.
   */
  Theory();

  /**
   * A unique integer identifying the theory
   */
  int d_id;

  /**
   * The context for the Theory.
   */
  context::Context* d_context;

  /**
   * The assertFact() queue.
   *
   * This queue MUST be emptied by ANY call to check() at ANY effort
   * level.  In debug builds, this is checked.  On backjump we clear
   * the fact queue (see FactsResetter, below).
   *
   * These can safely be TNodes because the literal map maintained in
   * the SAT solver keeps them live.  As an added benefit, if we have
   * them as TNodes, dtors are cheap (optimized away?).
   */
  std::deque<TNode> d_facts;

  /** Helper class to reset the fact queue on pop(). */
  class FactsResetter : public context::ContextNotifyObj {
    Theory& d_thy;

  public:
    FactsResetter(Theory& thy) :
      context::ContextNotifyObj(thy.d_context),
      d_thy(thy) {
    }

    void notify() {
      d_thy.d_facts.clear();
    }
  } d_factsResetter;

  friend class FactsResetter;

protected:

  /**
   * Construct a Theory.
   */
  Theory(int id, context::Context* ctxt, OutputChannel& out) throw() :
    d_id(id),
    d_context(ctxt),
    d_facts(),
    d_factsResetter(*this),
    d_out(&out) {
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
  virtual void shutdown() {
    d_facts.clear();
  }

  /**
   * The output channel for the Theory.
   */
  OutputChannel* d_out;

  /**
   * Returns true if the assertFact queue is empty
   */
  bool done() throw() {
    return d_facts.empty();
  }

  /** Tag for the "preRegisterTerm()-has-been-called" flag on Nodes */
  struct PreRegistered {};
  /** The "preRegisterTerm()-has-been-called" flag on Nodes */
  typedef CVC4::expr::Attribute<PreRegistered, bool> PreRegisteredAttr;

  /**
   * Returns the next atom in the assertFact() queue.  Guarantees that
   * registerTerm() has been called on the theory specific subterms.
   *
   * @return the next atom in the assertFact() queue.
   */
  Node get() {
    Assert( !d_facts.empty(),
            "Theory::get() called with assertion queue empty!" );
    Node fact = d_facts.front();
    d_facts.pop_front();
    Debug("theory") << "Theory::get() => " << fact
                    << "(" << d_facts.size() << " left)" << std::endl;
    d_out->newFact(fact);
    return fact;
  }

public:

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

  // TODO add compiler annotation "constant function" here
  static bool minEffortOnly(Effort e)        { return e == MIN_EFFORT; }
  static bool quickCheckOrMore(Effort e)     { return e >= QUICK_CHECK; }
  static bool quickCheckOnly(Effort e)       { return e >= QUICK_CHECK &&
                                                      e <  STANDARD; }
  static bool standardEffortOrMore(Effort e) { return e >= STANDARD; }
  static bool standardEffortOnly(Effort e)   { return e >= STANDARD &&
                                                      e <  FULL_EFFORT; }
  static bool fullEffort(Effort e)           { return e >= FULL_EFFORT; }

  /**
   * Get the id for this Theory.
   */
  int getId() const {
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
   * Get the output channel associated to this theory [const].
   */
  const OutputChannel& getOutputChannel() const {
    return *d_out;
  }

  /**
   * Pre-register a term.  Done one time for a Node, ever.
   */
  virtual void preRegisterTerm(TNode) = 0;

  /**
   * Pre-rewrite a term.  This default base-class implementation
   * simply returns RewriteComplete(n).  A theory should never
   * rewrite a term to a strictly larger term that contains itself, as
   * this will cause a loop of hard Node links in the cache (and thus
   * memory leakage).
   *
   * Be careful with the return value.  If a preRewrite() can return a
   * sub-expression, and that sub-expression can be a member of the
   * same theory and could be rewritten, make sure to return
   * RewriteAgain instead of RewriteComplete.  This is an easy mistake
   * to make, as preRewrite() is often a short-circuiting version of
   * the same rewrites that occur in postRewrite(); however, in the
   * postRewrite() case, the subexpressions have all been
   * post-rewritten.  In the preRewrite() case, they have NOT yet been
   * pre-rewritten.  For example, (ITE true (ITE true x y) z) should
   * pre-rewrite to x; but if the outer preRewrite() returns
   * RewriteComplete, the result of the pre-rewrite will be
   * (ITE true x y).
   */
  virtual RewriteResponse preRewrite(TNode n, bool topLevel) {
    Debug("theory-rewrite") << "no pre-rewriting to perform for "
                            << n << std::endl;
    return RewriteComplete(n);
  }

  /**
   * Post-rewrite a term.  This default base-class implementation
   * simply returns RewriteComplete(n).  A theory should never
   * rewrite a term to a strictly larger term that contains itself, as
   * this will cause a loop of hard Node links in the cache (and thus
   * memory leakage).
   */
  virtual RewriteResponse postRewrite(TNode n, bool topLevel) {
    Debug("theory-rewrite") << "no post-rewriting to perform for "
                            << n << std::endl;
    return RewriteComplete(n);
  }

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
  virtual void registerTerm(TNode) = 0;

  /**
   * Assert a fact in the current context.
   */
  void assertFact(TNode n) {
    Debug("theory") << "Theory::assertFact(" << n << ")" << std::endl;
    d_facts.push_back(n);
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
  virtual void check(Effort level = FULL_EFFORT) = 0;

  /**
   * T-propagate new literal assignments in the current context.
   */
  virtual void propagate(Effort level = FULL_EFFORT) = 0;

  /**
   * Return an explanation for the literal represented by parameter n
   * (which was previously propagated by this theory).  Report
   * explanations to an output channel.
   */
  virtual void explain(TNode n, Effort level = FULL_EFFORT) = 0;

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
   * TheoryEngine.
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
  virtual Node getValue(TNode n, TheoryEngine* engine) = 0;

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
  virtual void presolve() = 0;

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

  //
  // CODE INVARIANT CHECKING (used only with CVC4_ASSERTIONS)
  //

  /**
   * Different states at which invariants are checked.
   */
  enum ReadyState {
    ABOUT_TO_PUSH,
    ABOUT_TO_POP
  };/* enum ReadyState */

  /**
   * Public invariant checker.  Assert that this theory is in a valid
   * state for the (external) system state.  This implementation
   * checks base invariants and then calls theoryReady().  This
   * function may abort in the case of a failed assert, or return
   * false (the caller should assert that the return value is true).
   *
   * @param s the state about which to check invariants
   */
  bool ready(ReadyState s) {
    if(s == ABOUT_TO_PUSH) {
      Assert(d_facts.empty(), "Theory base code invariant broken: "
             "fact queue is nonempty on context push");
    }

    return theoryReady(s);
  }

protected:

  /**
   * Check any invariants at the ReadyState given.  Only called by
   * Theory class, and then only with CVC4_ASSERTIONS enabled.  This
   * function may abort in the case of a failed assert, or return
   * false (the caller should assert that the return value is true).
   *
   * @param s the state about which to check invariants
   */
  virtual bool theoryReady(ReadyState s) {
    return true;
  }

  /**
   * Check whether a node is in the pre-rewrite cache or not.
   */
  static bool inPreRewriteCache(TNode n, bool topLevel) throw() {
    if(topLevel) {
      return n.hasAttribute(PreRewriteCacheTop());
    } else {
      return n.hasAttribute(PreRewriteCache());
    }
  }

  /**
   * Get the value of the pre-rewrite cache (or Node::null()) if there is
   * none).
   */
  static Node getPreRewriteCache(TNode n, bool topLevel) throw() {
    if(topLevel) {
      Node out;
      if(n.getAttribute(PreRewriteCacheTop(), out)) {
        return out.isNull() ? Node(n) : out;
      }
    } else {
      Node out;
      if(n.getAttribute(PreRewriteCache(), out)) {
        return out.isNull() ? Node(n) : out;
      }
    }
    return Node::null();
  }

  /**
   * Set the value of the pre-rewrite cache.  v cannot be a null Node.
   */
  static void setPreRewriteCache(TNode n, bool topLevel, TNode v) throw() {
    AssertArgument(!n.isNull(), n, "n cannot be null in setPostRewriteCache()");
    AssertArgument(!v.isNull(), v, "v cannot be null in setPreRewriteCache()");
    // mappings from  n -> n  are actually stored as  n -> null  as a
    // special case, to avoid cycles in the reference-counting of Nodes
    if(topLevel) {
      n.setAttribute(PreRewriteCacheTop(), n == v ? TNode::null() : v);
    } else {
      n.setAttribute(PreRewriteCache(), n == v ? TNode::null() : v);
    }
  }

  /**
   * Check whether a node is in the post-rewrite cache or not.
   */
  static bool inPostRewriteCache(TNode n, bool topLevel) throw() {
    if(topLevel) {
      return n.hasAttribute(PostRewriteCacheTop());
    } else {
      return n.hasAttribute(PostRewriteCache());
    }
  }

  /**
   * Get the value of the post-rewrite cache (or Node::null()) if there is
   * none).
   */
  static Node getPostRewriteCache(TNode n, bool topLevel) throw() {
    if(topLevel) {
      Node out;
      if(n.getAttribute(PostRewriteCacheTop(), out)) {
        return out.isNull() ? Node(n) : out;
      }
    } else {
      Node out;
      if(n.getAttribute(PostRewriteCache(), out)) {
        return out.isNull() ? Node(n) : out;
      }
    }
    return Node::null();
  }

  /**
   * Set the value of the post-rewrite cache.  v cannot be a null Node.
   */
  static void setPostRewriteCache(TNode n, bool topLevel, TNode v) throw() {
    AssertArgument(!n.isNull(), n, "n cannot be null in setPostRewriteCache()");
    AssertArgument(!v.isNull(), v, "v cannot be null in setPostRewriteCache()");
    // mappings from  n -> n  are actually stored as  n -> null  as a
    // special case, to avoid cycles in the reference-counting of Nodes
    if(topLevel) {
      n.setAttribute(PostRewriteCacheTop(), n == v ? TNode::null() : v);
    } else {
      n.setAttribute(PostRewriteCache(), n == v ? TNode::null() : v);
    }
  }

};/* class Theory */

std::ostream& operator<<(std::ostream& os, Theory::Effort level);

}/* CVC4::theory namespace */

inline std::ostream& operator<<(std::ostream& out,
                                const CVC4::theory::Theory& theory) {
  return out << theory.identify();
}

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_H */
