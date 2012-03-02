/*********************                                                        */
/*! \file congruence_closure.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The congruence closure module
 **
 ** The congruence closure module.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__CONGRUENCE_CLOSURE_H
#define __CVC4__UTIL__CONGRUENCE_CLOSURE_H

#include <sstream>
#include <list>

#include <ext/hash_map>

#include "expr/node_manager.h"
#include "expr/node.h"
#include "context/context_mm.h"
#include "context/cdo.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist_context_memory.h"
#include "util/exception.h"
#include "context/stacking_map.h"
#include "util/stats.h"

namespace CVC4 {

template <class OutputChannel, class CongruenceOperatorList>
class CongruenceClosure;

template <class OutputChannel, class CongruenceOperatorList>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel, CongruenceOperatorList>& cc);

/**
 * A CongruenceClosureException is thrown by
 * CongruenceClosure::explain() when that method is asked to explain a
 * congruence that doesn't exist.
 */
class CVC4_PUBLIC CongruenceClosureException : public Exception {
public:
  inline CongruenceClosureException(std::string msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
  inline CongruenceClosureException(const char* msg) :
    Exception(std::string("Congruence closure exception: ") + msg) {}
};/* class CongruenceClosureException */

struct EndOfCongruenceOpList;
template <Kind kind_, class Tail_ = EndOfCongruenceOpList>
struct CongruenceOperator {
  enum { kind = kind_ };
  typedef Tail_ Tail;
};/* class CongruenceOperator<> */

#define CONGRUENCE_OPERATORS_1(kind1) ::CVC4::CongruenceOperator<kind1, ::CVC4::EndOfCongruenceOpList>
#define CONGRUENCE_OPERATORS_2(kind1, kind2) ::CVC4::CongruenceOperator<kind1, CONGRUENCE_OPERATORS_1(kind2)>
#define CONGRUENCE_OPERATORS_3(kind1, kind2, kind3) ::CVC4::CongruenceOperator<kind1, CONGRUENCE_OPERATORS_2(kind2, kind3)>
#define CONGRUENCE_OPERATORS_4(kind1, kind2, kind3, kind4) ::CVC4::CongruenceOperator<kind1, CONGRUENCE_OPERATORS_3(kind2, kind3, kind4)>
#define CONGRUENCE_OPERATORS_5(kind1, kind2, kind3, kind4, kind5) ::CVC4::CongruenceOperator<kind1, CONGRUENCE_OPERATORS_4(kind2, kind3, kind4, kind5)>

/**
 * Returns true if the kind k is registered as a congruence operator
 * for this CongruenceClosure.  (That is, if it's in the
 * CongruenceOperatorList template parameter.)  False otherwise.
 */
template <class CongruenceOperatorList>
inline bool isInCongruenceOperatorList(Kind k) {
  typedef typename CongruenceOperatorList::Tail Tail;
  return k == Kind(CongruenceOperatorList::kind) ||
    isInCongruenceOperatorList<Tail>(k);
}

// specialization for empty list
template <>
inline bool isInCongruenceOperatorList<EndOfCongruenceOpList>(Kind k) {
  return false;
}

/**
 * Congruence closure module for CVC4.
 *
 * This is a service class for theories.  One uses a CongruenceClosure
 * by adding a number of relevant terms with addTerm() and equalities
 * with addEquality().  It then gets notified (through OutputChannel,
 * below), of new equalities.
 *
 * OutputChannel is a template argument (it's probably a thin layer,
 * and we want to avoid a virtual call hierarchy in this case, and
 * enable aggressive inlining).  It need only implement one method,
 * notifyCongruent():
 *
 *   class MyOutputChannel {
 *   public:
 *     void notifyCongruent(TNode a, TNode b) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with addTerm().  However,
 *       // something in their equivalence class was (for which a
 *       // previous notifyCongruent() would have notified you of
 *       // their EC representative, which is now "a" or "b").
 *       //
 *       // This call is made while the merge is being done.  If you
 *       // throw any exception here, you'll immediately exit the
 *       // CongruenceClosure call and will miss whatever pending
 *       // merges were being performed, leaving the CongruenceClosure
 *       // module in a bad state.  Therefore if you throw, you should
 *       // only do so if you are going to backjump, re-establishing a
 *       // good (former) state.  Keep this in mind if a
 *       // CVC4::Interrupted that *doesn't* lead to a backjump can
 *       // interrupt you.
 *     }
 *   };
 *
 * CongruenceOperatorList is a typelist of congruence Kinds,
 * e.g., CONGRUENCE_OPERATORS_1(kind::APPLY_UF)
 * or CONGRUENCE_OPERATORS_2(kind::SELECT, kind::STORE)
 */
template <class OutputChannel, class CongruenceOperatorList>
class CongruenceClosure {
  /** The context */
  context::Context* d_context;

  /** The output channel */
  OutputChannel* d_out;

  // typedef all of these so that iterators are easy to define
  typedef context::StackingMap<Node, Node, NodeHashFunction> RepresentativeMap;
  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > ClassList;
  typedef context::CDHashMap<Node, ClassList*, NodeHashFunction> ClassLists;
  typedef context::CDList<TNode, context::ContextMemoryAllocator<TNode> > UseList;
  typedef context::CDHashMap<TNode, UseList*, TNodeHashFunction> UseLists;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> LookupMap;

  typedef __gnu_cxx::hash_map<TNode, Node, TNodeHashFunction> EqMap;

  typedef context::CDHashMap<Node, Node, NodeHashFunction> ProofMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> ProofLabel;

  // Simple, NON-context-dependent pending list, union find and "seen
  // set" types for constructing explanations and
  // nearestCommonAncestor(); see explain().
  typedef std::list<std::pair<Node, Node> > PendingProofList_t;
  typedef __gnu_cxx::hash_map<TNode, TNode, TNodeHashFunction> UnionFind_t;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> SeenSet_t;

  RepresentativeMap d_representative;
  ClassLists d_classList;
  UseLists d_useList;
  LookupMap d_lookup;

  EqMap d_eqMap;
  context::CDHashSet<TNode, TNodeHashFunction> d_added;

  ProofMap d_proof;
  ProofLabel d_proofLabel;

  ProofMap d_proofRewrite;

  /**
   * The set of terms we care about (i.e. those that have been given
   * us with addTerm() and their representatives).
   */
  typedef context::CDHashSet<TNode, TNodeHashFunction> CareSet;
  CareSet d_careSet;

  // === STATISTICS ===
  AverageStat d_explanationLength;/**< average explanation length */
  IntStat d_newSkolemVars;/**< new vars created */

  static inline bool isCongruenceOperator(TNode n) {
    // For the datatypes theory, we've removed the invariant that
    // parameterized kinds must have at least one argument.  Consider
    // (CONSTRUCTOR nil) for instance.  So, n here can be an operator
    // that's normally checked for congruence (like CONSTRUCTOR) but
    // shouldn't be treated as a congruence operator if it only has an
    // operator and no children (like CONSTRUCTOR nil), since we can
    // treat that as a simple variable.
    return n.getNumChildren() > 0 &&
      isInCongruenceOperatorList<CongruenceOperatorList>(n.getKind());
  }

public:
  /** Construct a congruence closure module instance */
  CongruenceClosure(context::Context* ctxt, OutputChannel* out)
    throw(AssertionException) :
    d_context(ctxt),
    d_out(out),
    d_representative(ctxt),
    d_classList(ctxt),
    d_useList(ctxt),
    d_lookup(ctxt),
    d_added(ctxt),
    d_proof(ctxt),
    d_proofLabel(ctxt),
    d_proofRewrite(ctxt),
    d_careSet(ctxt),
    d_explanationLength("congruence_closure::AverageExplanationLength"),
    d_newSkolemVars("congruence_closure::NewSkolemVariables", 0) {
  }

  ~CongruenceClosure() {}

  /**
   * Add a term into CC consideration.  This is context-dependent.
   * Calls OutputChannel::notifyCongruent(), so it can throw anything
   * that that function can.
   */
  void addTerm(TNode trm);

  /**
   * Add an equality literal eq into CC consideration.  This is
   * context-dependent.  Calls OutputChannel::notifyCongruent()
   * indirectly, so it can throw anything that that function can.
   */
  void addEquality(TNode inputEq) {
    if(Debug.isOn("cc")) {
      Debug("cc") << "CC addEquality[" << d_context->getLevel() << "]: " << inputEq << std::endl;
    }
    Assert(inputEq.getKind() == kind::EQUAL ||
           inputEq.getKind() == kind::IFF);
    NodeBuilder<> eqb(inputEq.getKind());
    if(isCongruenceOperator(inputEq[1]) &&
       !isCongruenceOperator(inputEq[0])) {
      eqb << flatten(inputEq[1]) << inputEq[0];
    } else {
      eqb << flatten(inputEq[0]) << replace(flatten(inputEq[1]));
    }
    Node eq = eqb;
    addEq(eq, inputEq);
  }

private:
  void addEq(TNode eq, TNode inputEq);

  Node flatten(TNode t) {
    if(isCongruenceOperator(t)) {
      NodeBuilder<> appb(t.getKind());
      Assert(replace(flatten(t.getOperator())) == t.getOperator(),
             "CongruenceClosure:: bad state: higher-order term ??");
      if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
	appb << t.getOperator();
      }
      for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
        appb << replace(flatten(*i));
      }
      return Node(appb);
    } else {
      return t;
    }
  }

  Node replace(TNode t) {
    if(isCongruenceOperator(t)) {
      EqMap::iterator i = d_eqMap.find(t);
      if(i == d_eqMap.end()) {
        ++d_newSkolemVars;
        Node v = NodeManager::currentNM()->mkSkolem(t.getType());
        Debug("cc") << "CC made skolem " << v << std::endl;
        addEq(NodeManager::currentNM()->mkNode(t.getType().isBoolean() ? kind::IFF : kind::EQUAL, t, v), TNode::null());
        d_added.insert(v);
        d_eqMap[t] = v;
        return v;
      } else {
        TNode v = (*i).second;
        if(!d_added.contains(v)) {
          addEq(NodeManager::currentNM()->mkNode(t.getType().isBoolean() ? kind::IFF : kind::EQUAL, t, v), TNode::null());
          d_added.insert(v);
        }
        return v;
      }
    } else {
      return t;
    }
  }

  TNode proofRewrite(TNode pfStep) const {
    ProofMap::const_iterator i = d_proofRewrite.find(pfStep);
    if(i == d_proofRewrite.end()) {
      return pfStep;
    } else {
      return (*i).second;
    }
  }

public:
  /**
   * Inquire whether two expressions are congruent in the current
   * context.
   */
  inline bool areCongruent(TNode a, TNode b) const throw(AssertionException) {
    if(Debug.isOn("cc")) {
      Debug("cc") << "CC areCongruent? " << a << "  ==  " << b << std::endl;
      Debug("cc") << "  a  " << a << std::endl;
      Debug("cc") << "  a' " << normalize(a) << std::endl;
      Debug("cc") << "  b  " << b << std::endl;
      Debug("cc") << "  b' " << normalize(b) << std::endl;
    }

    Node ap = find(a), bp = find(b);

    // areCongruent() works fine as just find(a) == find(b) _except_
    // for terms not appearing in equalities.  For example, let's say
    // you have unary f and binary g, h, and
    //
    //   a == f(b) ; f(a) == b ; g == h
    //
    // it's clear that h(f(a),a) == g(b,a), but it's not in the
    // union-find even if you addTerm() on those two.
    //
    // we implement areCongruent() to handle more general
    // queries---i.e., to check for new congruences---but shortcut a
    // cheap & common case
    //
    return ap == bp || normalize(ap) == normalize(bp);
  }

private:
  /**
   * Find the EC representative for a term t in the current context.
   */
  inline TNode find(TNode t) const throw(AssertionException) {
    TNode rep1 = d_representative[t];
    return rep1.isNull() ? t : rep1;
  }

  void explainAlongPath(TNode a, TNode c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
    throw(AssertionException);

  Node highestNode(TNode a, UnionFind_t& unionFind) const
    throw(AssertionException);

  Node nearestCommonAncestor(TNode a, TNode b, UnionFind_t& unionFind)
    throw(AssertionException);

public:
  /**
   * Request an explanation for why a and b are in the same EC in the
   * current context.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  Node explain(Node a, Node b)
    throw(CongruenceClosureException, AssertionException);

  /**
   * Request an explanation for why the lhs and rhs of this equality
   * are in the same EC.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  inline Node explain(TNode eq)
    throw(CongruenceClosureException, AssertionException) {
    Assert(eq.getKind() == kind::EQUAL ||
           eq.getKind() == kind::IFF);
    return explain(eq[0], eq[1]);
  }

  /**
   * Normalization.
   */
  Node normalize(TNode t) const throw(AssertionException);

private:

  friend std::ostream& operator<< <>(std::ostream& out,
                                     const CongruenceClosure<OutputChannel, CongruenceOperatorList>& cc);

  /**
   * Internal propagation of information.  Propagation tends to
   * cascade (this implementation uses an iterative "pending"
   * worklist), and "seed" is the "seeding" propagation to do (the
   * first one).  Calls OutputChannel::notifyCongruent() indirectly,
   * so it can throw anything that that function can.
   */
  void propagate(TNode seed);

  /**
   * Internal lookup mapping from tuples to equalities.
   */
  inline TNode lookup(TNode a) const {
    LookupMap::iterator i = d_lookup.find(a);
    if(i == d_lookup.end()) {
      return TNode::null();
    } else {
      TNode l = (*i).second;
      Assert(l.getKind() == kind::EQUAL ||
             l.getKind() == kind::IFF);
      return l;
    }
  }

  /**
   * Internal lookup mapping.
   */
  inline void setLookup(TNode a, TNode b) {
    Assert(a.getKind() == kind::TUPLE);
    Assert(b.getKind() == kind::EQUAL ||
           b.getKind() == kind::IFF);
    d_lookup[a] = b;
  }

  /**
   * Given an apply (f a1 a2...), build a TUPLE expression
   * (f', a1', a2', ...) suitable for a lookup() key.
   */
  Node buildRepresentativesOfApply(TNode apply, Kind kindToBuild = kind::TUPLE)
    throw(AssertionException);

  /**
   * Append equality "eq" to uselist of "of".
   */
  inline void appendToUseList(TNode of, TNode eq) {
    Trace("cc") << "adding " << eq << " to use list of " << of << std::endl;
    Assert(eq.getKind() == kind::EQUAL ||
           eq.getKind() == kind::IFF);
    Assert(of == find(of));
    UseLists::iterator usei = d_useList.find(of);
    UseList* ul;
    if(usei == d_useList.end()) {
      ul = new(d_context->getCMM()) UseList(true, d_context, false,
                                            context::ContextMemoryAllocator<TNode>(d_context->getCMM()));
      d_useList.insertDataFromContextMemory(of, ul);
    } else {
      ul = (*usei).second;
    }
    ul->push_back(eq);
  }

  /**
   * Merge equivalence class ec1 under ec2.  ec1's new union-find
   * representative becomes ec2.  Calls
   * OutputChannel::notifyCongruent(), so it can throw anything that
   * that function can.
   */
  void merge(TNode ec1, TNode ec2);
  void mergeProof(TNode a, TNode b, TNode e);

public:

  // === STATISTICS ACCESSORS ===

  /**
   * Get access to the explanation-length statistic.  Returns the
   * statistic itself so that reference-statistics can be wrapped
   * around it, useful since CongruenceClosure is a client class and
   * shouldn't be directly registered with the StatisticsRegistry.
   */
  const AverageStat& getExplanationLength() const throw() {
    return d_explanationLength;
  }

  /**
   * Get access to the new-skolem-vars statistic.  Returns the
   * statistic itself so that reference-statistics can be wrapped
   * around it, useful since CongruenceClosure is a client class and
   * shouldn't be directly registered with the StatisticsRegistry.
   */
  const IntStat& getNewSkolemVars() const throw() {
    return d_newSkolemVars;
  }

};/* class CongruenceClosure */


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::addTerm(TNode t) {
  Node trm = replace(flatten(t));
  Node trmp = find(trm);

  if(Debug.isOn("cc")) {
    Debug("cc") << "CC addTerm [" << d_careSet.size() << "] " << d_careSet.contains(t) << ": " << t << std::endl
                << "           [" << d_careSet.size() << "] " << d_careSet.contains(trm) << ": " << trm << std::endl
                << "           [" << d_careSet.size() << "] " << d_careSet.contains(trmp) << ": " << trmp << std::endl;
  }

  if(t != trm && !d_careSet.contains(t)) {
    // we take care to only notify our client once of congruences
    d_out->notifyCongruent(t, trm);
    d_careSet.insert(t);
  }

  if(!d_careSet.contains(trm)) {
    if(trm != trmp) {
      // if part of an equivalence class headed by another node,
      // notify the client of this merge that's already been
      // performed..
      d_out->notifyCongruent(trm, trmp);
    }

    // add its representative to the care set
    d_careSet.insert(trmp);
  }
}


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::addEq(TNode eq, TNode inputEq) {
  Assert(!eq[0].getType().isFunction() && !eq[1].getType().isFunction(),
         "CongruenceClosure:: equality between function symbols not allowed");

  d_proofRewrite[eq] = inputEq;

  if(Trace.isOn("cc")) {
    Trace("cc") << "CC addEq[" << d_context->getLevel() << "]: " << eq << std::endl;
  }
  Assert(eq.getKind() == kind::EQUAL ||
         eq.getKind() == kind::IFF);
  Assert(!isCongruenceOperator(eq[1]));
  if(areCongruent(eq[0], eq[1])) {
    Trace("cc") << "CC -- redundant, ignoring...\n";
    return;
  }

  TNode s = eq[0], t = eq[1];

  Assert(s != t);

  Trace("cc:detail") << "CC        " << s << " == " << t << std::endl;

  // change from paper: do this whether or not s, t are applications
  Trace("cc:detail") << "CC        propagating the eq" << std::endl;

  if(!isCongruenceOperator(s)) {
    // s, t are constants
    propagate(eq);
  } else {
    // s is an apply, t is a constant
    Node ap = buildRepresentativesOfApply(s);

    Trace("cc:detail") << "CC rewrLHS " << "op_and_args_a == " << t << std::endl;
    Trace("cc") << "CC ap is   " << ap << std::endl;

    TNode l = lookup(ap);
    Trace("cc:detail") << "CC lookup(ap): " << l << std::endl;
    if(!l.isNull()) {
      // ensure a hard Node link exists to this during the call
      Node pending = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, l);
      Trace("cc:detail") << "pending1 " << pending << std::endl;
      propagate(pending);
    } else {
      Trace("cc") << "CC lookup(ap) setting to " << eq << std::endl;
      setLookup(ap, eq);
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        appendToUseList(*i, eq);
      }
    }
  }
}/* addEq() */


template <class OutputChannel, class CongruenceOperatorList>
Node CongruenceClosure<OutputChannel, CongruenceOperatorList>::buildRepresentativesOfApply(TNode apply,
                                                              Kind kindToBuild)
  throw(AssertionException) {
  Assert(isCongruenceOperator(apply));
  NodeBuilder<> argspb(kindToBuild);
  Assert(find(apply.getOperator()) == apply.getOperator(),
         "CongruenceClosure:: bad state: "
         "function symbol (or other congruence operator) merged with another");
  if(apply.getMetaKind() == kind::metakind::PARAMETERIZED) {
    argspb << apply.getOperator();
  }
  for(TNode::iterator i = apply.begin(); i != apply.end(); ++i) {
    argspb << find(*i);
  }
  return argspb;
}/* buildRepresentativesOfApply() */


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::propagate(TNode seed) {
  Trace("cc:detail") << "=== doing a round of propagation ===" << std::endl
                     << "the \"seed\" propagation is: " << seed << std::endl;

  std::list<Node> pending;

  Trace("cc") << "seed propagation with: " << seed << std::endl;
  pending.push_back(seed);
  do { // while(!pending.empty())
    Node e = pending.front();
    pending.pop_front();

    Trace("cc") << "=== top of propagate loop ===" << std::endl
                << "=== e is " << e << " ===" << std::endl;

    TNode a, b;
    if(e.getKind() == kind::EQUAL ||
       e.getKind() == kind::IFF) {
      // e is an equality a = b (a, b are constants)

      a = e[0];
      b = e[1];

      Trace("cc:detail") << "propagate equality: " << a << " == " << b << std::endl;
    } else {
      // e is a tuple ( apply f A... = a , apply f B... = b )

      Trace("cc") << "propagate tuple: " << e << "\n";

      Assert(e.getKind() == kind::TUPLE);

      Assert(e.getNumChildren() == 2);
      Assert(e[0].getKind() == kind::EQUAL ||
             e[0].getKind() == kind::IFF);
      Assert(e[1].getKind() == kind::EQUAL ||
             e[1].getKind() == kind::IFF);

      // tuple is (eq, lookup)
      a = e[0][1];
      b = e[1][1];

      Assert(!isCongruenceOperator(a));
      Assert(!isCongruenceOperator(b));

      Trace("cc") << "                 ( " << a << " , " << b << " )" << std::endl;
    }

    if(Debug.isOn("cc")) {
      Trace("cc:detail") << "=====at start=====" << std::endl
                         << "a          :" << a << std::endl
                         << "NORMALIZE a:" << normalize(a) << std::endl
                         << "b          :" << b << std::endl
                         << "NORMALIZE b:" << normalize(b) << std::endl
                         << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;
    }

    // change from paper: need to normalize() here since in our
    // implementation, a and b can be applications
    Node ap = find(a), bp = find(b);
    if(ap != bp) {

      Trace("cc:detail") << "EC[a] == " << ap << std::endl
                         << "EC[b] == " << bp << std::endl;

      { // w.l.o.g., |classList ap| <= |classList bp|
        ClassLists::iterator cl_api = d_classList.find(ap);
        ClassLists::iterator cl_bpi = d_classList.find(bp);
        unsigned sizeA = (cl_api == d_classList.end() ? 0 : (*cl_api).second->size());
        unsigned sizeB = (cl_bpi == d_classList.end() ? 0 : (*cl_bpi).second->size());
        Trace("cc") << "sizeA == " << sizeA << "  sizeB == " << sizeB << std::endl;
        if(sizeA > sizeB) {
          Trace("cc") << "swapping..\n";
          TNode tmp = ap; ap = bp; bp = tmp;
          tmp = a; a = b; b = tmp;
        }
      }

      { // class list handling
        ClassLists::iterator cl_bpi = d_classList.find(bp);
        ClassList* cl_bp;
        if(cl_bpi == d_classList.end()) {
          cl_bp = new(d_context->getCMM()) ClassList(true, d_context, false,
                                                     context::ContextMemoryAllocator<TNode>(d_context->getCMM()));
          d_classList.insertDataFromContextMemory(bp, cl_bp);
          Trace("cc:detail") << "CC in prop alloc classlist for " << bp << std::endl;
        } else {
          cl_bp = (*cl_bpi).second;
        }
        // we don't store 'ap' in its own class list; so process it here
        Trace("cc:detail") << "calling mergeproof/merge1 " << ap
                           << "   AND   " << bp << std::endl;
        mergeProof(a, b, e);
        merge(ap, bp);

        Trace("cc") << " adding ap == " << ap << std::endl
                    << "   to class list of " << bp << std::endl;
        cl_bp->push_back(ap);
        ClassLists::const_iterator cli = d_classList.find(ap);
        if(cli != d_classList.end()) {
          const ClassList* cl = (*cli).second;
          for(ClassList::const_iterator i = cl->begin();
              i != cl->end();
              ++i) {
            TNode c = *i;
            if(Debug.isOn("cc")) {
              Debug("cc") << "c is " << c << "\n"
                          << " from cl of " << ap << std::endl;
              Debug("cc") << " it's find ptr is: " << find(c) << std::endl;
            }
            Assert(find(c) == ap);
            Trace("cc:detail") << "calling merge2 " << c << bp << std::endl;
            merge(c, bp);
            // move c from classList(ap) to classlist(bp);
            //i = cl.erase(i);// difference from paper: don't need to erase
            Trace("cc") << " adding c to class list of " << bp << std::endl;
            cl_bp->push_back(c);
          }
        }
        Trace("cc:detail") << "bottom\n";
      }

      { // use list handling
        if(Debug.isOn("cc:detail")) {
          Debug("cc:detail") << "ap is " << ap << std::endl;
          Debug("cc:detail") << "find(ap) is " << find(ap) << std::endl;
          Debug("cc:detail") << "CC in prop go through useList of " << ap << std::endl;
        }
        UseLists::iterator usei = d_useList.find(ap);
        if(usei != d_useList.end()) {
          UseList* ul = (*usei).second;
          //for( f(c1,c2)=c in UseList(ap) )
          for(UseList::const_iterator i = ul->begin();
              i != ul->end();
              ++i) {
            TNode eq = *i;
            Trace("cc") << "CC  -- useList: " << eq << std::endl;
            Assert(eq.getKind() == kind::EQUAL ||
                   eq.getKind() == kind::IFF);
            // change from paper
            // use list elts can have form (apply c..) = x  OR  x = (apply c..)
            Assert(isCongruenceOperator(eq[0]) ||
                   isCongruenceOperator(eq[1]));
            // do for each side that is an application
            for(int side = 0; side <= 1; ++side) {
              if(!isCongruenceOperator(eq[side])) {
                continue;
              }

              Node cp = buildRepresentativesOfApply(eq[side]);

              // if lookup(c1',c2') is some f(d1,d2)=d then
              TNode n = lookup(cp);

              Trace("cc:detail") << "CC     -- c' is " << cp << std::endl;

              if(!n.isNull()) {
                Trace("cc:detail") << "CC     -- lookup(c') is " << n << std::endl;
                // add (f(c1,c2)=c,f(d1,d2)=d) to pending
                Node tuple = NodeManager::currentNM()->mkNode(kind::TUPLE, eq, n);
                Trace("cc") << "CC add tuple to pending: " << tuple << std::endl;
                pending.push_back(tuple);
                // remove f(c1,c2)=c from UseList(ap)
                Trace("cc:detail") << "supposed to remove " << eq << std::endl
                                   << "  from UseList of " << ap << std::endl;
                //i = ul.erase(i);// difference from paper: don't need to erase
              } else {
                Trace("cc") << "CC     -- lookup(c') is null" << std::endl;
                Trace("cc") << "CC     -- setlookup(c') to " << eq << std::endl;
                // set lookup(c1',c2') to f(c1,c2)=c
                setLookup(cp, eq);
                // move f(c1,c2)=c from UseList(ap) to UseList(b')
                //i = ul.erase(i);// difference from paper: don't need to erase
                appendToUseList(bp, eq);
              }
            }
          }
        }
      }/* use lists */
      Trace("cc:detail") << "CC in prop done with useList of " << ap << std::endl;
    } else {
      Trace("cc:detail") << "CCs the same ( == " << ap << "), do nothing." << std::endl;
    }

    if(Debug.isOn("cc")) {
      Debug("cc") << "=====at end=====" << std::endl
                  << "a          :" << a << std::endl
                  << "NORMALIZE a:" << normalize(a) << std::endl
                  << "b          :" << b << std::endl
                  << "NORMALIZE b:" << normalize(b) << std::endl
                  << "alreadyCongruent?:" << areCongruent(a,b) << std::endl;
    }
    Assert(areCongruent(a, b));
  } while(!pending.empty());
}/* propagate() */


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::merge(TNode ec1, TNode ec2) {
  /*
  if(Debug.isOn("cc:detail")) {
    Debug("cc:detail") << "  -- merging " << ec1
                       << (d_careSet.find(ec1) == d_careSet.end() ?
                           " -- NOT in care set" : " -- IN CARE SET") << std::endl
                       << "         and " << ec2
                       << (d_careSet.find(ec2) == d_careSet.end() ?
                           " -- NOT in care set" : " -- IN CARE SET") << std::endl;
  }
  */

  Trace("cc") << "CC setting rep of " << ec1 << std::endl;
  Trace("cc") << "CC             to " << ec2 << std::endl;

  /* can now be applications
  Assert(!isCongruenceOperator(ec1));
  Assert(!isCongruenceOperator(ec2));
  */

  Assert(find(ec1) != ec2);
  //Assert(find(ec1) == ec1);
  Assert(find(ec2) == ec2);

  d_representative.set(ec1, ec2);

  if(d_careSet.find(ec1) != d_careSet.end()) {
    d_careSet.insert(ec2);
    d_out->notifyCongruent(ec1, ec2);
  }
}/* merge() */


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::mergeProof(TNode a, TNode b, TNode e) {
  Trace("cc") << "  -- merge-proofing " << a << "\n"
              << "                and " << b << "\n"
              << "               with " << e << "\n";

  // proof forest gets a -> b labeled with e

  // first reverse all the edges in proof forest to root of this proof tree
  Trace("cc") << "CC PROOF reversing proof tree\n";
  // c and p are child and parent in (old) proof tree
  Node c = a, p = d_proof[a], edgePf = d_proofLabel[a];
  // when we hit null p, we're at the (former) root
  Trace("cc") << "CC PROOF start at c == " << c << std::endl
              << "                  p == " << p << std::endl
              << "             edgePf == " << edgePf << std::endl;
  while(!p.isNull()) {
    // in proof forest,
    // we have edge   c --edgePf-> p
    // turn it into   c <-edgePf-- p

    Node pParSave = d_proof[p];
    Node pLabelSave = d_proofLabel[p];
    d_proof[p] = c;
    d_proofLabel[p] = edgePf;
    c = p;
    p = pParSave;
    edgePf = pLabelSave;
    Trace("cc") << "CC PROOF now   at c == " << c << std::endl
                << "                  p == " << p << std::endl
                << "             edgePf == " << edgePf << std::endl;
  }

  // add an edge from a to b
  d_proof[a] = b;
  d_proofLabel[a] = e;
}/* mergeProof() */


template <class OutputChannel, class CongruenceOperatorList>
Node CongruenceClosure<OutputChannel, CongruenceOperatorList>::normalize(TNode t) const
  throw(AssertionException) {
  Trace("cc:detail") << "normalize " << t << std::endl;
  if(!isCongruenceOperator(t)) {// t is a constant
    t = find(t);
    Trace("cc:detail") << "  find " << t << std::endl;
    return t;
  } else {// t is an apply
    NodeBuilder<> apb(kind::TUPLE);
    Assert(normalize(t.getOperator()) == t.getOperator(),
           "CongruenceClosure:: bad state: "
           "function symbol merged with another");
    if(t.getMetaKind() == kind::metakind::PARAMETERIZED) {
      apb << t.getOperator();
    }
    Node n;
    bool allConstants = (!isCongruenceOperator(n));
    for(TNode::iterator i = t.begin(); i != t.end(); ++i) {
      TNode c = *i;
      n = normalize(c);
      apb << n;
      allConstants = (allConstants && !isCongruenceOperator(n));
    }

    Node ap = apb;
    Trace("cc:detail") << "  got ap " << ap << std::endl;

    Node theLookup = lookup(ap);
    if(allConstants && !theLookup.isNull()) {
      Assert(theLookup.getKind() == kind::EQUAL ||
             theLookup.getKind() == kind::IFF);
      Assert(isCongruenceOperator(theLookup[0]));
      Assert(!isCongruenceOperator(theLookup[1]));
      return find(theLookup[1]);
    } else {
      NodeBuilder<> fa(t.getKind());
      for(Node::iterator i = ap.begin(); i != ap.end(); ++i) {
        fa << *i;
      }
      // ensure a hard Node link exists for the return
      Node n = fa;
      return n;
    }
  }
}/* normalize() */


// This is the find() operation for the auxiliary union-find.  This
// union-find is not context-dependent, as it's used only during
// explain().  It does path compression.
template <class OutputChannel, class CongruenceOperatorList>
Node CongruenceClosure<OutputChannel, CongruenceOperatorList>::highestNode(TNode a, UnionFind_t& unionFind) const
  throw(AssertionException) {
  UnionFind_t::iterator i = unionFind.find(a);
  if(i == unionFind.end()) {
    return a;
  } else {
    return unionFind[a] = highestNode((*i).second, unionFind);
  }
}/* highestNode() */


template <class OutputChannel, class CongruenceOperatorList>
void CongruenceClosure<OutputChannel, CongruenceOperatorList>::explainAlongPath(TNode a, TNode c, PendingProofList_t& pending, UnionFind_t& unionFind, std::list<Node>& pf)
  throw(AssertionException) {

  a = highestNode(a, unionFind);
  Assert(c == highestNode(c, unionFind));

  while(a != c) {
    Node b = d_proof[a];
    Node e = d_proofLabel[a];
    if(e.getKind() == kind::EQUAL ||
       e.getKind() == kind::IFF) {
      pf.push_back(e);
    } else {
      Assert(e.getKind() == kind::TUPLE);
      pf.push_back(e[0]);
      pf.push_back(e[1]);
      Assert(isCongruenceOperator(e[0][0]));
      Assert(!isCongruenceOperator(e[0][1]));
      Assert(isCongruenceOperator(e[1][0]));
      Assert(!isCongruenceOperator(e[1][1]));
      Assert(e[0][0].getNumChildren() == e[1][0].getNumChildren());
      Assert(e[0][0].getOperator() == e[1][0].getOperator(),
             "CongruenceClosure:: bad state: function symbols should be equal");
      // shouldn't have to prove this for operators
      //pending.push_back(std::make_pair(e[0][0].getOperator(), e[1][0].getOperator()));
      for(int i = 0, nc = e[0][0].getNumChildren(); i < nc; ++i) {
        pending.push_back(std::make_pair(e[0][0][i], e[1][0][i]));
      }
    }
    unionFind[a] = b;
    a = highestNode(b, unionFind);
  }
}/* explainAlongPath() */


template <class OutputChannel, class CongruenceOperatorList>
Node CongruenceClosure<OutputChannel, CongruenceOperatorList>::nearestCommonAncestor(TNode a, TNode b, UnionFind_t& unionFind)
  throw(AssertionException) {
  SeenSet_t seen;

  Assert(find(a) == find(b));

  do {
    a = highestNode(a, unionFind);
    seen.insert(a);
    a = d_proof[a];
  } while(!a.isNull());

  for(;;) {
    b = highestNode(b, unionFind);
    if(seen.find(b) != seen.end()) {
      return b;
    }
    b = d_proof[b];

    Assert(!b.isNull());
  }
}/* nearestCommonAncestor() */


template <class OutputChannel, class CongruenceOperatorList>
Node CongruenceClosure<OutputChannel, CongruenceOperatorList>::explain(Node a, Node b)
  throw(CongruenceClosureException, AssertionException) {

  Assert(a != b);

  if(!areCongruent(a, b)) {
    throw CongruenceClosureException("asked to explain() congruence of nodes "
                                     "that aren't congruent");
  }

  if(isCongruenceOperator(a)) {
    a = replace(flatten(a));
  }
  if(isCongruenceOperator(b)) {
    b = replace(flatten(b));
  }

  PendingProofList_t pending;
  UnionFind_t unionFind;
  std::list<Node> terms;

  pending.push_back(std::make_pair(a, b));

  Trace("cc") << "CC EXPLAINING " << a << " == " << b << std::endl;

  do {// while(!pending.empty())
    std::pair<Node, Node> eq = pending.front();
    pending.pop_front();

    a = eq.first;
    b = eq.second;

    Node c = nearestCommonAncestor(a, b, unionFind);

    explainAlongPath(a, c, pending, unionFind, terms);
    explainAlongPath(b, c, pending, unionFind, terms);
  } while(!pending.empty());

  if(Trace.isOn("cc")) {
    Trace("cc") << "CC EXPLAIN final proof has size " << terms.size() << std::endl;
  }

  NodeBuilder<> pf(kind::AND);
  while(!terms.empty()) {
    Node p = terms.front();
    terms.pop_front();
    Trace("cc") << "CC EXPLAIN " << p << std::endl;
    p = proofRewrite(p);
    Trace("cc") << "   rewrite " << p << std::endl;
    if(!p.isNull()) {
      pf << p;
    }
  }

  Trace("cc") << "CC EXPLAIN done" << std::endl;

  Assert(pf.getNumChildren() > 0);

  if(pf.getNumChildren() == 1) {
    d_explanationLength.addEntry(1.0);
    return pf[0];
  } else {
    d_explanationLength.addEntry(double(pf.getNumChildren()));
    return pf;
  }
}/* explain() */


template <class OutputChannel, class CongruenceOperatorList>
std::ostream& operator<<(std::ostream& out,
                         const CongruenceClosure<OutputChannel, CongruenceOperatorList>& cc) {
  out << "==============================================" << std::endl;

  /*out << "Representatives:" << std::endl;
  for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::RepresentativeMap::const_iterator i = cc.d_representative.begin(); i != cc.d_representative.end(); ++i) {
    out << "  " << (*i).first << " => " << (*i).second << std::endl;
  }*/

  out << "ClassLists:" << std::endl;
  for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::ClassLists::const_iterator i = cc.d_classList.begin(); i != cc.d_classList.end(); ++i) {
    if(cc.find((*i).first) == (*i).first) {
      out << "  " << (*i).first << " =>" << std::endl;
      for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::ClassList::const_iterator j = (*i).second->begin(); j != (*i).second->end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }

  out << "UseLists:" << std::endl;
  for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::UseLists::const_iterator i = cc.d_useList.begin(); i != cc.d_useList.end(); ++i) {
    if(cc.find((*i).first) == (*i).first) {
      out << "  " << (*i).first << " =>" << std::endl;
      for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::UseList::const_iterator j = (*i).second->begin(); j != (*i).second->end(); ++j) {
        out << "      " << *j << std::endl;
      }
    }
  }

  out << "Lookup:" << std::endl;
  for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::LookupMap::const_iterator i = cc.d_lookup.begin(); i != cc.d_lookup.end(); ++i) {
    TNode n = (*i).second;
    out << "  " << (*i).first << " => " << n << std::endl;
  }

  out << "Care set:" << std::endl;
  for(typename CongruenceClosure<OutputChannel, CongruenceOperatorList>::CareSet::const_iterator i = cc.d_careSet.begin(); i != cc.d_careSet.end(); ++i) {
    out << "  " << *i << std::endl;
  }

  out << "==============================================" << std::endl;

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */
