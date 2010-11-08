/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): cconway, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine.
 **
 ** The theory engine.
 **/

#include <vector>
#include <list>

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "util/options.h"

#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/booleans/theory_bool.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/morgan/theory_uf_morgan.h"
#include "theory/uf/tim/theory_uf_tim.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {
namespace theory {

struct PreRegisteredTag {};
typedef expr::Attribute<PreRegisteredTag, bool> PreRegistered;

struct IteRewriteTag {};
typedef expr::Attribute<IteRewriteTag, Node> IteRewriteAttr;

}/* CVC4::theory namespace */

void TheoryEngine::EngineOutputChannel::newFact(TNode fact) {
  //FIXME: Assert(fact.isLiteral(), "expected literal");
  if (fact.getKind() == kind::NOT) {
    // No need to register negations - only atoms
    fact = fact[0];
// FIXME: In future, might want to track disequalities in shared term manager
//     if (fact.getKind() == kind::EQUAL) {
//       d_engine->getSharedTermManager()->addDiseq(fact);
//     }
  }
  else if (fact.getKind() == kind::EQUAL) {
    // Automatically track all asserted equalities in the shared term manager
    d_engine->getSharedTermManager()->addEq(fact);
  }

  if(d_engine->d_theoryRegistration && !fact.getAttribute(RegisteredAttr())) {
    list<TNode> toReg;
    toReg.push_back(fact);

    Debug("theory") << "Theory::get(): registering new atom" << endl;

    /* Essentially this is doing a breadth-first numbering of
     * non-registered subterms with children.  Any non-registered
     * leaves are immediately registered. */
    for(list<TNode>::iterator workp = toReg.begin();
        workp != toReg.end();
        ++workp) {

      TNode n = *workp;
      Theory* thParent = d_engine->theoryOf(n);

      for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
        TNode c = *i;
        Theory* thChild = d_engine->theoryOf(c);

        if (thParent != thChild) {
          d_engine->getSharedTermManager()->addTerm(c, thParent, thChild);
        }
        if(! c.getAttribute(RegisteredAttr())) {
          if(c.getNumChildren() == 0) {
            c.setAttribute(RegisteredAttr(), true);
            thChild->registerTerm(c);
          } else {
            toReg.push_back(c);
          }
        }
      }
    }

    /* Now register the list of terms in reverse order.  Between this
     * and the above registration of leaves, this should ensure that
     * all subterms in the entire tree were registered in
     * reverse-topological order. */
    for(list<TNode>::reverse_iterator i = toReg.rbegin();
        i != toReg.rend();
        ++i) {

      TNode n = *i;

      /* Note that a shared TNode in the DAG rooted at "fact" could
       * appear twice on the list, so we have to avoid hitting it
       * twice. */
      // FIXME when ExprSets are online, use one of those to avoid
      // duplicates in the above?
      // Actually, that doesn't work because you have to make sure 
      // that the *last* occurrence is the one that gets processed first @CB
      // This could be a big performance problem though because it requires
      // traversing a DAG as a tree and that can really blow up @CB
      if(! n.getAttribute(RegisteredAttr())) {
        n.setAttribute(RegisteredAttr(), true);
        d_engine->theoryOf(n)->registerTerm(n);
      }
    }
  }/* d_engine->d_theoryRegistration && !fact.getAttribute(RegisteredAttr()) */
}

TheoryEngine::TheoryEngine(context::Context* ctxt, const Options& opts) :
  d_propEngine(NULL),
  d_theoryOut(this, ctxt),
  d_theoryRegistration(opts.theoryRegistration),
  d_hasShutDown(false),
  d_incomplete(ctxt, false),
  d_statistics() {

  d_sharedTermManager = new SharedTermManager(this, ctxt);

  d_builtin = new theory::builtin::TheoryBuiltin(0, ctxt, d_theoryOut);
  d_bool = new theory::booleans::TheoryBool(1, ctxt, d_theoryOut);
  switch(opts.uf_implementation) {
  case Options::TIM:
    d_uf = new theory::uf::tim::TheoryUFTim(2, ctxt, d_theoryOut);
    break;
  case Options::MORGAN:
    d_uf = new theory::uf::morgan::TheoryUFMorgan(2, ctxt, d_theoryOut);
    break;
  default:
    Unhandled(opts.uf_implementation);
  }
  d_arith = new theory::arith::TheoryArith(3, ctxt, d_theoryOut);
  d_arrays = new theory::arrays::TheoryArrays(4, ctxt, d_theoryOut);
  d_bv = new theory::bv::TheoryBV(5, ctxt, d_theoryOut);

  d_sharedTermManager->registerTheory(static_cast<theory::builtin::TheoryBuiltin*>(d_builtin));
  d_sharedTermManager->registerTheory(static_cast<theory::booleans::TheoryBool*>(d_bool));
  d_sharedTermManager->registerTheory(static_cast<theory::uf::TheoryUF*>(d_uf));
  d_sharedTermManager->registerTheory(static_cast<theory::arith::TheoryArith*>(d_arith));
  d_sharedTermManager->registerTheory(static_cast<theory::arrays::TheoryArrays*>(d_arrays));
  d_sharedTermManager->registerTheory(static_cast<theory::bv::TheoryBV*>(d_bv));

  d_theoryOfTable.registerTheory(static_cast<theory::builtin::TheoryBuiltin*>(d_builtin));
  d_theoryOfTable.registerTheory(static_cast<theory::booleans::TheoryBool*>(d_bool));
  d_theoryOfTable.registerTheory(static_cast<theory::uf::TheoryUF*>(d_uf));
  d_theoryOfTable.registerTheory(static_cast<theory::arith::TheoryArith*>(d_arith));
  d_theoryOfTable.registerTheory(static_cast<theory::arrays::TheoryArrays*>(d_arrays));
  d_theoryOfTable.registerTheory(static_cast<theory::bv::TheoryBV*>(d_bv));
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  delete d_bv;
  delete d_arrays;
  delete d_arith;
  delete d_uf;
  delete d_bool;
  delete d_builtin;

  delete d_sharedTermManager;
}

Theory* TheoryEngine::theoryOf(TypeNode t) {
  // FIXME: we don't yet have a Type-to-Theory map.  When we do,
  // look up the type of the var and return that Theory (?)

  // The following JUST hacks around this lack of a table
  Kind k = t.getKind();
  if(k == kind::TYPE_CONSTANT) {
    switch(TypeConstant tc = t.getConst<TypeConstant>()) {
    case BOOLEAN_TYPE:
      return d_theoryOfTable[kind::CONST_BOOLEAN];
    case INTEGER_TYPE:
      return d_theoryOfTable[kind::CONST_INTEGER];
    case REAL_TYPE:
      return d_theoryOfTable[kind::CONST_RATIONAL];
    case KIND_TYPE:
    default:
      Unhandled(tc);
    }
  }

  return d_theoryOfTable[k];
}


Theory* TheoryEngine::theoryOf(TNode n) {
  Kind k = n.getKind();

  Assert(k >= 0 && k < kind::LAST_KIND);

  if(n.getMetaKind() == kind::metakind::VARIABLE) {
    return theoryOf(n.getType());
  } else if(k == kind::EQUAL) {
    // equality is special: use LHS
    return theoryOf(n[0]);
  } else {
    // use our Kind-to-Theory mapping
    return d_theoryOfTable[k];
  }
}

Node TheoryEngine::preprocess(TNode t) {
  Node top = rewrite(t);
  Debug("rewrite") << "rewrote: " << t << endl << "to     : " << top << endl;

  list<TNode> toReg;
  toReg.push_back(top);

  /* Essentially this is doing a breadth-first numbering of
   * non-registered subterms with children.  Any non-registered
   * leaves are immediately registered. */
  for(list<TNode>::iterator workp = toReg.begin();
      workp != toReg.end();
      ++workp) {

    TNode n = *workp;

    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      TNode c = *i;

      if(!c.getAttribute(theory::PreRegistered())) {// c not yet registered
        if(c.getNumChildren() == 0) {
          c.setAttribute(theory::PreRegistered(), true);
          theoryOf(c)->preRegisterTerm(c);
        } else {
          toReg.push_back(c);
        }
      }
    }
  }

  /* Now register the list of terms in reverse order.  Between this
   * and the above registration of leaves, this should ensure that
   * all subterms in the entire tree were registered in
   * reverse-topological order. */
  for(list<TNode>::reverse_iterator i = toReg.rbegin();
      i != toReg.rend();
      ++i) {

    TNode n = *i;

    /* Note that a shared TNode in the DAG rooted at "fact" could
     * appear twice on the list, so we have to avoid hitting it
     * twice. */
    // FIXME when ExprSets are online, use one of those to avoid
    // duplicates in the above?
    if(!n.getAttribute(theory::PreRegistered())) {
      n.setAttribute(theory::PreRegistered(), true);
      theoryOf(n)->preRegisterTerm(n);
    }
  }

  return top;
}

/* Our goal is to tease out any ITE's sitting under a theory operator. */
Node TheoryEngine::removeITEs(TNode node) {
  Debug("ite") << "removeITEs(" << node << ")" << endl;

  /* The result may be cached already */
  Node cachedRewrite;
  NodeManager *nodeManager = NodeManager::currentNM();
  if(nodeManager->getAttribute(node, theory::IteRewriteAttr(), cachedRewrite)) {
    Debug("ite") << "removeITEs: in-cache: " << cachedRewrite << endl;
    return cachedRewrite.isNull() ? Node(node) : cachedRewrite;
  }

  if(node.getKind() == kind::ITE){
    Assert( node.getNumChildren() == 3 );
    TypeNode nodeType = node[1].getType();
    if(!nodeType.isBoolean()){
      Node skolem = nodeManager->mkVar(node.getType());
      Node newAssertion =
        nodeManager->mkNode(kind::ITE,
                            node[0],
                            nodeManager->mkNode(kind::EQUAL, skolem, node[1]),
                            nodeManager->mkNode(kind::EQUAL, skolem, node[2]));
      nodeManager->setAttribute(node, theory::IteRewriteAttr(), skolem);

      Debug("ite") << "removeITEs([" << node.getId() << "," << node << "])"
                   << "->"
                   << "["<<newAssertion.getId() << "," << newAssertion << "]"
                   << endl;

      Node preprocessed = preprocess(newAssertion);
      d_propEngine->assertFormula(preprocessed);

      return skolem;
    }
  }
  vector<Node> newChildren;
  bool somethingChanged = false;
  for(TNode::const_iterator it = node.begin(), end = node.end();
      it != end;
      ++it) {
    Node newChild = removeITEs(*it);
    somethingChanged |= (newChild != *it);
    newChildren.push_back(newChild);
  }

  if(somethingChanged) {
    cachedRewrite = nodeManager->mkNode(node.getKind(), newChildren);
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), cachedRewrite);
    return cachedRewrite;
  } else {
    nodeManager->setAttribute(node, theory::IteRewriteAttr(), Node::null());
    return node;
  }
}

namespace theory {
namespace rewrite {

/**
 * TheoryEngine::rewrite() keeps a stack of things that are being pre-
 * and post-rewritten.  Each element of the stack is a
 * RewriteStackElement.
 */
struct RewriteStackElement {
  /**
   * The node at this rewrite level.  For example (AND (OR x y) z)
   * will have, as it's rewriting x, the stack:
   *    x
   *    (OR x y)
   *    (AND (OR x y) z)
   */
  Node d_node;

  /**
   * The theory associated to d_node.  Cached here to avoid having to
   * look it up again.
   */
  Theory* d_theory;

  /**
   * Whether or not this was a top-level rewrite.  Note that at theory
   * boundaries, topLevel is forced to true, so it's not the case that
   * this is true only at the lowest stack level.
   */
  bool d_topLevel;

  /**
   * A saved index to the "next child" to pre- and post-rewrite.  In
   * the case when (AND (OR x y) z) is being rewritten, the AND, OR,
   * and x are pre-rewritten, then (assuming they don't change), x is
   * post-rewritten, then y is pre- and post-rewritten, then the OR is
   * post-rewritten, then z is pre-rewritten, then the AND is
   * post-rewritten.  At each stack level, we need to remember the
   * child index we're currently processing.
   */
  int d_nextChild;

  /**
   * A (re)builder for this node.  As this node's children are
   * post-rewritten, in order, they append to this builder.  When this
   * node is post-rewritten, it is reformed from d_builder since the
   * children may have changed.  Note Nodes aren't rebuilt if they
   * have metakinds CONSTANT (which is illegal) or VARIABLE (which
   * would create a fresh variable, not what we want)---which is fine,
   * since those types don't have children anyway.
   */
  NodeBuilder<> d_builder;

  /**
   * Construct a fresh stack element.
   */
  RewriteStackElement(Node n, Theory* thy, bool topLevel) :
    d_node(n),
    d_theory(thy),
    d_topLevel(topLevel),
    d_nextChild(0) {
  }
};

}/* CVC4::theory::rewrite namespace */
}/* CVC4::theory namespace */

Node TheoryEngine::rewrite(TNode in, bool topLevel) {
  using theory::rewrite::RewriteStackElement;

  Node noItes = removeITEs(in);
  Node out;

  Debug("theory-rewrite") << "removeITEs of: " << in << endl
                          << "           is: " << noItes << endl;

  // descend top-down into the theory rewriters
  vector<RewriteStackElement> stack;
  stack.push_back(RewriteStackElement(noItes, theoryOf(noItes), topLevel));
  Debug("theory-rewrite") << "TheoryEngine::rewrite() starting at" << endl
                          << "  " << noItes << " " << theoryOf(noItes)
                          << " " << (topLevel ? "TOP-LEVEL " : "")
                          << "0" << endl;
  // This whole thing is essentially recursive, but we avoid actually
  // doing any recursion.
  do {// do until the stack is empty..
    RewriteStackElement& rse = stack.back();
    bool done;

    Debug("theory-rewrite") << "rewriter looking at level " << stack.size()
                            << endl
                            << "  " << rse.d_node << " " << rse.d_theory
                            << "[" << *rse.d_theory << "]"
                            << " " << (rse.d_topLevel ? "TOP-LEVEL " : "")
                            << rse.d_nextChild << endl;

    if(rse.d_nextChild == 0) {
      Node original = rse.d_node;
      bool wasTopLevel = rse.d_topLevel;
      Node cached = getPreRewriteCache(original, wasTopLevel);
      if(cached.isNull()) {
        do {
          Debug("theory-rewrite") << "doing pre-rewrite in " << *rse.d_theory
                                  << " topLevel==" << rse.d_topLevel << endl;
          RewriteResponse response =
            rse.d_theory->preRewrite(rse.d_node, rse.d_topLevel);
          rse.d_node = response.getNode();
          Assert(!rse.d_node.isNull(), "node illegally rewritten to null");
          Theory* thy2 = theoryOf(rse.d_node);
          Assert(thy2 != NULL, "node illegally rewritten to null theory");
          Debug("theory-rewrite") << "got back " << rse.d_node << " "
                                  << thy2 << "[" << *thy2 << "]"
                                  << (response.needsMoreRewriting() ?
                                      (response.needsFullRewriting() ?
                                       " FULL-REWRITING" : " MORE-REWRITING")
                                      : " DONE")
                                  << endl;
          if(rse.d_theory != thy2) {
            Debug("theory-rewrite") << "pre-rewritten from " << *rse.d_theory
                                    << " into " << *thy2
                                    << ", marking top-level and !done" << endl;
            rse.d_theory = thy2;
            done = false;
            // FIXME how to handle the "top-levelness" of a node that's
            // rewritten from theory T1 into T2, then back to T1 ?
            rse.d_topLevel = true;
          } else {
            done = response.isDone();
          }
        } while(!done);
        setPreRewriteCache(original, wasTopLevel, rse.d_node);
      } else {// is in pre-rewrite cache
        Debug("theory-rewrite") << "in pre-cache: " << cached << endl;
        rse.d_node = cached;
        Theory* thy2 = theoryOf(cached);
        if(rse.d_theory != thy2) {
          Debug("theory-rewrite") << "[cache-]pre-rewritten from "
                                  << *rse.d_theory << " into " << *thy2
                                  << ", marking top-level" << endl;
          rse.d_theory = thy2;
          rse.d_topLevel = true;
        }
      }
    }

    // children
    Node original = rse.d_node;
    bool wasTopLevel = rse.d_topLevel;
    Node cached = getPostRewriteCache(original, wasTopLevel);

    if(cached.isNull()) {
      unsigned nch = rse.d_nextChild++;

      if(nch == 0 &&
         rse.d_node.getMetaKind() == kind::metakind::PARAMETERIZED) {
        // this is an apply, so we have to push the operator
        TNode op = rse.d_node.getOperator();
        Debug("theory-rewrite") << "pushing operator " << op
                                << " of " << rse.d_node << endl;
        rse.d_builder << op;
      }

      if(nch < rse.d_node.getNumChildren()) {
        Debug("theory-rewrite") << "pushing child " << nch
                                << " of " << rse.d_node << endl;
        Node c = rse.d_node[nch];
        Theory* t = theoryOf(c);
        stack.push_back(RewriteStackElement(c, t, t != rse.d_theory));
        continue;// break out of this node, do its child
      }

      // incorporate the children's rewrites
      if(rse.d_node.getMetaKind() != kind::metakind::VARIABLE &&
         rse.d_node.getMetaKind() != kind::metakind::CONSTANT) {
        Debug("theory-rewrite") << "builder here is " << &rse.d_builder
                                << " and it gets " << rse.d_node.getKind()
                                << endl;
        rse.d_builder << rse.d_node.getKind();
        rse.d_node = Node(rse.d_builder);
      }

      // post-rewriting
      do {
        Debug("theory-rewrite") << "doing post-rewrite of "
                                << rse.d_node << endl
                                << " in " << *rse.d_theory
                                << " topLevel==" << rse.d_topLevel << endl;
        RewriteResponse response =
          rse.d_theory->postRewrite(rse.d_node, rse.d_topLevel);
        rse.d_node = response.getNode();
        Assert(!rse.d_node.isNull(), "node illegally rewritten to null");
        Theory* thy2 = theoryOf(rse.d_node);
        Assert(thy2 != NULL, "node illegally rewritten to null theory");
        Debug("theory-rewrite") << "got back " << rse.d_node << " "
                                << thy2 << "[" << *thy2 << "]"
                                << (response.needsMoreRewriting() ?
                                    (response.needsFullRewriting() ?
                                     " FULL-REWRITING" : " MORE-REWRITING")
                                    : " DONE")
                                << endl;
        if(rse.d_theory != thy2) {
          Debug("theory-rewrite") << "post-rewritten from " << *rse.d_theory
                                  << " into " << *thy2
                                  << ", marking top-level and !done" << endl;
          rse.d_theory = thy2;
          done = false;
          // FIXME how to handle the "top-levelness" of a node that's
          // rewritten from theory T1 into T2, then back to T1 ?
          rse.d_topLevel = true;
        } else {
          done = response.isDone();
        }
        if(response.needsFullRewriting()) {
          Debug("theory-rewrite") << "full-rewrite requested for node "
                                  << rse.d_node.getId() << ", invoking..."
                                  << endl;
          Node n = rewrite(rse.d_node, rse.d_topLevel);
          Debug("theory-rewrite") << "full-rewrite finished for node "
                                  << rse.d_node.getId() << ", got node "
                                  << n << " output." << endl;
          rse.d_node = n;
          done = true;
        }
      } while(!done);

      /* If extra-checking is on, do _another_ rewrite before putting
       * in the cache to make sure they are the same.  This is
       * especially necessary if a theory post-rewrites something into
       * a term of another theory. */
      if(Debug.isOn("extra-checking") &&
         !Debug.isOn("$extra-checking:inside-rewrite")) {
        ScopedDebug d("$extra-checking:inside-rewrite");
        Node rewrittenAgain = rewrite(rse.d_node, rse.d_topLevel);
        Assert(rewrittenAgain == rse.d_node,
               "\nExtra-checking assumption failed, "
               "node is not completely rewritten.\n\n"
               "Original : %s\n"
               "Rewritten: %s\n"
               "Again    : %s\n",
               original.toString().c_str(),
               rse.d_node.toString().c_str(),
               rewrittenAgain.toString().c_str());
      }
      setPostRewriteCache(original, wasTopLevel, rse.d_node);

      out = rse.d_node;
    } else {
      Debug("theory-rewrite") << "in post-cache: " << cached << endl;
      out = cached;
      Theory* thy2 = theoryOf(cached);
      if(rse.d_theory != thy2) {
        Debug("theory-rewrite") << "[cache-]post-rewritten from "
                                << *rse.d_theory << " into " << *thy2 << endl;
        rse.d_theory = thy2;
      }
    }

    stack.pop_back();
    if(!stack.empty()) {
      Debug("theory-rewrite") << "asserting " << out << " to previous builder "
                              << &stack.back().d_builder << endl;
      stack.back().d_builder << out;
    }
  } while(!stack.empty());

  Debug("theory-rewrite") << "DONE with theory rewriter." << endl;
  Debug("theory-rewrite") << "result is:" << endl << out << endl;

  return out;
}/* TheoryEngine::rewrite(TNode in) */


Node TheoryEngine::getValue(TNode node) {
  kind::MetaKind metakind = node.getMetaKind();
  // special case: prop engine handles boolean vars
  if(metakind == kind::metakind::VARIABLE && node.getType().isBoolean()) {
    return d_propEngine->getValue(node);
  }
  // special case: value of a constant == itself
  if(metakind == kind::metakind::CONSTANT) {
    return node;
  }

  // otherwise ask the theory-in-charge
  return theoryOf(node)->getValue(node, this);
}/* TheoryEngine::getValue(TNode node) */

}/* CVC4 namespace */
