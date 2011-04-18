/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking, barrett, dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
#include "theory/rewriter.h"
#include "theory/theory_traits.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

namespace CVC4 {

namespace theory {

/** Tag for the "registerTerm()-has-been-called" flag on Nodes */
struct RegisteredAttrTag {};
/** The "registerTerm()-has-been-called" flag on Nodes */
typedef CVC4::expr::CDAttribute<RegisteredAttrTag, bool> RegisteredAttr;

struct PreRegisteredAttrTag {};
typedef expr::Attribute<PreRegisteredAttrTag, bool> PreRegistered;

struct IteRewriteAttrTag {};
typedef expr::Attribute<IteRewriteAttrTag, Node> IteRewriteAttr;

}/* CVC4::theory namespace */

void TheoryEngine::EngineOutputChannel::newFact(TNode fact) {
  TimerStat::CodeTimer codeTimer(d_newFactTimer);

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

  if(Options::current()->theoryRegistration && !fact.getAttribute(RegisteredAttr())) {
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
  }/* Options::current()->theoryRegistration && !fact.getAttribute(RegisteredAttr()) */
}

TheoryEngine::TheoryEngine(context::Context* ctxt) :
  d_propEngine(NULL),
  d_context(ctxt),
  d_theoryOut(this, ctxt),
  d_hasShutDown(false),
  d_incomplete(ctxt, false),
  d_statistics() {

  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_theoryTable[theoryId] = NULL;
  }

  Rewriter::init();

  d_sharedTermManager = new SharedTermManager(this, ctxt);
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_theoryTable[theoryId]) {
      delete d_theoryTable[theoryId];
    }
  }

  delete d_sharedTermManager;
}

struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};

Node TheoryEngine::preprocess(TNode node) {
  // Make sure the node is type-checked first (some rewrites depend on
  // typechecking having succeeded to be safe).
  if(Options::current()->typeChecking) {
    node.getType(true);
  }
  // Remove ITEs and rewrite the node
  Node preprocessed = Rewriter::rewrite(removeITEs(node));
  return preprocessed;
}

void TheoryEngine::preRegister(TNode preprocessed) {
  // If we are pre-registered already we are done
  if (preprocessed.getAttribute(PreRegistered())) {
    return;
  }

  // Do a topological sort of the subexpressions and preregister them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back((TNode) preprocessed);
  while (!toVisit.empty()) {
    preprocess_stack_element& stackHead = toVisit.back();
    // The current node we are processing
    TNode current = stackHead.node;
    // If we already added all the children its time to register or just pop from the stack
    if (stackHead.children_added || current.getAttribute(PreRegistered())) {
      if (!current.getAttribute(PreRegistered())) {
        // Mark it as registered
        current.setAttribute(PreRegistered(), true);
        // Register this node
        if (current.getKind() == kind::EQUAL) {
          TheoryId theoryLHS = Theory::theoryOf(current[0]);
          Debug("register") << "preregistering " << current << " with " << theoryLHS << std::endl;
          d_theoryTable[theoryLHS]->preRegisterTerm(current);
//          TheoryId theoryRHS = Theory::theoryOf(current[1]);
//          if (theoryLHS != theoryRHS) {
//            d_theoryTable[theoryRHS]->preRegisterTerm(current);
//            Debug("register") << "preregistering " << current << " with " << theoryRHS << std::endl;
//          }
//          TheoryId typeTheory = Theory::theoryOf(current[0].getType());
//          if (typeTheory != theoryLHS && typeTheory != theoryRHS) {
//            d_theoryTable[typeTheory]->preRegisterTerm(current);
//            Debug("register") << "preregistering " << current << " with " << typeTheory << std::endl;
//          }
        } else {
          TheoryId theory = Theory::theoryOf(current);
          Debug("register") << "preregistering " << current << " with " << theory << std::endl;
          d_theoryTable[theory]->preRegisterTerm(current);
          TheoryId typeTheory = Theory::theoryOf(current.getType());
          if (theory != typeTheory) {
            Debug("register") << "preregistering " << current << " with " << typeTheory << std::endl;
            d_theoryTable[typeTheory]->preRegisterTerm(current);
          }
        }
      }
      // Done with this node, remove from the stack
      toVisit.pop_back();
    } else {
      // Mark that we have added the children
      stackHead.children_added = true;
      // We need to add the children
      for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
        TNode childNode = *child_it;
        if (!childNode.getAttribute(PreRegistered())) {
          toVisit.push_back(childNode);
        }
      }
    }
  }
}

/**
 * Check all (currently-active) theories for conflicts.
 * @param effort the effort level to use
 */
bool TheoryEngine::check(theory::Theory::Effort effort) {
  d_theoryOut.d_conflictNode = Node::null();
  d_theoryOut.d_propagatedLiterals.clear();

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasCheck) { \
     reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->check(effort); \
     if (!d_theoryOut.d_conflictNode.get().isNull()) { \
       return false; \
     } \
  }

  // Do the checking
  try {
    CVC4_FOR_EACH_THEORY
  } catch(const theory::Interrupted&) {
    Debug("theory") << "TheoryEngine::check() => conflict" << std::endl;
  }

  return true;
}

void TheoryEngine::propagate() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->propagate(theory::Theory::FULL_EFFORT); \
  }

  // Propagate for each theory using the statement above
  CVC4_FOR_EACH_THEORY
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
    TypeNode nodeType = node.getType();
    if(!nodeType.isBoolean()){
      Node skolem = nodeManager->mkVar(nodeType);
      Node newAssertion =
        nodeManager->mkNode(kind::ITE,
                            node[0],
                            nodeManager->mkNode(kind::EQUAL, skolem, node[1]),
                            nodeManager->mkNode(kind::EQUAL, skolem, node[2]));
      nodeManager->setAttribute(node, theory::IteRewriteAttr(), skolem);

      Debug("ite") << "removeITEs([" << node.getId() << "," << node << "," << nodeType << "])"
                   << "->"
                   << "[" << newAssertion.getId() << "," << newAssertion << "]"
                   << endl;

      Node preprocessed = preprocess(newAssertion);
      d_propEngine->assertFormula(preprocessed);

      return skolem;
    }
  }
  vector<Node> newChildren;
  bool somethingChanged = false;
  if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
    // Make sure to push operator or it will be missing in new
    // (reformed) node.  This was crashing on the very simple input
    // "(f (ite c 0 1))"
    newChildren.push_back(node.getOperator());
  }
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
  return theoryOf(node)->getValue(node);
}/* TheoryEngine::getValue(TNode node) */

bool TheoryEngine::presolve() {
  d_theoryOut.d_conflictNode = Node::null();
  d_theoryOut.d_propagatedLiterals.clear();
  try {
    for(unsigned i = 0; i < THEORY_LAST; ++ i) {
        d_theoryTable[i]->presolve();
        if(!d_theoryOut.d_conflictNode.get().isNull()) {
          return true;
	}
     }
  } catch(const theory::Interrupted&) {
    Debug("theory") << "TheoryEngine::presolve() => interrupted" << endl;
  }
  // return whether we have a conflict
  return !d_theoryOut.d_conflictNode.get().isNull();
}


void TheoryEngine::notifyRestart() {
  for(unsigned i = 0; i < THEORY_LAST; ++ i) {
    if (d_theoryTable[i]) {
      d_theoryTable[i]->notifyRestart();
    }
  }
}


void TheoryEngine::staticLearning(TNode in, NodeBuilder<>& learned) {
  for(unsigned i = 0; i < THEORY_LAST; ++ i) {
    if (d_theoryTable[i]) {
      d_theoryTable[i]->staticLearning(in, learned);
    }
  }
}


}/* CVC4 namespace */
