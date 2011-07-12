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

#include "util/ite_removal.h"

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

  if(Options::current()->theoryRegistration &&
     !fact.getAttribute(RegisteredAttr()) &&
     d_engine->d_needRegistration) {
    list<TNode> toReg;
    toReg.push_back(fact);

    Trace("theory") << "Theory::get(): registering new atom" << endl;

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
  d_activeTheories(0),
  d_needRegistration(false),
  d_theoryOut(this, ctxt),
  d_hasShutDown(false),
  d_incomplete(ctxt, false),
  d_statistics() {

  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_theoryTable[theoryId] = NULL;
    d_theoryIsActive[theoryId] = false;
  }

  Rewriter::init();

  d_sharedTermManager = new SharedTermManager(this, ctxt);
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_theoryTable[theoryId] != NULL) {
      delete d_theoryTable[theoryId];
    }
  }

  delete d_sharedTermManager;
}

struct preregister_stack_element {
  TNode node;
  bool children_added;
  preregister_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */

void TheoryEngine::preRegister(TNode preprocessed) {
  // If we are pre-registered already we are done
  if (preprocessed.getAttribute(PreRegistered())) {
    return;
  }

  // Do a topological sort of the subexpressions and preregister them
  vector<preregister_stack_element> toVisit;
  toVisit.push_back((TNode) preprocessed);
  while (!toVisit.empty()) {
    preregister_stack_element& stackHead = toVisit.back();
    // The current node we are processing
    TNode current = stackHead.node;
    // If we already added all the children its time to register or just
    // pop from the stack
    if (stackHead.children_added || current.getAttribute(PreRegistered())) {
      if (!current.getAttribute(PreRegistered())) {
        // Mark it as registered
        current.setAttribute(PreRegistered(), true);
        // Register this node
        if (current.getKind() == kind::EQUAL) {
          if(d_logic == "QF_AX") {
            d_theoryTable[theory::THEORY_ARRAY]->preRegisterTerm(current);
          } else {
            Theory* theory = theoryOf(current);
            TheoryId theoryLHS = theory->getId();
            Trace("register") << "preregistering " << current
                              << " with " << theoryLHS << std::endl;
            markActive(theoryLHS);
            theory->preRegisterTerm(current);
          }
        } else {
          TheoryId theory = theoryIdOf(current);
          Trace("register") << "preregistering " << current
                            << " with " << theory << std::endl;
          markActive(theory);
          d_theoryTable[theory]->preRegisterTerm(current);
          TheoryId typeTheory = theoryIdOf(current.getType());
          if (theory != typeTheory) {
            Trace("register") << "preregistering " << current
                              << " with " << typeTheory << std::endl;
            markActive(typeTheory);
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
  if (theory::TheoryTraits<THEORY>::hasCheck && d_theoryIsActive[THEORY]) { \
     reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->check(effort); \
     if (!d_theoryOut.d_conflictNode.get().isNull()) { \
       return false; \
     } \
  }

  // Do the checking
  try {
    CVC4_FOR_EACH_THEORY;
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::check() => conflict" << std::endl;
  }

  return true;
}

void TheoryEngine::propagate() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate && d_theoryIsActive[THEORY]) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->propagate(theory::Theory::FULL_EFFORT); \
  }

  // Propagate for each theory using the statement above
  CVC4_FOR_EACH_THEORY;
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
  // NOTE that we don't look at d_theoryIsActive[] here.  First of
  // all, we haven't done any pre-registration yet, so we don't know
  // which theories are active.  Second, let's give each theory a shot
  // at doing something with the input formula, even if it wouldn't
  // otherwise be active.

  d_theoryOut.d_conflictNode = Node::null();
  d_theoryOut.d_propagatedLiterals.clear();

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPresolve) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->presolve(); \
      if(!d_theoryOut.d_conflictNode.get().isNull()) { \
        return true; \
      } \
    }

    // Presolve for each theory using the statement above
    CVC4_FOR_EACH_THEORY;
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::presolve() => interrupted" << endl;
  }
  // return whether we have a conflict
  return !d_theoryOut.d_conflictNode.get().isNull();
}


void TheoryEngine::notifyRestart() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasNotifyRestart && d_theoryIsActive[THEORY]) { \
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->notifyRestart(); \
  }

  // notify each theory using the statement above
  CVC4_FOR_EACH_THEORY;
}

void TheoryEngine::staticLearning(TNode in, NodeBuilder<>& learned) {
  // NOTE that we don't look at d_theoryIsActive[] here.  First of
  // all, we haven't done any pre-registration yet, so we don't know
  // which theories are active.  Second, let's give each theory a shot
  // at doing something with the input formula, even if it wouldn't
  // otherwise be active.

  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasStaticLearning) { \
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->staticLearning(in, learned); \
  }

  // static learning for each theory using the statement above
  CVC4_FOR_EACH_THEORY;
}

bool TheoryEngine::hasRegisterTerm(TheoryId th) const {
  switch(th) {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  case THEORY: \
    return theory::TheoryTraits<THEORY>::hasRegisterTerm;

    CVC4_FOR_EACH_THEORY
  default:
    Unhandled(th);
  }
}

theory::Theory::SolveStatus TheoryEngine::solve(TNode literal, SubstitutionMap& substitionOut) {
  TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
  Trace("theory") << "TheoryEngine::solve(" << literal << "): solving with " << theoryOf(atom)->getId() << std::endl;
  Theory::SolveStatus solveStatus = theoryOf(atom)->solve(literal, substitionOut);
  Trace("theory") << "TheoryEngine::solve(" << literal << ") => " << solveStatus << std::endl;
  return solveStatus;
}

struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */


Node TheoryEngine::preprocess(TNode assertion) {

  Trace("theory") << "TheoryEngine::preprocess(" << assertion << ")" << std::endl;

    // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    Debug("theory::internal") << "TheoryEngine::preprocess(" << assertion << "): processing " << current << std::endl;

    // If node already in the cache we're done, pop from the stack
    NodeMap::iterator find = d_atomPreprocessingCache.find(current);
    if (find != d_atomPreprocessingCache.end()) {
      toVisit.pop_back();
      continue;
    }

    // If this is an atom, we preprocess it with the theory
    if (theoryIdOf(current) != THEORY_BOOL) {
      d_atomPreprocessingCache[current] = theoryOf(current)->preprocess(current);
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.children_added) {
      // Children have been processed, so substitute
      NodeBuilder<> builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(d_atomPreprocessingCache.find(current[i]) != d_atomPreprocessingCache.end());
        builder << d_atomPreprocessingCache[current[i]];
      }
      // Mark the substitution and continue
      Node result = builder;
      Debug("theory::internal") << "TheoryEngine::preprocess(" << assertion << "): setting " << current << " -> " << result << std::endl;
      d_atomPreprocessingCache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_atomPreprocessingCache.find(childNode);
          if (childFind == d_atomPreprocessingCache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << assertion << "): setting " << current << " -> " << current << std::endl;
        d_atomPreprocessingCache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return d_atomPreprocessingCache[assertion];
}


}/* CVC4 namespace */
