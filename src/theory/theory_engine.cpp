/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett, dejan
 ** Minor contributors (to current version): cconway, taking
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

#include "util/node_visitor.h"
#include "util/ite_removal.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

TheoryEngine::TheoryEngine(context::Context* ctxt) :
  d_propEngine(NULL),
  d_context(ctxt),
  d_activeTheories(0),
  d_atomPreprocessingCache(),
  d_possiblePropagations(),
  d_hasPropagated(ctxt),
  d_theoryOut(this, ctxt),
  d_sharedTermManager(NULL),
  d_hasShutDown(false),
  d_incomplete(ctxt, false),
  d_logic(""),
  d_statistics(),
  d_preRegistrationVisitor(*this, ctxt) {

  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    d_theoryTable[theoryId] = NULL;
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

void TheoryEngine::setLogic(std::string logic) {
  Assert(d_logic.empty());
  // Set the logic
  d_logic = logic;
}

struct preregister_stack_element {
  TNode node;
  bool children_added;
  preregister_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */

void TheoryEngine::preRegister(TNode preprocessed) {
  if(Dump.isOn("missed-t-propagations")) {
    d_possiblePropagations.push_back(preprocessed);
  }

  NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, preprocessed);
}

/**
 * Check all (currently-active) theories for conflicts.
 * @param effort the effort level to use
 */
void TheoryEngine::check(theory::Theory::Effort effort) {

  d_theoryOut.d_propagatedLiterals.clear();

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasCheck && isActive(THEORY)) { \
     reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->check(effort); \
     if (d_theoryOut.d_inConflict) { \
       return; \
     } \
  }

  // Do the checking
  try {
    CVC4_FOR_EACH_THEORY;

    if(Dump.isOn("missed-t-conflicts")) {
      Dump("missed-t-conflicts")
        << CommentCommand("Completeness check for T-conflicts; expect sat") << endl
        << CheckSatCommand() << endl;
    }
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::check() => conflict" << endl;
  }
}

void TheoryEngine::propagate() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate && isActive(THEORY)) { \
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->propagate(theory::Theory::FULL_EFFORT); \
  }

  // Propagate for each theory using the statement above
  CVC4_FOR_EACH_THEORY;

  if(Dump.isOn("missed-t-propagations")) {
    for(vector<TNode>::iterator i = d_possiblePropagations.begin();
        i != d_possiblePropagations.end();
        ++i) {
      if(d_hasPropagated.find(*i) == d_hasPropagated.end()) {
        Dump("missed-t-propagations")
          << CommentCommand("Completeness check for T-propagations; expect invalid") << endl
          << QueryCommand((*i).toExpr()) << endl;
      }
    }
  }
}

Node TheoryEngine::getExplanation(TNode node, theory::Theory* theory) {
  theory->explain(node);
  if(Dump.isOn("t-explanations")) {
    Dump("t-explanations")
      << CommentCommand(string("theory explanation from ") +
                        theory->identify() + ": expect valid") << endl
      << QueryCommand(d_theoryOut.d_explanationNode.get().impNode(node).toExpr())
      << endl;
  }
  Assert(properExplanation(node, d_theoryOut.d_explanationNode.get()));
  return d_theoryOut.d_explanationNode;
}

bool TheoryEngine::properConflict(TNode conflict) const {
  Assert(!conflict.isNull());
#warning fixme
  return true;
}

bool TheoryEngine::properPropagation(TNode lit) const {
  Assert(!lit.isNull());
#warning fixme
  return true;
}

bool TheoryEngine::properExplanation(TNode node, TNode expl) const {
  Assert(!node.isNull() && !expl.isNull());
#warning fixme
  return true;
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

  d_theoryOut.d_propagatedLiterals.clear();

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPresolve) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(d_theoryTable[THEORY])->presolve(); \
      if(d_theoryOut.d_inConflict) { \
        return true; \
      } \
    }

    // Presolve for each theory using the statement above
    CVC4_FOR_EACH_THEORY;
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::presolve() => interrupted" << endl;
  }
  // return whether we have a conflict
  return false;
}


void TheoryEngine::notifyRestart() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasNotifyRestart && isActive(THEORY)) { \
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

void TheoryEngine::shutdown() {
  // Set this first; if a Theory shutdown() throws an exception,
  // at least the destruction of the TheoryEngine won't confound
  // matters.
  d_hasShutDown = true;

  // Shutdown all the theories
  for(unsigned theoryId = 0; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_theoryTable[theoryId]) {
      d_theoryTable[theoryId]->shutdown();
    }
  }

  theory::Rewriter::shutdown();
}

theory::Theory::SolveStatus TheoryEngine::solve(TNode literal, SubstitutionMap& substitionOut) {
  TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
  Trace("theory") << "TheoryEngine::solve(" << literal << "): solving with " << theoryOf(atom)->getId() << endl;
  Theory::SolveStatus solveStatus = theoryOf(atom)->solve(literal, substitionOut);
  Trace("theory") << "TheoryEngine::solve(" << literal << ") => " << solveStatus << endl;
  return solveStatus;
}

struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */


Node TheoryEngine::preprocess(TNode assertion) {

  Trace("theory") << "TheoryEngine::preprocess(" << assertion << ")" << endl;

  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  while (!toVisit.empty())
  {
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    Debug("theory::internal") << "TheoryEngine::preprocess(" << assertion << "): processing " << current << endl;

    // If node already in the cache we're done, pop from the stack
    NodeMap::iterator find = d_atomPreprocessingCache.find(current);
    if (find != d_atomPreprocessingCache.end()) {
      toVisit.pop_back();
      continue;
    }

    // If this is an atom, we preprocess it with the theory
    if (Theory::theoryOf(current) != THEORY_BOOL) {
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
      Debug("theory::internal") << "TheoryEngine::preprocess(" << assertion << "): setting " << current << " -> " << result << endl;
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
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << assertion << "): setting " << current << " -> " << current << endl;
        d_atomPreprocessingCache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return d_atomPreprocessingCache[assertion];
}

