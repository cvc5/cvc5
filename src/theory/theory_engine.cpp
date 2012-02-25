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

TheoryEngine::TheoryEngine(context::Context* context,
                           context::UserContext* userContext)
: d_propEngine(NULL),
  d_context(context),
  d_userContext(userContext),
  d_activeTheories(context, 0),
  d_sharedTerms(context),
  d_atomPreprocessingCache(),
  d_possiblePropagations(),
  d_hasPropagated(context),
  d_inConflict(context, false),
  d_sharedTermsExist(context, false),
  d_hasShutDown(false),
  d_incomplete(context, false),
  d_sharedAssertions(context),
  d_propagatedLiterals(context),
  d_propagatedLiteralsIndex(context, 0),
  d_decisionRequests(context),
  d_decisionRequestsIndex(context, 0),
  d_preRegistrationVisitor(this, context),
  d_sharedTermsVisitor(d_sharedTerms)
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }
  Rewriter::init();
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    if(d_theoryTable[theoryId] != NULL) {
      delete d_theoryTable[theoryId];
      delete d_theoryOut[theoryId];
    }
  }
}

void TheoryEngine::preRegister(TNode preprocessed) {
  if(Dump.isOn("missed-t-propagations")) {
    d_possiblePropagations.push_back(preprocessed);
  }

  // Pre-register the terms in the atom
  bool multipleTheories = NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, preprocessed);
  if (multipleTheories) {
    // Collect the shared terms if there are multipe theories
    NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor, preprocessed);
    // Mark the multiple theories flag
    d_sharedTermsExist = true;
  }
}

/**
 * Check all (currently-active) theories for conflicts.
 * @param effort the effort level to use
 */
void TheoryEngine::check(Theory::Effort effort) {

  d_propEngine->checkTime();

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasCheck && isActive(THEORY)) { \
       reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->check(effort); \
       if (d_inConflict) { \
         break; \
       } \
    }

  // Do the checking
  try {

    // Clear any leftover propagated equalities
    d_propagatedEqualities.clear();

    // Mark the lemmas flag (no lemmas added)
    d_lemmasAdded = false;

    // Mark the output channel unused (if this is FULL_EFFORT, and nothing
    // is done by the theories, no additional check will be needed)
    d_outputChannelUsed = false;

    while (true) {

      Debug("theory") << "TheoryEngine::check(" << effort << "): running check" << std::endl;

      if (Debug.isOn("theory::assertions")) {
        for (unsigned theoryId = 0; theoryId < THEORY_LAST; ++ theoryId) {
          Theory* theory = d_theoryTable[theoryId];
          if (theory && Theory::setContains((TheoryId)theoryId, d_activeTheories)) {
            Debug("theory::assertions") << "--------------------------------------------" << std::endl;
            Debug("theory::assertions") << "Assertions of " << theory->getId() << ": " << std::endl;
            context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
            for (unsigned i = 0; it != it_end; ++ it, ++i) {
                if ((*it).isPreregistered) {
                  Debug("theory::assertions") << "[" << i << "]: ";
                } else {
                  Debug("theory::assertions") << "(" << i << "): ";
                }
                Debug("theory::assertions") << (*it).assertion << endl;
            }

            if (d_sharedTermsExist) {
              Debug("theory::assertions") << "Shared terms of " << theory->getId() << ": " << std::endl;
              context::CDList<TNode>::const_iterator it = theory->shared_terms_begin(), it_end = theory->shared_terms_end();
              for (unsigned i = 0; it != it_end; ++ it, ++i) {
                  Debug("theory::assertions") << "[" << i << "]: " << (*it) << endl;
              }
            }
          }
        }
      }

      // Do the checking
      CVC4_FOR_EACH_THEORY;

      if(Dump.isOn("missed-t-conflicts")) {
        Dump("missed-t-conflicts")
            << CommentCommand("Completeness check for T-conflicts; expect sat") << endl
            << CheckSatCommand() << endl;
      }

      Debug("theory") << "TheoryEngine::check(" << effort << "): running propagation after the initial check" << std::endl;

      // We are still satisfiable, propagate as much as possible
      propagate(effort);

      // If we have any propagated equalities, we enqueue them to the theories and re-check
      if (d_propagatedEqualities.size() > 0) {
        Debug("theory") << "TheoryEngine::check(" << effort << "): distributing shared equalities" << std::endl;
        assertSharedEqualities();
        continue;
      }

      // If we added any lemmas, we're done
      if (d_lemmasAdded) {
        Debug("theory") << "TheoryEngine::check(" << effort << "): lemmas added, done" << std::endl;
        break;
      }

      // If in full check and no lemmas added, run the combination
      if (Theory::fullEffort(effort) && d_sharedTermsExist) {
        // Do the combination
        Debug("theory") << "TheoryEngine::check(" << effort << "): running combination" << std::endl;
        combineTheories();
        // If we have any propagated equalities, we enqueue them to the theories and re-check
        if (d_propagatedEqualities.size() > 0) {
          Debug("theory") << "TheoryEngine::check(" << effort << "): distributing shared equalities" << std::endl;
          assertSharedEqualities();
        } else {
          // No propagated equalities, we're either sat, or there are lemmas added
          break;
        }
      } else {
        break;
      }
    }

    // Clear any leftover propagated equalities
    d_propagatedEqualities.clear();

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas") << std::endl;

  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::check() => conflict" << endl;
  }
}

void TheoryEngine::assertSharedEqualities() {
  // Assert all the shared equalities
  for (unsigned i = 0; i < d_propagatedEqualities.size(); ++ i) {
    const SharedEquality& eq = d_propagatedEqualities[i];
    // Check if the theory already got this one
    if (d_sharedAssertions.find(eq.toAssert) == d_sharedAssertions.end()) {
      Debug("sharing") << "TheoryEngine::assertSharedEqualities(): asserting " << eq.toAssert.node << " to " << eq.toAssert.theory << std::endl;
      Debug("sharing") << "TheoryEngine::assertSharedEqualities(): orignal " << eq.toExplain.node << " from " << eq.toExplain.theory << std::endl;
      d_sharedAssertions[eq.toAssert] = eq.toExplain;
      if (eq.toAssert.theory == theory::THEORY_LAST) {
        d_propagatedLiterals.push_back(eq.toAssert.node);
      } else {
        theoryOf(eq.toAssert.theory)->assertFact(eq.toAssert.node, false);
      }
    }
  }
  // Clear the equalities
  d_propagatedEqualities.clear();
}


void TheoryEngine::combineTheories() {

  Debug("sharing") << "TheoryEngine::combineTheories()" << std::endl;

  CareGraph careGraph;
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::isParametric && isActive(THEORY)) { \
     CareGraph theoryGraph; \
     reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->computeCareGraph(theoryGraph); \
     careGraph.insert(careGraph.end(), theoryGraph.begin(), theoryGraph.end()); \
  }

  CVC4_FOR_EACH_THEORY;

  // Now add splitters for the ones we are interested in
  for (unsigned i = 0; i < careGraph.size(); ++ i) {
    const CarePair& carePair = careGraph[i];

    Debug("sharing") << "TheoryEngine::combineTheories(): checking " << carePair.a << " = " << carePair.b << " from " << carePair.theory << std::endl;

    Node equality = carePair.a.eqNode(carePair.b);
    Node normalizedEquality = Rewriter::rewrite(equality);
	bool isTrivial = normalizedEquality.getKind() == kind::CONST_BOOLEAN;


    // If the node has a literal, it has been asserted so we should just check it
    bool value;
    if (isTrivial || (d_propEngine->isSatLiteral(normalizedEquality) && d_propEngine->hasValue(normalizedEquality, value))) {
      Debug("sharing") << "TheoryEngine::combineTheories(): has a literal or is trivial" << std::endl;

      if (isTrivial) {
	// if the equality is trivial, we assert it back to the theory saying the sat solver should explain
        value = normalizedEquality.getConst<bool>();
      }

      // Normalize the equality to the theory that requested it
      Node toAssert = Rewriter::rewriteEquality(carePair.theory, equality);

      if (value) {
        SharedEquality sharedEquality(toAssert, normalizedEquality, theory::THEORY_LAST, carePair.theory);
        Assert(d_sharedAssertions.find(sharedEquality.toAssert) == d_sharedAssertions.end());
        d_propagatedEqualities.push_back(sharedEquality);
      } else {
        SharedEquality sharedEquality(toAssert.notNode(), normalizedEquality.notNode(), theory::THEORY_LAST, carePair.theory);
        Assert(d_sharedAssertions.find(sharedEquality.toAssert) == d_sharedAssertions.end());
        d_propagatedEqualities.push_back(sharedEquality);
      }
    } else {
       Debug("sharing") << "TheoryEngine::combineTheories(): requesting a split " << std::endl;

       // There is no value, so we need to split on it
       lemma(equality.orNode(equality.notNode()), false, false);
    }
  }
}

void TheoryEngine::propagate(Theory::Effort effort) {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate && isActive(THEORY)) { \
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->propagate(effort); \
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

bool TheoryEngine::properConflict(TNode conflict) const {
  bool value;
  if (conflict.getKind() == kind::AND) {
    for (unsigned i = 0; i < conflict.getNumChildren(); ++ i) {
      if (! getPropEngine()->hasValue(conflict[i], value)) {
        Debug("properConflict") << "Bad conflict is due to unassigned atom: "
                                << conflict[i] << endl;
        return false;
      }
      if (! value) {
        Debug("properConflict") << "Bad conflict is due to false atom: "
                                << conflict[i] << endl;
        return false;
      }
    }
  } else {
    if (! getPropEngine()->hasValue(conflict, value)) {
      Debug("properConflict") << "Bad conflict is due to unassigned atom: "
                              << conflict << endl;
      return false;
    }
    if(! value) {
      Debug("properConflict") << "Bad conflict is due to false atom: "
                              << conflict << endl;
      return false;
    }
  }
  return true;
}

bool TheoryEngine::properPropagation(TNode lit) const {
  if(!getPropEngine()->isTranslatedSatLiteral(lit)) {
    return false;
  }
  bool b;
  return !getPropEngine()->hasValue(lit, b);
}

bool TheoryEngine::properExplanation(TNode node, TNode expl) const {
  Assert(!node.isNull() && !expl.isNull());
#warning implement TheoryEngine::properExplanation()
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

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPresolve) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->presolve(); \
      if(d_inConflict) { \
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
}/* TheoryEngine::presolve() */

void TheoryEngine::postsolve() {
  // NOTE that we don't look at d_theoryIsActive[] here (for symmetry
  // with presolve()).

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPostsolve) { \
      reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->postsolve(); \
      Assert(! d_inConflict, "conflict raised during postsolve()"); \
    }

    // Postsolve for each theory using the statement above
    CVC4_FOR_EACH_THEORY;
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::postsolve() => interrupted" << endl;
  }
}/* TheoryEngine::postsolve() */


void TheoryEngine::notifyRestart() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasNotifyRestart && isActive(THEORY)) { \
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->notifyRestart(); \
  }

  // notify each theory using the statement above
  CVC4_FOR_EACH_THEORY;
}

void TheoryEngine::ppStaticLearn(TNode in, NodeBuilder<>& learned) {
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
    reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->ppStaticLearn(in, learned); \
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
      theoryOf(static_cast<TheoryId>(theoryId))->shutdown();
    }
  }

  theory::Rewriter::shutdown();
}

theory::Theory::PPAssertStatus TheoryEngine::solve(TNode literal, SubstitutionMap& substitutionOut) {
  TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
  Trace("theory::solve") << "TheoryEngine::solve(" << literal << "): solving with " << theoryOf(atom)->getId() << endl;
  Theory::PPAssertStatus solveStatus = theoryOf(atom)->ppAssert(literal, substitutionOut);
  Trace("theory::solve") << "TheoryEngine::solve(" << literal << ") => " << solveStatus << endl;
  return solveStatus;
}

struct preprocess_stack_element {
  TNode node;
  bool children_added;
  preprocess_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct preprocess_stack_element */


Node TheoryEngine::preprocess(TNode assertion) {

  Trace("theory::preprocess") << "TheoryEngine::preprocess(" << assertion << ")" << endl;

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
      d_atomPreprocessingCache[current] = theoryOf(current)->ppRewrite(current);
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

void TheoryEngine::assertFact(TNode node)
{
  Trace("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;

  d_propEngine->checkTime();

  // Get the atom
  TNode atom = node.getKind() == kind::NOT ? node[0] : node;

  // Assert the fact to the apropriate theory
  theoryOf(atom)->assertFact(node, true);

  // If any shared terms, notify the theories
  if (d_sharedTerms.hasSharedTerms(atom)) {
    SharedTermsDatabase::shared_terms_iterator it = d_sharedTerms.begin(atom);
    SharedTermsDatabase::shared_terms_iterator it_end = d_sharedTerms.end(atom);
    for (; it != it_end; ++ it) {
      TNode term = *it;
      Theory::Set theories = d_sharedTerms.getTheoriesToNotify(atom, term);
      for (TheoryId theory = THEORY_FIRST; theory != THEORY_LAST; ++ theory) {
        if (Theory::setContains(theory, theories)) {
          theoryOf(theory)->addSharedTermInternal(term);
        }
      }
      d_sharedTerms.markNotified(term, theories);
      markActive(theories);
    }
  }
}

void TheoryEngine::propagate(TNode literal, theory::TheoryId theory) {

  Debug("theory") << "EngineOutputChannel::propagate(" << literal << ", " << theory << ")" << std::endl;

  d_propEngine->checkTime();

  if(Dump.isOn("t-propagations")) {
    Dump("t-propagations") << CommentCommand("negation of theory propagation: expect valid") << std::endl
                           << QueryCommand(literal.toExpr()) << std::endl;
  }
  if(Dump.isOn("missed-t-propagations")) {
    d_hasPropagated.insert(literal);
  }

  TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;

  if (!d_sharedTermsExist || atom.getKind() != kind::EQUAL) {
    // If not an equality it must be a SAT literal so we enlist it, and it can only
    // be propagated by the theory that owns it, as it is the only one that got
    // a preregister call with it.
    Assert(d_propEngine->isSatLiteral(literal));
    d_propagatedLiterals.push_back(literal);
  } else {
    // Otherwise it might be a shared-term (dis-)equality
    Node normalizedLiteral = Rewriter::rewrite(literal);
    if (d_propEngine->isSatLiteral(normalizedLiteral)) {
      // If there is a literal, just enqueue it, same as above
      bool value;
      if (d_propEngine->hasValue(normalizedLiteral, value)) {
        // if we are propagting something that already has a sat value we better be the same
        Debug("theory") << "literal " << literal << " (" << normalizedLiteral << ") propagated by " << theory << " but already has a sat value " << (value ? "true" : "false") << std::endl;
        Assert(value);
      } else {
        SharedEquality sharedEquality(normalizedLiteral, literal, theory, theory::THEORY_LAST);
        d_propagatedEqualities.push_back(sharedEquality);
      }
    }
    // Otherwise, we assert it to all interested theories
    Theory::Set lhsNotified = d_sharedTerms.getNotifiedTheories(atom[0]);
    Theory::Set rhsNotified = d_sharedTerms.getNotifiedTheories(atom[1]);
    // Now notify the theories
    if (Theory::setIntersection(lhsNotified, rhsNotified) != 0) {
      bool negated = literal.getKind() == kind::NOT;
      for (TheoryId currentTheory = theory::THEORY_FIRST; currentTheory != theory::THEORY_LAST; ++ currentTheory) {
        if (currentTheory == theory) {
          // Don't reassert to the same theory
          continue;
        }
        // Assert if theory is interested in both terms
        if (Theory::setContains(currentTheory, lhsNotified) && Theory::setContains(currentTheory, rhsNotified)) {
          // Normalize the equality
          Node equality = Rewriter::rewriteEquality(currentTheory, atom);
          if (equality.getKind() != kind::CONST_BOOLEAN) {
            // The assertion
            Node assertion = negated ? equality.notNode() : equality;
            // Remember it to assert later
            d_propagatedEqualities.push_back(SharedEquality(assertion, literal, theory, currentTheory));
          } else {
            Assert(negated || equality.getConst<bool>());
          }
        }
      }
    }
  }
}

void TheoryEngine::propagateAsDecision(TNode literal, theory::TheoryId theory) {
  Debug("theory") << "EngineOutputChannel::propagateAsDecision(" << literal << ", " << theory << ")" << std::endl;

  d_propEngine->checkTime();

  Assert(d_propEngine->isSatLiteral(literal.getKind() == kind::NOT ? literal[0] : literal), "OutputChannel::propagateAsDecision() requires a SAT literal (or negation of one)");

  d_decisionRequests.push_back(literal);
}

theory::EqualityStatus TheoryEngine::getEqualityStatus(TNode a, TNode b) {
  Assert(a.getType() == b.getType());
  return theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

Node TheoryEngine::getExplanation(TNode node) {
  Debug("theory") << "TheoryEngine::getExplanation(" << node << ")" << std::endl;

  TNode atom = node.getKind() == kind::NOT ? node[0] : node;

  Node explanation;

  // The theory that has explaining to do
  Theory* theory;

  //This is true if atom is a shared assertion
  bool sharedAssertion = false;

  SharedAssertionsMap::iterator find;
  // "find" will have a value when sharedAssertion is true
  if (d_sharedTermsExist && atom.getKind() == kind::EQUAL) {
    find = d_sharedAssertions.find(NodeTheoryPair(node, theory::THEORY_LAST));
    sharedAssertion = (find != d_sharedAssertions.end());
  }

  // Get the explanation
  if(sharedAssertion){
    theory = theoryOf((*find).second.theory);
    explanation = theory->explain((*find).second.node);
  } else {
    theory = theoryOf(atom);
    explanation = theory->explain(node);
  }

  // Explain any shared equalities that might be in the explanation
  if (d_sharedTermsExist) {
    NodeBuilder<> nb(kind::AND);
    explainEqualities(theory->getId(), explanation, nb);
    explanation = nb;
  }

  Assert(!explanation.isNull());
  if(Dump.isOn("t-explanations")) {
    Dump("t-explanations") << CommentCommand(std::string("theory explanation from ") + theoryOf(atom)->identify() + ": expect valid") << std::endl
      << QueryCommand(explanation.impNode(node).toExpr()) << std::endl;
  }
  Assert(properExplanation(node, explanation));

  return explanation;
}

void TheoryEngine::conflict(TNode conflict, TheoryId theoryId) {

  // Mark that we are in conflict
  d_inConflict = true;

  if(Dump.isOn("t-conflicts")) {
    Dump("t-conflicts") << CommentCommand("theory conflict: expect unsat") << std::endl
                        << CheckSatCommand(conflict.toExpr()) << std::endl;
  }

  if (d_sharedTermsExist) {
    // In the multiple-theories case, we need to reconstruct the conflict
    NodeBuilder<> nb(kind::AND);
    explainEqualities(theoryId, conflict, nb);
    Node fullConflict = nb;
    Assert(properConflict(fullConflict));
    Debug("theory") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << "): " << fullConflict << std::endl;
    lemma(fullConflict, true, false);
  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    lemma(conflict, true, false);
  }
}

void TheoryEngine::explainEqualities(TheoryId theoryId, TNode literals, NodeBuilder<>& builder) {
  Debug("theory") << "TheoryEngine::explainEqualities(" << theoryId << ", " << literals << ")" << std::endl;
  if (literals.getKind() == kind::AND) {
    for (unsigned i = 0, i_end = literals.getNumChildren(); i != i_end; ++ i) {
      TNode literal = literals[i];
      TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
      if (atom.getKind() == kind::EQUAL) {
        explainEquality(theoryId, literal, builder);
      } else if(literal.getKind() == kind::AND){
        explainEqualities(theoryId, literal, builder);
      } else {
        builder << literal;
      }
    }
  } else {
    TNode atom = literals.getKind() == kind::NOT ? literals[0] : literals;
    if (atom.getKind() == kind::EQUAL) {
      explainEquality(theoryId, literals, builder);
    } else {
      builder << literals;
    }
  }
}

void TheoryEngine::explainEquality(TheoryId theoryId, TNode eqLiteral, NodeBuilder<>& builder) {
  Assert(eqLiteral.getKind() == kind::EQUAL || (eqLiteral.getKind() == kind::NOT && eqLiteral[0].getKind() == kind::EQUAL));

  SharedAssertionsMap::iterator find = d_sharedAssertions.find(NodeTheoryPair(eqLiteral, theoryId));
  if (find == d_sharedAssertions.end()) {
    // Not a shared assertion, just add it since it must be SAT literal
    builder << Rewriter::rewrite(eqLiteral);
  } else {
    TheoryId explainingTheory = (*find).second.theory;
    if (explainingTheory == theory::THEORY_LAST) {
      // If the theory is from the SAT solver, just take the normalized one
      builder << (*find).second.node;
    } else {
      // Explain it using the theory that propagated it
      Node explanation = theoryOf(explainingTheory)->explain((*find).second.node);
      explainEqualities(explainingTheory, explanation, builder);
    }
  }
}
