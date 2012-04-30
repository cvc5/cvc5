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
                           context::UserContext* userContext,
                           const LogicInfo& logicInfo)
: d_propEngine(NULL),
  d_context(context),
  d_userContext(userContext),
  d_logicInfo(logicInfo),
  d_notify(*this),
  d_sharedTerms(d_notify, context),
  d_ppCache(),
  d_possiblePropagations(),
  d_hasPropagated(context),
  d_inConflict(context, false),
  d_sharedTermsExist(logicInfo.isSharingEnabled()),
  d_hasShutDown(false),
  d_incomplete(context, false),
  d_sharedLiteralsIn(context),
  d_assertedLiteralsOut(context),
  d_propagatedLiterals(context),
  d_propagatedLiteralsIndex(context, 0),
  d_decisionRequests(context),
  d_decisionRequestsIndex(context, 0),
  d_combineTheoriesTime("TheoryEngine::combineTheoriesTime"),
  d_preRegistrationVisitor(this, context),
  d_sharedTermsVisitor(d_sharedTerms)
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }
  Rewriter::init();
  StatisticsRegistry::registerStat(&d_combineTheoriesTime);
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    if(d_theoryTable[theoryId] != NULL) {
      delete d_theoryTable[theoryId];
      delete d_theoryOut[theoryId];
    }
  }

  StatisticsRegistry::unregisterStat(&d_combineTheoriesTime);
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
    if (theory::TheoryTraits<THEORY>::hasCheck && d_logicInfo.isTheoryEnabled(THEORY)) { \
       reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->check(effort); \
       if (d_inConflict) { \
         break; \
       } \
    }

  // Do the checking
  try {

    // Clear any leftover propagated shared literals
    d_propagatedSharedLiterals.clear();

    // Mark the output channel unused (if this is FULL_EFFORT, and nothing
    // is done by the theories, no additional check will be needed)
    d_outputChannelUsed = false;

    // Mark the lemmas flag (no lemmas added)
    d_lemmasAdded = false;

    while (true) {

      Debug("theory") << "TheoryEngine::check(" << effort << "): running check" << std::endl;

      if (Debug.isOn("theory::assertions")) {
        for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
          Theory* theory = d_theoryTable[theoryId];
          if (theory && d_logicInfo.isTheoryEnabled(theoryId)) {
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
            << CommentCommand("Completeness check for T-conflicts; expect sat")
            << CheckSatCommand();
      }

      Debug("theory") << "TheoryEngine::check(" << effort << "): running propagation after the initial check" << std::endl;

      // We are still satisfiable, propagate as much as possible
      propagate(effort);

      // If we have any propagated shared literals, we enqueue them to the theories and re-check
      if (d_propagatedSharedLiterals.size() > 0) {
        Debug("theory") << "TheoryEngine::check(" << effort << "): distributing shared literals" << std::endl;
        outputSharedLiterals();
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
        // If we have any propagated shared literals, we enqueue them to the theories and re-check
        if (d_propagatedSharedLiterals.size() > 0) {
          Debug("theory") << "TheoryEngine::check(" << effort << "): distributing shared literals" << std::endl;
          outputSharedLiterals();
        } else {
          // No propagated shared literals, we're either sat, or there are lemmas added
          break;
        }
      } else {
        break;
      }
    }

    // Clear any leftover propagated shared literals
    d_propagatedSharedLiterals.clear();

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas") << std::endl;

  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::check() => conflict" << endl;
  }
}

void TheoryEngine::outputSharedLiterals() {
  // Assert all the shared literals
  for (unsigned i = 0; i < d_propagatedSharedLiterals.size(); ++ i) {
    const SharedLiteral& eq = d_propagatedSharedLiterals[i];
    // Check if the theory already got this one
    if (d_assertedLiteralsOut.find(eq.toAssert) == d_assertedLiteralsOut.end()) {
      Debug("sharing") << "TheoryEngine::outputSharedLiterals(): asserting " << eq.toAssert.node << " to " << eq.toAssert.theory << std::endl;
      Debug("sharing") << "TheoryEngine::outputSharedLiterals(): orignal " << eq.toExplain << std::endl;
      d_assertedLiteralsOut[eq.toAssert] = eq.toExplain;
      if (eq.toAssert.theory == theory::THEORY_LAST) {
        d_propagatedLiterals.push_back(eq.toAssert.node);
      } else {
        theoryOf(eq.toAssert.theory)->assertFact(eq.toAssert.node, false);
      }
    }
  }
  // Clear the equalities
  d_propagatedSharedLiterals.clear();
}


void TheoryEngine::combineTheories() {

  Debug("sharing") << "TheoryEngine::combineTheories()" << std::endl;

  TimerStat::CodeTimer combineTheoriesTimer(d_combineTheoriesTime);

  CareGraph careGraph;
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::isParametric && d_logicInfo.isTheoryEnabled(THEORY)) { \
     reinterpret_cast<theory::TheoryTraits<THEORY>::theory_class*>(theoryOf(THEORY))->getCareGraph(careGraph); \
  }

  CVC4_FOR_EACH_THEORY;

  // Now add splitters for the ones we are interested in
  CareGraph::const_iterator care_it = careGraph.begin();
  CareGraph::const_iterator care_it_end = careGraph.end();
  for (; care_it != care_it_end; ++ care_it) {
    const CarePair& carePair = *care_it;

    Debug("sharing") << "TheoryEngine::combineTheories(): checking " << carePair.a << " = " << carePair.b << " from " << carePair.theory << std::endl;

    if (d_sharedTerms.areEqual(carePair.a, carePair.b) ||
        d_sharedTerms.areDisequal(carePair.a, carePair.b)) {
      continue;
    }

    if (carePair.a.isConst() && carePair.b.isConst()) {
      // TODO: equality engine should auto-detect these as disequal
      d_sharedTerms.processSharedLiteral(carePair.a.eqNode(carePair.b).notNode(), NodeManager::currentNM()->mkConst<bool>(true));
      continue;
    }

    Node equality = carePair.a.eqNode(carePair.b);
    Node normalizedEquality = Rewriter::rewrite(equality);
    bool isTrivial = normalizedEquality.getKind() == kind::CONST_BOOLEAN;
    bool value;
    if (isTrivial || (d_propEngine->isSatLiteral(normalizedEquality) && d_propEngine->hasValue(normalizedEquality, value))) {
      // Missed propagation!
      Debug("sharing") << "TheoryEngine::combineTheories(): has a literal or is trivial" << std::endl;
      
      if (isTrivial) {
        value = normalizedEquality.getConst<bool>();
        normalizedEquality = NodeManager::currentNM()->mkConst<bool>(true);
      }
      else {
        d_sharedLiteralsIn[normalizedEquality] = theory::THEORY_LAST;
        if (!value) normalizedEquality = normalizedEquality.notNode();
      }
      if (!value) {
        equality = equality.notNode();
      }
      d_sharedTerms.processSharedLiteral(equality, normalizedEquality);
      continue;
    }

    // There is no value, so we need to split on it
    Debug("sharing") << "TheoryEngine::combineTheories(): requesting a split " << std::endl;
    lemma(equality.orNode(equality.notNode()), false, false);

  }
}

void TheoryEngine::propagate(Theory::Effort effort) {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate && d_logicInfo.isTheoryEnabled(THEORY)) { \
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
          << CommentCommand("Completeness check for T-propagations; expect invalid")
          << QueryCommand((*i).toExpr());
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
  if (theory::TheoryTraits<THEORY>::hasNotifyRestart && d_logicInfo.isTheoryEnabled(THEORY)) { \
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
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId) {
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

// Recursively traverse a term and call the theory rewriter on its sub-terms
Node TheoryEngine::ppTheoryRewrite(TNode term)
{
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end()) {
    return (*find).second;
  }
  unsigned nc = term.getNumChildren();
  if (nc == 0) {
    return theoryOf(term)->ppRewrite(term);
  }
  Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;
  NodeBuilder<> newNode(term.getKind());
  if (term.getMetaKind() == kind::metakind::PARAMETERIZED) {
    newNode << term.getOperator();
  }
  unsigned i;
  for (i = 0; i < nc; ++i) {
    newNode << ppTheoryRewrite(term[i]);
  }
  Node newTerm = Rewriter::rewrite(newNode);
  Node newTerm2 = theoryOf(newTerm)->ppRewrite(newTerm);
  if (newTerm != newTerm2) {
    newTerm = ppTheoryRewrite(Rewriter::rewrite(newTerm2));
  }
  d_ppCache[term] = newTerm;
  Trace("theory-pp")<< "ppTheoryRewrite returning " << newTerm << "}" << endl;
  return newTerm;
}


void TheoryEngine::preprocessStart()
{
  d_ppCache.clear();
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
    NodeMap::iterator find = d_ppCache.find(current);
    if (find != d_ppCache.end()) {
      toVisit.pop_back();
      continue;
    }

    // If this is an atom, we preprocess its terms with the theory ppRewriter
    if (Theory::theoryOf(current) != THEORY_BOOL) {
      d_ppCache[current] = ppTheoryRewrite(current);
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
        Assert(d_ppCache.find(current[i]) != d_ppCache.end());
        builder << d_ppCache[current[i]];
      }
      // Mark the substitution and continue
      Node result = builder;
      Debug("theory::internal") << "TheoryEngine::preprocess(" << assertion << "): setting " << current << " -> " << result << endl;
      d_ppCache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_ppCache.find(childNode);
          if (childFind == d_ppCache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // No children, so we're done
        Debug("substitution::internal") << "SubstitutionMap::internalSubstitute(" << assertion << "): setting " << current << " -> " << current << endl;
        d_ppCache[current] = current;
        toVisit.pop_back();
      }
    }
  }

  // Return the substituted version
  return d_ppCache[assertion];
}

void TheoryEngine::assertFact(TNode node)
{
  Trace("theory") << "TheoryEngine::assertFact(" << node << ")" << std::endl;
  Trace("theory::assertFact") << "TheoryEngine::assertFact(" << node << ")" << std::endl;

  d_propEngine->checkTime();

  // Get the atom
  bool negated = node.getKind() == kind::NOT;
  TNode atom = negated ? node[0] : node;
  Theory* theory = theoryOf(atom);

  if (d_sharedTermsExist) {

    // If any shared terms, notify the theories
    if (d_sharedTerms.hasSharedTerms(atom)) {
      SharedTermsDatabase::shared_terms_iterator it = d_sharedTerms.begin(atom);
      SharedTermsDatabase::shared_terms_iterator it_end = d_sharedTerms.end(atom);
      for (; it != it_end; ++ it) {
        TNode term = *it;
        Theory::Set theories = d_sharedTerms.getTheoriesToNotify(atom, term);
        for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++ id) {
          if (Theory::setContains(id, theories)) {
            theoryOf(id)->addSharedTermInternal(term);
          }
        }
        d_sharedTerms.markNotified(term, theories);
      }
    }

    if (atom.getKind() == kind::EQUAL &&
        d_sharedTerms.isShared(atom[0]) &&
        d_sharedTerms.isShared(atom[1])) {
      Debug("sharing") << "TheoryEngine::assertFact: asserting shared node: " << node << std::endl;
      // Important: don't let facts through that are already known by the shared terms database or we can get into a loop in explain
      if ((negated && d_sharedTerms.areDisequal(atom[0], atom[1])) ||
          ((!negated) && d_sharedTerms.areEqual(atom[0], atom[1]))) {
        Debug("sharing") << "TheoryEngine::assertFact: sharedLiteral already known(" << node << ")" << std::endl;
        return;
      }
      d_sharedLiteralsIn[node] = THEORY_LAST;
      d_sharedTerms.processSharedLiteral(node, node);
      if (d_propagatedSharedLiterals.size() > 0) {
        Debug("theory") << "TheoryEngine::assertFact: distributing shared literals" << std::endl;
        outputSharedLiterals();
      }
      // TODO: have processSharedLiteral propagate disequalities?
      if (node.getKind() == kind::EQUAL) {
        // Don't have to assert it - this will be taken care of by processSharedLiteral
        Assert(d_logicInfo.isTheoryEnabled(theory->getId()));
        return;
      }
    }
    // If theory didn't already get this literal, add to the map
    NodeTheoryPair ntp(node, theory->getId());
    if (d_assertedLiteralsOut.find(ntp) == d_assertedLiteralsOut.end()) {
      d_assertedLiteralsOut[ntp] = Node();
    }
  }

  // Assert the fact to the appropriate theory and mark it active
  theory->assertFact(node, true);
  Assert(d_logicInfo.isTheoryEnabled(theory->getId()));
}

void TheoryEngine::propagate(TNode literal, theory::TheoryId theory) {

  Debug("theory") << "TheoryEngine::propagate(" << literal << ", " << theory << ")" << std::endl;

  d_propEngine->checkTime();

  if(Dump.isOn("t-propagations")) {
    Dump("t-propagations") << CommentCommand("negation of theory propagation: expect valid")
                           << QueryCommand(literal.toExpr());
  }
  if(Dump.isOn("missed-t-propagations")) {
    d_hasPropagated.insert(literal);
  }

  bool negated = (literal.getKind() == kind::NOT);
  TNode atom = negated ? literal[0] : literal;
  bool value;

  if (!d_sharedTermsExist || atom.getKind() != kind::EQUAL ||
      !d_sharedTerms.isShared(atom[0]) || !d_sharedTerms.isShared(atom[1])) {
    // If not an equality or if an equality between terms that are not both shared,
    // it must be a SAT literal so we enqueue it
    Assert(d_propEngine->isSatLiteral(literal));
    if (d_propEngine->hasValue(literal, value)) {
      // if we are propagting something that already has a sat value we better be the same
      Debug("theory") << "literal " << literal << ") propagated by " << theory << " but already has a sat value " << (value ? "true" : "false") << std::endl;
      Assert(value);
    } else {
      d_propagatedLiterals.push_back(literal);
    }
  } else {
    // Important: don't let facts through that are already known by the shared terms database or we can get into a loop in explain
    if ((negated && d_sharedTerms.areDisequal(atom[0], atom[1])) ||
        ((!negated) && d_sharedTerms.areEqual(atom[0], atom[1]))) {
      Debug("sharing") << "TheoryEngine::propagate: sharedLiteral already known(" << literal << ")" << std::endl;
      return;
    }

    // Otherwise it is a shared-term (dis-)equality
    Node normalizedLiteral = Rewriter::rewrite(literal);
    if (d_propEngine->isSatLiteral(normalizedLiteral)) {
      // If there is a literal, propagate it to SAT
      if (d_propEngine->hasValue(normalizedLiteral, value)) {
        // if we are propagting something that already has a sat value we better be the same
        Debug("theory") << "literal " << literal << ", normalized = " << normalizedLiteral << ", propagated by " << theory << " but already has a sat value " << (value ? "true" : "false") << std::endl;
        Assert(value);
      } else {
        SharedLiteral sharedLiteral(normalizedLiteral, literal, theory::THEORY_LAST);
        d_propagatedSharedLiterals.push_back(sharedLiteral);
      }
    }
    // Assert to interested theories
    Debug("shared-in") << "TheoryEngine::propagate: asserting shared node: " << literal << std::endl;
    d_sharedLiteralsIn[literal] = theory;
    d_sharedTerms.processSharedLiteral(literal, literal);
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
  if (d_sharedTerms.isShared(a) && d_sharedTerms.isShared(b)) {
    if (d_sharedTerms.areEqual(a,b)) {
      return EQUALITY_TRUE_AND_PROPAGATED;
    }
    else if (d_sharedTerms.areDisequal(a,b)) {
      return EQUALITY_FALSE_AND_PROPAGATED;
    }
  }
  return theoryOf(Theory::theoryOf(a.getType()))->getEqualityStatus(a, b);
}

Node TheoryEngine::getExplanation(TNode node) {
  Debug("theory") << "TheoryEngine::getExplanation(" << node << ")" << std::endl;

  TNode atom = node.getKind() == kind::NOT ? node[0] : node;

  Node explanation;

  // The theory that has explaining to do
  Theory* theory;

  //This is true if atom is a shared assertion
  bool sharedLiteral = false;

  AssertedLiteralsOutMap::iterator find;
  // "find" will have a value when sharedAssertion is true
  if (d_sharedTermsExist && atom.getKind() == kind::EQUAL) {
    find = d_assertedLiteralsOut.find(NodeTheoryPair(node, theory::THEORY_LAST));
    sharedLiteral = (find != d_assertedLiteralsOut.end());
  }

  // Get the explanation
  if(sharedLiteral) {
    explanation = explain(ExplainTask((*find).second, SHARED_LITERAL_OUT));
  } else {
    theory = theoryOf(atom);
    explanation = theory->explain(node);

    // Explain any shared equalities that might be in the explanation
    if (d_sharedTermsExist) {
      explanation = explain(ExplainTask(explanation, THEORY_EXPLANATION, theory->getId()));
    }
  }

  Assert(!explanation.isNull());
  if(Dump.isOn("t-explanations")) {
    Dump("t-explanations") << CommentCommand(std::string("theory explanation from ") + theoryOf(atom)->identify() + ": expect valid")
      << QueryCommand(explanation.impNode(node).toExpr());
  }
  Assert(properExplanation(node, explanation));

  return explanation;
}

Node TheoryEngine::explain(ExplainTask toExplain)
{
  Debug("theory") << "TheoryEngine::explain(" << toExplain.node << ", " << toExplain.kind << ", " << toExplain.theory << ")" << std::endl;

  std::set<TNode> satAssertions;
  std::deque<ExplainTask> explainQueue;
  // TODO: benchmark whether this helps
  std::hash_set<ExplainTask, ExplainTaskHashFunction> explained;
  bool value;

  // No need to explain "true"
  explained.insert(ExplainTask(NodeManager::currentNM()->mkConst<bool>(true), SHARED_DATABASE_EXPLANATION));

  while (true) {

    Debug("theory-explain") << "TheoryEngine::explain(" << toExplain.node << ", " << toExplain.kind << ", " << toExplain.theory << ")" << std::endl;

    if (explained.find(toExplain) == explained.end()) {

      explained.insert(toExplain);

      if (toExplain.node.getKind() == kind::AND) {
        for (unsigned i = 0, i_end = toExplain.node.getNumChildren(); i != i_end; ++ i) {
          explainQueue.push_back(ExplainTask(toExplain.node[i], toExplain.kind, toExplain.theory));
        }
      }
      else {

        switch (toExplain.kind) {

          // toExplain.node contains a shared literal sent out from theory engine (before being rewritten)
          case SHARED_LITERAL_OUT: {
            // Shortcut - see if this came directly from a theory
            SharedLiteralsInMap::iterator it = d_sharedLiteralsIn.find(toExplain.node);
            if (it != d_sharedLiteralsIn.end()) {
              TheoryId id = (*it).second;
              if (id == theory::THEORY_LAST) {
                Assert(d_propEngine->isSatLiteral(toExplain.node));
                Assert(d_propEngine->hasValue(toExplain.node, value) && value);
                satAssertions.insert(toExplain.node);
                break;
              }
              explainQueue.push_back(ExplainTask(theoryOf((*it).second)->explain(toExplain.node), THEORY_EXPLANATION, (*it).second));
            }
            // Otherwise, get explanation from shared terms database
            else {
              explainQueue.push_back(ExplainTask(d_sharedTerms.explain(toExplain.node), SHARED_DATABASE_EXPLANATION));
            }
            break;
          }

            // toExplain.node contains explanation from theory, toExplain.theory contains theory that produced explanation
          case THEORY_EXPLANATION: {
            AssertedLiteralsOutMap::iterator find = d_assertedLiteralsOut.find(NodeTheoryPair(toExplain.node, toExplain.theory));
            if (find == d_assertedLiteralsOut.end() || (*find).second.isNull()) {
              Assert(d_propEngine->isSatLiteral(toExplain.node));
              Assert(d_propEngine->hasValue(toExplain.node, value) && value);
              satAssertions.insert(toExplain.node);
            }
            else {
              explainQueue.push_back(ExplainTask((*find).second, SHARED_LITERAL_OUT));
            }
            break;
          }

            // toExplain.node contains an explanation from the shared terms database
            // Each literal in the explanation should be in the d_sharedLiteralsIn map
          case SHARED_DATABASE_EXPLANATION: {
            Assert(d_sharedLiteralsIn.find(toExplain.node) != d_sharedLiteralsIn.end());
            TheoryId id = d_sharedLiteralsIn[toExplain.node];
            if (id == theory::THEORY_LAST) {
              Assert(d_propEngine->isSatLiteral(toExplain.node));
              Assert(d_propEngine->hasValue(toExplain.node, value) && value);
              satAssertions.insert(toExplain.node);
            }
            else {
              explainQueue.push_back(ExplainTask(theoryOf(id)->explain(toExplain.node), THEORY_EXPLANATION, id));
            }
            break;
          }        
          default:
            Unreachable();
        }
      }
    }

    if (explainQueue.empty()) break;

    toExplain = explainQueue.front();
    explainQueue.pop_front();
  }

  Assert(satAssertions.size() > 0);
  if (satAssertions.size() == 1) {
    return *(satAssertions.begin());
  }

  // Now build the explanation
  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = satAssertions.begin();
  std::set<TNode>::const_iterator it_end = satAssertions.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }
  return conjunction;
}

void TheoryEngine::conflict(TNode conflict, TheoryId theoryId) {

  // Mark that we are in conflict
  d_inConflict = true;

  if(Dump.isOn("t-conflicts")) {
    Dump("t-conflicts") << CommentCommand("theory conflict: expect unsat")
                        << CheckSatCommand(conflict.toExpr());
  }

  if (d_sharedTermsExist) {
    // In the multiple-theories case, we need to reconstruct the conflict
    Node fullConflict = explain(ExplainTask(conflict, THEORY_EXPLANATION, theoryId));
    Assert(properConflict(fullConflict));
    Debug("theory") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << "): " << fullConflict << std::endl;
    lemma(fullConflict, true, false);
  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    lemma(conflict, true, false);
  }
}


//Conflict from shared terms database
void TheoryEngine::sharedConflict(TNode conflict) {
  // Mark that we are in conflict
  d_inConflict = true;

  if(Dump.isOn("t-conflicts")) {
    Dump("t-conflicts") << CommentCommand("theory conflict: expect unsat")
                        << CheckSatCommand(conflict.toExpr());
  }

  Node fullConflict = explain(ExplainTask(d_sharedTerms.explain(conflict), SHARED_DATABASE_EXPLANATION));
  Assert(properConflict(fullConflict));
  Debug("theory") << "TheoryEngine::sharedConflict(" << conflict << "): " << fullConflict << std::endl;
  lemma(fullConflict, true, false);
}
