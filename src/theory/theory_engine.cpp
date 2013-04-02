/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Christopher L. Conway, Kshitij Bansal, Tim King, Liana Hadarean, Clark Barrett, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include <vector>
#include <list>

#include "decision/decision_engine.h"

#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "options/options.h"
#include "util/lemma_output_channel.h"

#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_traits.h"

#include "smt/logic_exception.h"

#include "util/node_visitor.h"
#include "util/ite_removal.h"

#include "theory/model.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/first_order_model.h"

#include "theory/uf/equality_engine.h"

#include "theory/rewriterules/efficient_e_matching.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

void TheoryEngine::finishInit() {
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->finishInit();
    Assert(d_masterEqualityEngine == 0);
    d_masterEqualityEngine = new eq::EqualityEngine(d_masterEENotify,getSatContext(), "theory::master");

    for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
      if (d_theoryTable[theoryId]) {
        d_theoryTable[theoryId]->setMasterEqualityEngine(d_masterEqualityEngine);
      }
    }
  }
}

void TheoryEngine::eqNotifyNewClass(TNode t){
  d_quantEngine->addTermToDatabase( t );
}

void TheoryEngine::eqNotifyPreMerge(TNode t1, TNode t2){
  //TODO: add notification to efficient E-matching
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->getEfficientEMatcher()->merge( t1, t2 );
  }
}

void TheoryEngine::eqNotifyPostMerge(TNode t1, TNode t2){

}

void TheoryEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){

}


TheoryEngine::TheoryEngine(context::Context* context,
                           context::UserContext* userContext,
                           RemoveITE& iteRemover,
                           const LogicInfo& logicInfo)
: d_propEngine(NULL),
  d_decisionEngine(NULL),
  d_context(context),
  d_userContext(userContext),
  d_logicInfo(logicInfo),
  d_sharedTerms(this, context),
  d_masterEqualityEngine(NULL),
  d_masterEENotify(*this),
  d_quantEngine(NULL),
  d_curr_model(NULL),
  d_curr_model_builder(NULL),
  d_ppCache(),
  d_possiblePropagations(context),
  d_hasPropagated(context),
  d_inConflict(context, false),
  d_hasShutDown(false),
  d_incomplete(context, false),
  d_propagationMap(context),
  d_propagationMapTimestamp(context, 0),
  d_propagatedLiterals(context),
  d_propagatedLiteralsIndex(context, 0),
  d_iteRemover(iteRemover),
  d_combineTheoriesTime("TheoryEngine::combineTheoriesTime"),
  d_true(),
  d_false(),
  d_interrupted(false),
  d_inPreregister(false),
  d_factsAsserted(context, false),
  d_preRegistrationVisitor(this, context),
  d_sharedTermsVisitor(d_sharedTerms),
  d_unconstrainedSimp(context, logicInfo)
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }

  // initialize the quantifiers engine
  d_quantEngine = new QuantifiersEngine(context, userContext, this);

  // build model information if applicable
  d_curr_model = new theory::TheoryModel(userContext, "DefaultModel", true);
  d_curr_model_builder = new theory::TheoryEngineModelBuilder(this);

  StatisticsRegistry::registerStat(&d_combineTheoriesTime);
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

TheoryEngine::~TheoryEngine() {
  Assert(d_hasShutDown);

  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    if(d_theoryTable[theoryId] != NULL) {
      delete d_theoryTable[theoryId];
      delete d_theoryOut[theoryId];
    }
  }

  delete d_curr_model_builder;
  delete d_curr_model;

  delete d_quantEngine;

  delete d_masterEqualityEngine;

  StatisticsRegistry::unregisterStat(&d_combineTheoriesTime);
}

void TheoryEngine::interrupt() throw(ModalException) {
  d_interrupted = true;
}

void TheoryEngine::preRegister(TNode preprocessed) {

  if(Dump.isOn("missed-t-propagations")) {
    d_possiblePropagations.push_back(preprocessed);
  }
  d_preregisterQueue.push(preprocessed);

  if (!d_inPreregister) {
    // We're in pre-register
    d_inPreregister = true;

    // Process the pre-registration queue
    while (!d_preregisterQueue.empty()) {
      // Get the next atom to pre-register
      preprocessed = d_preregisterQueue.front();
      d_preregisterQueue.pop();

      if (d_logicInfo.isSharingEnabled() && preprocessed.getKind() == kind::EQUAL) {
        // When sharing is enabled, we propagate from the shared terms manager also
        d_sharedTerms.addEqualityToPropagate(preprocessed);
      }

      // Pre-register the terms in the atom
      bool multipleTheories = NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, preprocessed);
      if (multipleTheories) {
        // Collect the shared terms if there are multipe theories
        NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor, preprocessed);
      }
    }

    // Leaving pre-register
    d_inPreregister = false;
  }
}

void TheoryEngine::printAssertions(const char* tag) {
  if (Trace.isOn(tag)) {

    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
      Theory* theory = d_theoryTable[theoryId];
      if (theory && d_logicInfo.isTheoryEnabled(theoryId)) {
        Trace(tag) << "--------------------------------------------" << std::endl;
        Trace(tag) << "Assertions of " << theory->getId() << ": " << std::endl;
        context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
        for (unsigned i = 0; it != it_end; ++ it, ++i) {
            if ((*it).isPreregistered) {
              Trace(tag) << "[" << i << "]: ";
            } else {
              Trace(tag) << "(" << i << "): ";
            }
            Trace(tag) << (*it).assertion << endl;
        }

        if (d_logicInfo.isSharingEnabled()) {
          Trace(tag) << "Shared terms of " << theory->getId() << ": " << std::endl;
          context::CDList<TNode>::const_iterator it = theory->shared_terms_begin(), it_end = theory->shared_terms_end();
          for (unsigned i = 0; it != it_end; ++ it, ++i) {
              Trace(tag) << "[" << i << "]: " << (*it) << endl;
          }
        }
      }
    }
  }
}

void TheoryEngine::dumpAssertions(const char* tag) {
  if (Dump.isOn(tag)) {
    Dump(tag) << CommentCommand("Starting completeness check");
    for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
      Theory* theory = d_theoryTable[theoryId];
      if (theory && d_logicInfo.isTheoryEnabled(theoryId)) {
        Dump(tag) << CommentCommand("Completeness check");
        Dump(tag) << PushCommand();

        // Dump the shared terms
        if (d_logicInfo.isSharingEnabled()) {
          Dump(tag) << CommentCommand("Shared terms");
          context::CDList<TNode>::const_iterator it = theory->shared_terms_begin(), it_end = theory->shared_terms_end();
          for (unsigned i = 0; it != it_end; ++ it, ++i) {
              stringstream ss;
              ss << (*it);
              Dump(tag) << CommentCommand(ss.str());
          }
        }

        // Dump the assertions
        Dump(tag) << CommentCommand("Assertions");
        context::CDList<Assertion>::const_iterator it = theory->facts_begin(), it_end = theory->facts_end();
        for (; it != it_end; ++ it) {
          // Get the assertion
          Node assertionNode = (*it).assertion;
          // Purify all the terms

          if ((*it).isPreregistered) {
            Dump(tag) << CommentCommand("Preregistered");
          } else {
            Dump(tag) << CommentCommand("Shared assertion");
          }
          Dump(tag) << AssertCommand(assertionNode.toExpr());
        }
        Dump(tag) << CheckSatCommand();

        Dump(tag) << PopCommand();
      }
    }
  }
}

/**
 * Check all (currently-active) theories for conflicts.
 * @param effort the effort level to use
 */
void TheoryEngine::check(Theory::Effort effort) {

  d_propEngine->checkTime();

  // Reset the interrupt flag
  d_interrupted = false;

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasCheck && d_logicInfo.isTheoryEnabled(THEORY)) { \
Debug("theory") << "check<" << THEORY << ">" << std::endl; \
       theoryOf(THEORY)->check(effort); \
Debug("theory") << "done<" << THEORY << ">" << std::endl; \
       if (d_inConflict) { \
         break; \
       } \
    }

  // Do the checking
  try {

    // Mark the output channel unused (if this is FULL_EFFORT, and nothing
    // is done by the theories, no additional check will be needed)
    d_outputChannelUsed = false;

    // Mark the lemmas flag (no lemmas added)
    d_lemmasAdded = false;

    Debug("theory") << "TheoryEngine::check(" << effort << "): d_factsAsserted = " << (d_factsAsserted ? "true" : "false") << std::endl;

    // If in full effort, we have a fake new assertion just to jumpstart the checking
    if (Theory::fullEffort(effort)) {
      d_factsAsserted = true;
    }

    // Check until done
    while (d_factsAsserted && !d_inConflict && !d_lemmasAdded) {

      Debug("theory") << "TheoryEngine::check(" << effort << "): running check" << std::endl;

      Trace("theory::assertions") << std::endl;
      if (Trace.isOn("theory::assertions")) {
        printAssertions("theory::assertions");
      }

      // Note that we've discharged all the facts
      d_factsAsserted = false;

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

      // We do combination if all has been processed and we are in fullcheck
      if (Theory::fullEffort(effort) && d_logicInfo.isSharingEnabled() && !d_factsAsserted && !d_lemmasAdded) {
        // Do the combination
        Debug("theory") << "TheoryEngine::check(" << effort << "): running combination" << std::endl;
        combineTheories();
      }
    }

    // Must consult quantifiers theory for last call to ensure sat, or otherwise add a lemma
    if( effort == Theory::EFFORT_FULL && ! d_inConflict && ! needCheck() ) {
      if(d_logicInfo.isQuantified()) {
        // quantifiers engine must pass effort last call check
        d_quantEngine->check(Theory::EFFORT_LAST_CALL);
        // if we have given up, then possibly flip decision
        if(options::flipDecision()) {
          if(d_incomplete && !d_inConflict && !needCheck()) {
            ((theory::quantifiers::TheoryQuantifiers*) d_theoryTable[THEORY_QUANTIFIERS])->flipDecision();
          }
        }
        // if returning incomplete or SAT, we have ensured that the model in the quantifiers engine has been built
      } else if(options::produceModels()) {
        // must build model at this point
        d_curr_model_builder->buildModel(d_curr_model, true);
      }
    }

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas") << std::endl;

  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::check() => interrupted" << endl;
  }

  // If fulleffort, check all theories
  if(Dump.isOn("theory::fullcheck") && Theory::fullEffort(effort)) {
    if (!d_inConflict && !needCheck()) {
      dumpAssertions("theory::fullcheck");
    }
  }
}

void TheoryEngine::combineTheories() {

  Debug("sharing") << "TheoryEngine::combineTheories()" << std::endl;

  TimerStat::CodeTimer combineTheoriesTimer(d_combineTheoriesTime);

  // Care graph we'll be building
  CareGraph careGraph;

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::isParametric && d_logicInfo.isTheoryEnabled(THEORY)) { \
    theoryOf(THEORY)->getCareGraph(careGraph); \
  }

  // Call on each parametric theory to give us its care graph
  CVC4_FOR_EACH_THEORY;

  Debug("sharing") << "TheoryEngine::combineTheories(): care graph size = " << careGraph.size() << std::endl;

  // Now add splitters for the ones we are interested in
  CareGraph::const_iterator care_it = careGraph.begin();
  CareGraph::const_iterator care_it_end = careGraph.end();
  for (; care_it != care_it_end; ++ care_it) {
    const CarePair& carePair = *care_it;

    Debug("sharing") << "TheoryEngine::combineTheories(): checking " << carePair.a << " = " << carePair.b << " from " << carePair.theory << std::endl;

    Assert(d_sharedTerms.isShared(carePair.a) || carePair.a.isConst());
    Assert(d_sharedTerms.isShared(carePair.b) || carePair.b.isConst());
    //AJR-temp Assert(!d_sharedTerms.areEqual(carePair.a, carePair.b), "Please don't care about stuff you were notified about");
    //AJR-temp Assert(!d_sharedTerms.areDisequal(carePair.a, carePair.b), "Please don't care about stuff you were notified about");

    // The equality in question
    Node equality = carePair.a < carePair.b ?
        carePair.a.eqNode(carePair.b) :
        carePair.b.eqNode(carePair.a);

    // Normalize the equality
    Node normalizedEquality = Rewriter::rewrite(equality);

    // Check if the normalized equality already has a value (this also
    // covers constants, since they always have values
    if (d_propEngine->isSatLiteral(normalizedEquality)) {
      bool value;
      if (d_propEngine->hasValue(normalizedEquality, value)) {
        Assert(equality != normalizedEquality);
        Node literal = value ? equality : equality.notNode();
        Node normalizedLiteral = value ? normalizedEquality : normalizedEquality.notNode();
        // We're sending the original literal back, backed by the normalized one
        if (markPropagation(literal, normalizedLiteral, /* to */ carePair.theory, /* from */ THEORY_SAT_SOLVER)) {
          // We assert it, and we know it's preregistereed if it's the same theory
          bool preregistered = Theory::theoryOf(literal) == carePair.theory;
          theoryOf(carePair.theory)->assertFact(literal, preregistered);
          // Mark that we have more information
          d_factsAsserted = true;
          continue;
        } else {
          Message() << "mark propagation fail: " << literal << " " << normalizedLiteral << " " << carePair.theory << std::endl;
          Unreachable();
        }
      }
    }

    // We need to split on it
    Debug("sharing") << "TheoryEngine::combineTheories(): requesting a split " << std::endl;
    lemma(equality.orNode(equality.notNode()), false, false);
  }
}

void TheoryEngine::propagate(Theory::Effort effort) {
  // Reset the interrupt flag
  d_interrupted = false;

  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPropagate && d_logicInfo.isTheoryEnabled(THEORY)) { \
    theoryOf(THEORY)->propagate(effort); \
  }

  // Reset the interrupt flag
  d_interrupted = false;

  // Propagate for each theory using the statement above
  CVC4_FOR_EACH_THEORY;

  if(Dump.isOn("missed-t-propagations")) {
    for(unsigned i = 0; i < d_possiblePropagations.size(); ++ i) {
      Node atom = d_possiblePropagations[i];
      bool value;
      if (!d_propEngine->hasValue(atom, value)) continue;
      // Doesn't have a value, check it (and the negation)
      if(d_hasPropagated.find(atom) == d_hasPropagated.end()) {
        Dump("missed-t-propagations")
          << CommentCommand("Completeness check for T-propagations; expect invalid")
          << QueryCommand(atom.toExpr())
          << QueryCommand(atom.notNode().toExpr());
      }
    }
  }
}

Node TheoryEngine::getNextDecisionRequest() {
  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasGetNextDecisionRequest && d_logicInfo.isTheoryEnabled(THEORY)) { \
    Node n = theoryOf(THEORY)->getNextDecisionRequest(); \
    if(! n.isNull()) { \
      return n; \
    } \
  }

  // Request decision from each theory using the statement above
  CVC4_FOR_EACH_THEORY;

  return TNode();
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
      if (conflict[i] != Rewriter::rewrite(conflict[i])) {
        Debug("properConflict") << "Bad conflict is due to atom not in normal form: "
                                << conflict[i] << " vs " << Rewriter::rewrite(conflict[i]) << endl;
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
    if (conflict != Rewriter::rewrite(conflict)) {
      Debug("properConflict") << "Bad conflict is due to atom not in normal form: "
                              << conflict << " vs " << Rewriter::rewrite(conflict) << endl;
      return false;
    }
  }
  return true;
}

bool TheoryEngine::properPropagation(TNode lit) const {
  if(!getPropEngine()->isSatLiteral(lit)) {
    return false;
  }
  bool b;
  return !getPropEngine()->hasValue(lit, b);
}

bool TheoryEngine::properExplanation(TNode node, TNode expl) const {
  // Explanation must be either a conjunction of true literals that have true SAT values already
  // or a singled literal that has a true SAT value already.
  if (expl.getKind() == kind::AND) {
    for (unsigned i = 0; i < expl.getNumChildren(); ++ i) {
      bool value;
      if (!d_propEngine->hasValue(expl[i], value) || !value) {
        return false;
      }
    }
  } else {
    bool value;
    return d_propEngine->hasValue(expl, value) && value;
  }
  return true;
}

void TheoryEngine::collectModelInfo( theory::TheoryModel* m, bool fullModel ){
  //have shared term engine collectModelInfo
  //  d_sharedTerms.collectModelInfo( m, fullModel );
  // Consult each active theory to get all relevant information
  // concerning the model.
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_logicInfo.isTheoryEnabled(theoryId)) {
      Trace("model-builder") << "  CollectModelInfo on theory: " << theoryId << endl;
      d_theoryTable[theoryId]->collectModelInfo( m, fullModel );
    }
  }
  // Get the Boolean variables
  vector<TNode> boolVars;
  d_propEngine->getBooleanVariables(boolVars);
  vector<TNode>::iterator it, iend = boolVars.end();
  bool hasValue, value;
  for (it = boolVars.begin(); it != iend; ++it) {
    TNode var = *it;
    hasValue = d_propEngine->hasValue(var, value);
    // TODO: Assert that hasValue is true?
    if (!hasValue) {
      value = false;
    }
    Trace("model-builder-assertions") << "(assert" << (value ? " " : " (not ") << var << (value ? ");" : "));") << endl;
    m->assertPredicate(var, value);
  }
}

/* get model */
TheoryModel* TheoryEngine::getModel() {
  Debug("model") << "TheoryEngine::getModel()" << std::endl;
  if( d_logicInfo.isQuantified() ) {
    Debug("model") << "Get model from quantifiers engine." << std::endl;
    return d_quantEngine->getModel();
  } else {
    Debug("model") << "Get default model." << std::endl;
    return d_curr_model;
  }
}

bool TheoryEngine::presolve() {
  // Reset the interrupt flag
  d_interrupted = false;

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPresolve) {    \
      theoryOf(THEORY)->presolve(); \
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
  // Reset the interrupt flag
  d_interrupted = false;

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPostsolve) { \
      theoryOf(THEORY)->postsolve(); \
      Assert(! d_inConflict, "conflict raised during postsolve()"); \
    }

    // Postsolve for each theory using the statement above
    CVC4_FOR_EACH_THEORY;
  } catch(const theory::Interrupted&) {
    Trace("theory") << "TheoryEngine::postsolve() => interrupted" << endl;
  }
}/* TheoryEngine::postsolve() */


void TheoryEngine::notifyRestart() {
  // Reset the interrupt flag
  d_interrupted = false;

  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasNotifyRestart && d_logicInfo.isTheoryEnabled(THEORY)) { \
    theoryOf(THEORY)->notifyRestart(); \
  }

  // notify each theory using the statement above
  CVC4_FOR_EACH_THEORY;
}

void TheoryEngine::ppStaticLearn(TNode in, NodeBuilder<>& learned) {
  // Reset the interrupt flag
  d_interrupted = false;

  // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasPpStaticLearn) { \
    theoryOf(THEORY)->ppStaticLearn(in, learned); \
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
      theoryOf(theoryId)->shutdown();
    }
  }

  d_ppCache.clear();
}

theory::Theory::PPAssertStatus TheoryEngine::solve(TNode literal, SubstitutionMap& substitutionOut) {
  // Reset the interrupt flag
  d_interrupted = false;

  TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;
  Trace("theory::solve") << "TheoryEngine::solve(" << literal << "): solving with " << theoryOf(atom)->getId() << endl;

  if(! d_logicInfo.isTheoryEnabled(Theory::theoryOf(atom)) &&
     Theory::theoryOf(atom) != THEORY_SAT_SOLVER) {
    stringstream ss;
    ss << "The logic was specified as " << d_logicInfo.getLogicString()
       << ", which doesn't include " << Theory::theoryOf(atom)
       << ", but got a preprocessing-time fact for that theory." << endl
       << "The fact:" << endl
       << literal;
    throw LogicException(ss.str());
  }

  Theory::PPAssertStatus solveStatus = theoryOf(atom)->ppAssert(literal, substitutionOut);
  Trace("theory::solve") << "TheoryEngine::solve(" << literal << ") => " << solveStatus << endl;
  return solveStatus;
}

// Recursively traverse a term and call the theory rewriter on its sub-terms
Node TheoryEngine::ppTheoryRewrite(TNode term) {
  NodeMap::iterator find = d_ppCache.find(term);
  if (find != d_ppCache.end()) {
    return (*find).second;
  }
  unsigned nc = term.getNumChildren();
  if (nc == 0) {
    return theoryOf(term)->ppRewrite(term);
  }
  Trace("theory-pp") << "ppTheoryRewrite { " << term << endl;

  Node newTerm;
  if (theoryOf(term)->ppDontRewriteSubterm(term)) {
    newTerm = term;
  } else {
    NodeBuilder<> newNode(term.getKind());
    if (term.getMetaKind() == kind::metakind::PARAMETERIZED) {
      newNode << term.getOperator();
    }
    unsigned i;
    for (i = 0; i < nc; ++i) {
      newNode << ppTheoryRewrite(term[i]);
    }
    newTerm = Rewriter::rewrite(Node(newNode));
  }
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

    if(! d_logicInfo.isTheoryEnabled(Theory::theoryOf(current)) &&
       Theory::theoryOf(current) != THEORY_SAT_SOLVER) {
      stringstream ss;
      ss << "The logic was specified as " << d_logicInfo.getLogicString()
         << ", which doesn't include " << Theory::theoryOf(current)
         << ", but got a preprocessing-time fact for that theory." << endl
         << "The fact:" << endl
         << current;
      throw LogicException(ss.str());
    }

    // If this is an atom, we preprocess its terms with the theory ppRewriter
    if (Theory::theoryOf(current) != THEORY_BOOL) {
      Node ppRewritten = ppTheoryRewrite(current);
      d_ppCache[current] = ppRewritten;
      Assert(Rewriter::rewrite(d_ppCache[current]) == d_ppCache[current]);
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
      if (result != current) {
        result = Rewriter::rewrite(result);
      }
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

bool TheoryEngine::markPropagation(TNode assertion, TNode originalAssertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId) {

  // What and where we are asserting
  NodeTheoryPair toAssert(assertion, toTheoryId, d_propagationMapTimestamp);
  // What and where it came from
  NodeTheoryPair toExplain(originalAssertion, fromTheoryId, d_propagationMapTimestamp);

  // See if the theory already got this literal
  PropagationMap::const_iterator find = d_propagationMap.find(toAssert);
  if (find != d_propagationMap.end()) {
    // The theory already knows this
    Trace("theory::assertToTheory") << "TheoryEngine::markPropagation(): already there" << std::endl;
    return false;
  }

  Trace("theory::assertToTheory") << "TheoryEngine::markPropagation(): marking [" << d_propagationMapTimestamp << "] " << assertion << ", " << toTheoryId << " from " << originalAssertion << ", " << fromTheoryId << std::endl;

  // Mark the propagation
  d_propagationMap[toAssert] = toExplain;
  d_propagationMapTimestamp = d_propagationMapTimestamp + 1;

  return true;
}


void TheoryEngine::assertToTheory(TNode assertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId) {

  Trace("theory::assertToTheory") << "TheoryEngine::assertToTheory(" << assertion << ", " << toTheoryId << ", " << fromTheoryId << ")" << std::endl;

  Assert(toTheoryId != fromTheoryId);
  if(! d_logicInfo.isTheoryEnabled(toTheoryId) &&
     toTheoryId != THEORY_SAT_SOLVER) {
    stringstream ss;
    ss << "The logic was specified as " << d_logicInfo.getLogicString()
       << ", which doesn't include " << toTheoryId
       << ", but got an asserted fact to that theory." << endl
       << "The fact:" << endl
       << assertion;
    throw LogicException(ss.str());
  }

  if (d_inConflict) {
    return;
  }

  // If sharing is disabled, things are easy
  if (!d_logicInfo.isSharingEnabled()) {
    if (fromTheoryId == THEORY_SAT_SOLVER) {
      // Send to the apropriate theory
      theory::Theory* toTheory = theoryOf(toTheoryId);
      // We assert it, and we know it's preregistereed
      toTheory->assertFact(assertion, true);
      // Mark that we have more information
      d_factsAsserted = true;
    } else {
      Assert(toTheoryId == THEORY_SAT_SOLVER);
      // Check for propositional conflict
      bool value;
      if (d_propEngine->hasValue(assertion, value)) {
        if (!value) {
          Trace("theory::propagate") << "TheoryEngine::assertToTheory(" << assertion << ", " << toTheoryId << ", " << fromTheoryId << "): conflict" << std::endl;
          d_inConflict = true;
        } else {
          return;
        }
      }
      d_propagatedLiterals.push_back(assertion);
    }
    return;
  }

  // Polarity of the assertion
  bool polarity = assertion.getKind() != kind::NOT;

  // Atom of the assertion
  TNode atom = polarity ? assertion : assertion[0];

  // If sending to the shared terms database, it's also simple
  if (toTheoryId == THEORY_BUILTIN) {
    Assert(atom.getKind() == kind::EQUAL, "atom should be an EQUALity, not `%s'", atom.toString().c_str());
    if (markPropagation(assertion, assertion, toTheoryId, fromTheoryId)) {
      d_sharedTerms.assertEquality(atom, polarity, assertion);
    }
    return;
  }

  // Things from the SAT solver are already normalized, so they go
  // directly to the apropriate theory
  if (fromTheoryId == THEORY_SAT_SOLVER) {
    // We know that this is normalized, so just send it off to the theory
    if (markPropagation(assertion, assertion, toTheoryId, fromTheoryId)) {
      // We assert it, and we know it's preregistereed coming from the SAT solver directly
      theoryOf(toTheoryId)->assertFact(assertion, true);
      // Mark that we have more information
      d_factsAsserted = true;
    }
    return;
  }

  // Propagations to the SAT solver are just enqueued for pickup by
  // the SAT solver later
  if (toTheoryId == THEORY_SAT_SOLVER) {
    if (markPropagation(assertion, assertion, toTheoryId, fromTheoryId)) {
      // Enqueue for propagation to the SAT solver
      d_propagatedLiterals.push_back(assertion);
      // Check for propositional conflicts
      bool value;
      if (d_propEngine->hasValue(assertion, value) && !value) {
        d_inConflict = true;
      }
    }
    return;
  }

  // See if it rewrites to true or false directly
  Node normalizedLiteral = Rewriter::rewrite(assertion);
  if (normalizedLiteral.isConst()) {
    if (normalizedLiteral.getConst<bool>()) {
      // trivially true, but theories need to share even trivially true facts
      // unless of course it is the theory that normalized it
      if (Theory::theoryOf(atom) == toTheoryId) {
      	return;
      }
    } else {
      // Mark the propagation for explanations
      if (markPropagation(normalizedLiteral, assertion, toTheoryId, fromTheoryId)) {
        // Get the explanation (conflict will figure out where it came from)
        conflict(normalizedLiteral, toTheoryId);
      } else {
        Unreachable();
      }
      return;
    }
  }

  // Normalize to lhs < rhs if not a sat literal
  Assert(atom.getKind() == kind::EQUAL);
  Assert(atom[0] != atom[1]);

  Node normalizedAtom = atom;
  if (!d_propEngine->isSatLiteral(normalizedAtom)) {
    Node reverse = atom[1].eqNode(atom[0]);
    if (d_propEngine->isSatLiteral(reverse) || atom[0] > atom[1]) {
      normalizedAtom = reverse;
    }
  }
  Node normalizedAssertion = polarity ? normalizedAtom : normalizedAtom.notNode();

  // Try and assert (note that we assert the non-normalized one)
  if (markPropagation(normalizedAssertion, assertion, toTheoryId, fromTheoryId)) {
    // Check if has been pre-registered with the theory
    bool preregistered = d_propEngine->isSatLiteral(normalizedAssertion) && Theory::theoryOf(normalizedAtom) == toTheoryId;
    // Assert away
    theoryOf(toTheoryId)->assertFact(normalizedAssertion, preregistered);
    d_factsAsserted = true;
  }

  return;
}

void TheoryEngine::assertFact(TNode literal)
{
  Trace("theory") << "TheoryEngine::assertFact(" << literal << ")" << std::endl;

  d_propEngine->checkTime();

  // If we're in conflict, nothing to do
  if (d_inConflict) {
    return;
  }

  // Get the atom
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];

  if (d_logicInfo.isSharingEnabled()) {

    // If any shared terms, it's time to do sharing work
    if (d_sharedTerms.hasSharedTerms(atom)) {
      // Notify the theories the shared terms
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

    // If it's an equality, assert it to the shared term manager, even though the terms are not
    // yet shared. As the terms become shared later, the shared terms manager will then add them
    // to the assert the equality to the interested theories
    if (atom.getKind() == kind::EQUAL) {
      // Assert it to the the owning theory
      assertToTheory(literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
      // Shared terms manager will assert to interested theories directly, as the terms become shared
      assertToTheory(literal, /* to */ THEORY_BUILTIN, /* from */ THEORY_SAT_SOLVER);
    } else {
      // Not an equality, just assert to the appropriate theory
      assertToTheory(literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
    }
  } else {
    // Assert the fact to the appropriate theory directly
    assertToTheory(literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
  }
}

bool TheoryEngine::propagate(TNode literal, theory::TheoryId theory) {

  Debug("theory::propagate") << "TheoryEngine::propagate(" << literal << ", " << theory << ")" << std::endl;

  d_propEngine->checkTime();

  if(Dump.isOn("t-propagations")) {
    Dump("t-propagations") << CommentCommand("negation of theory propagation: expect valid")
                           << QueryCommand(literal.toExpr());
  }
  if(Dump.isOn("missed-t-propagations")) {
    d_hasPropagated.insert(literal);
  }

  // Get the atom
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];

  if (d_logicInfo.isSharingEnabled() && atom.getKind() == kind::EQUAL) {
    if (d_propEngine->isSatLiteral(literal)) {
      // We propagate SAT literals to SAT
      assertToTheory(literal, /* to */ THEORY_SAT_SOLVER, /* from */ theory);
    }
    if (theory != THEORY_BUILTIN) {
      // Assert to the shared terms database
      assertToTheory(literal, /* to */ THEORY_BUILTIN, /* from */ theory);
    }
  } else {
    // Just send off to the SAT solver
    Assert(d_propEngine->isSatLiteral(literal));
    assertToTheory(literal, /* to */ THEORY_SAT_SOLVER, /* from */ theory);
  }

  return !d_inConflict;
}


theory::EqualityStatus TheoryEngine::getEqualityStatus(TNode a, TNode b) {
  Assert(a.getType().isComparableTo(b.getType()));
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

Node TheoryEngine::getModelValue(TNode var) {
  Assert(d_sharedTerms.isShared(var));
  return theoryOf(Theory::theoryOf(var.getType()))->getModelValue(var);
}

static Node mkExplanation(const std::vector<NodeTheoryPair>& explanation) {

  std::set<TNode> all;
  for (unsigned i = 0; i < explanation.size(); ++ i) {
    Assert(explanation[i].theory == THEORY_SAT_SOLVER);
    all.insert(explanation[i].node);
  }

  if (all.size() == 0) {
    // Normalize to true
    return NodeManager::currentNM()->mkConst<bool>(true);
  }

  if (all.size() == 1) {
    // All the same, or just one
    return explanation[0].node;
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}


Node TheoryEngine::getExplanation(TNode node) {
  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << "): current propagation index = " << d_propagationMapTimestamp << std::endl;

  bool polarity = node.getKind() != kind::NOT;
  TNode atom = polarity ? node : node[0];

  // If we're not in shared mode, explanations are simple
  if (!d_logicInfo.isSharingEnabled()) {
    Node explanation = theoryOf(atom)->explain(node);
    Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << std::endl;
    return explanation;
  }

  // Initial thing to explain
  NodeTheoryPair toExplain(node, THEORY_SAT_SOLVER, d_propagationMapTimestamp);
  Assert(d_propagationMap.find(toExplain) != d_propagationMap.end());
  // Create the workplace for explanations
  std::vector<NodeTheoryPair> explanationVector;
  explanationVector.push_back(d_propagationMap[toExplain]);
  // Process the explanation
  getExplanation(explanationVector);
  Node explanation = mkExplanation(explanationVector);

  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << std::endl;

  return explanation;
}

theory::LemmaStatus TheoryEngine::lemma(TNode node, bool negated, bool removable) {
  if(Dump.isOn("t-lemmas")) {
    Node n = node;
    if (negated) {
      n = node.negate();
    }
    Dump("t-lemmas") << CommentCommand("theory lemma: expect valid")
                     << QueryCommand(n.toExpr());
  }

  // Share with other portfolio threads
  if(options::lemmaOutputChannel() != NULL) {
    options::lemmaOutputChannel()->notifyNewLemma(node.toExpr());
  }

  // Remove the ITEs
  std::vector<Node> additionalLemmas;
  IteSkolemMap iteSkolemMap;
  additionalLemmas.push_back(node);
  d_iteRemover.run(additionalLemmas, iteSkolemMap);
  additionalLemmas[0] = theory::Rewriter::rewrite(additionalLemmas[0]);

  // assert to prop engine
  d_propEngine->assertLemma(additionalLemmas[0], negated, removable);
  for (unsigned i = 1; i < additionalLemmas.size(); ++ i) {
    additionalLemmas[i] = theory::Rewriter::rewrite(additionalLemmas[i]);
    d_propEngine->assertLemma(additionalLemmas[i], false, removable);
  }

  // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
  // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
  if(negated) {
    // Can't we just get rid of passing around this 'negated' stuff?
    // Is it that hard for the propEngine to figure that out itself?
    // (I like the use of triple negation <evil laugh>.) --K
    additionalLemmas[0] = additionalLemmas[0].notNode();
    negated = false;
  }
  // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
  // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.

  // assert to decision engine
  if(!removable) {
    d_decisionEngine->addAssertions(additionalLemmas, 1, iteSkolemMap);
  }

  // Mark that we added some lemmas
  d_lemmasAdded = true;

  // Lemma analysis isn't online yet; this lemma may only live for this
  // user level.
  return theory::LemmaStatus(additionalLemmas[0], d_userContext->getLevel());
}

void TheoryEngine::conflict(TNode conflict, TheoryId theoryId) {

  Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << ")" << std::endl;

  // Mark that we are in conflict
  d_inConflict = true;

  if(Dump.isOn("t-conflicts")) {
    Dump("t-conflicts") << CommentCommand("theory conflict: expect unsat")
                        << CheckSatCommand(conflict.toExpr());
  }

  // In the multiple-theories case, we need to reconstruct the conflict
  if (d_logicInfo.isSharingEnabled()) {
    // Create the workplace for explanations
    std::vector<NodeTheoryPair> explanationVector;
    explanationVector.push_back(NodeTheoryPair(conflict, theoryId, d_propagationMapTimestamp));
    // Process the explanation
    getExplanation(explanationVector);
    Node fullConflict = mkExplanation(explanationVector);
    Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << "): full = " << fullConflict << std::endl;
    Assert(properConflict(fullConflict));
    lemma(fullConflict, true, true);
  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    lemma(conflict, true, true);
  }
}

Node TheoryEngine::ppSimpITE(TNode assertion)
{
  Node result = d_iteSimplifier.simpITE(assertion);
  result = d_iteSimplifier.simplifyWithCare(Rewriter::rewrite(result));
  result = Rewriter::rewrite(result);
  return result;
}

void TheoryEngine::getExplanation(std::vector<NodeTheoryPair>& explanationVector)
{
  Assert(explanationVector.size() > 0);

  unsigned i = 0; // Index of the current literal we are processing
  unsigned j = 0; // Index of the last literal we are keeping

  while (i < explanationVector.size()) {

    // Get the current literal to explain
    NodeTheoryPair toExplain = explanationVector[i];

    Debug("theory::explain") << "TheoryEngine::explain(): processing [" << toExplain.timestamp << "] " << toExplain.node << " sent from " << toExplain.theory << std::endl;

    // If a treu constant or a negation of a false constant we can ignore it
    if (toExplain.node.isConst() && toExplain.node.getConst<bool>()) {
      ++ i;
      continue;
    }
    if (toExplain.node.getKind() == kind::NOT && toExplain.node[0].isConst() && !toExplain.node[0].getConst<bool>()) {
      ++ i;
      continue;
    }

    // If from the SAT solver, keep it
    if (toExplain.theory == THEORY_SAT_SOLVER) {
      explanationVector[j++] = explanationVector[i++];
      continue;
    }

    // If an and, expand it
    if (toExplain.node.getKind() == kind::AND) {
      Debug("theory::explain") << "TheoryEngine::explain(): expanding " << toExplain.node << " got from " << toExplain.theory << std::endl;
      for (unsigned k = 0; k < toExplain.node.getNumChildren(); ++ k) {
        NodeTheoryPair newExplain(toExplain.node[k], toExplain.theory, toExplain.timestamp);
        explanationVector.push_back(newExplain);
      }
      ++ i;
      continue;
    }

    // See if it was sent to the theory by another theory
    PropagationMap::const_iterator find = d_propagationMap.find(toExplain);
    if (find != d_propagationMap.end()) {
      // There is some propagation, check if its a timely one
      if ((*find).second.timestamp < toExplain.timestamp) {
        explanationVector.push_back((*find).second);
        ++ i;
        continue;
      }
    }

    // It was produced by the theory, so ask for an explanation
    Node explanation;
    if (toExplain.theory == THEORY_BUILTIN) {
      explanation = d_sharedTerms.explain(toExplain.node);
    } else {
      explanation = theoryOf(toExplain.theory)->explain(toExplain.node);
    }
    Debug("theory::explain") << "TheoryEngine::explain(): got explanation " << explanation << " got from " << toExplain.theory << std::endl;
    Assert(explanation != toExplain.node, "wasn't sent to you, so why are you explaining it trivially");
    // Mark the explanation
    NodeTheoryPair newExplain(explanation, toExplain.theory, toExplain.timestamp);
    explanationVector.push_back(newExplain);
    ++ i;
  }

  // Keep only the relevant literals
  explanationVector.resize(j);
}


void TheoryEngine::ppUnconstrainedSimp(vector<Node>& assertions)
{
  d_unconstrainedSimp.processAssertions(assertions);
}


void TheoryEngine::setUserAttribute(const std::string& attr, Node n) {
  Trace("te-attr") << "set user attribute " << attr << " " << n << std::endl;
  if( d_attr_handle.find( attr )!=d_attr_handle.end() ){
    for( size_t i=0; i<d_attr_handle[attr].size(); i++ ){
      d_attr_handle[attr][i]->setUserAttribute(attr, n);
    }
  } else {
    //unhandled exception?
  }
}

void TheoryEngine::handleUserAttribute(const char* attr, Theory* t) {
  Trace("te-attr") << "Handle user attribute " << attr << " " << t << std::endl;
  std::string str( attr );
  d_attr_handle[ str ].push_back( t );
}

void TheoryEngine::checkTheoryAssertionsWithModel() {
  for(TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
    if(theoryId != THEORY_REWRITERULES) {
      Theory* theory = d_theoryTable[theoryId];
      if(theory && d_logicInfo.isTheoryEnabled(theoryId)) {
        for(context::CDList<Assertion>::const_iterator it = theory->facts_begin(),
              it_end = theory->facts_end();
            it != it_end;
            ++it) {
          Node assertion = (*it).assertion;
          Node val = getModel()->getValue(assertion);
          Assert(val == d_true);
        }
      }
    }
  }
}
