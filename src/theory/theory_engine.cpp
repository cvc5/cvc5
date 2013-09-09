/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): Christopher L. Conway, Kshitij Bansal, Liana Hadarean, Clark Barrett, Tim King, Andrew Reynolds
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

//#include "theory/ite_simplifier.h"
//#include "theory/ite_compressor.h"
#include "theory/ite_utilities.h"
#include "theory/unconstrained_simplifier.h"

#include "theory/theory_model.h"

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/first_order_model.h"

#include "theory/uf/equality_engine.h"

#include "theory/rewriterules/efficient_e_matching.h"

#include "proof/proof_manager.h"

using namespace std;

using namespace CVC4;
using namespace CVC4::theory;

void TheoryEngine::finishInit() {
  // initialize the quantifiers engine
  d_quantEngine = new QuantifiersEngine(d_context, d_userContext, this);

  if (d_logicInfo.isQuantified()) {
    d_quantEngine->finishInit();
    Assert(d_masterEqualityEngine == 0);
    d_masterEqualityEngine = new eq::EqualityEngine(d_masterEENotify,getSatContext(), "theory::master");

    for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
      if (d_theoryTable[theoryId]) {
        d_theoryTable[theoryId]->setQuantifiersEngine(d_quantEngine);
        d_theoryTable[theoryId]->setMasterEqualityEngine(d_masterEqualityEngine);
      }
    }
  }

  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    if (d_theoryTable[theoryId]) {
      d_theoryTable[theoryId]->finishInit();
    }
  }
}

void TheoryEngine::eqNotifyNewClass(TNode t){
  d_quantEngine->addTermToDatabase( t );
  if( d_logicInfo.isQuantified() && options::quantConflictFind() ){
    d_quantEngine->getConflictFind()->newEqClass( t );
  }
}

void TheoryEngine::eqNotifyPreMerge(TNode t1, TNode t2){
  //TODO: add notification to efficient E-matching
  if( d_logicInfo.isQuantified() ){
    d_quantEngine->getEfficientEMatcher()->merge( t1, t2 );
    if( options::quantConflictFind() ){
      d_quantEngine->getConflictFind()->merge( t1, t2 );
    }
  }
}

void TheoryEngine::eqNotifyPostMerge(TNode t1, TNode t2){

}

void TheoryEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){
  if( d_logicInfo.isQuantified() ){
    if( options::quantConflictFind() ){
      d_quantEngine->getConflictFind()->assertDisequal( t1, t2 );
    }
  }
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
  d_atomRequests(context),
  d_iteRemover(iteRemover),
  d_combineTheoriesTime("TheoryEngine::combineTheoriesTime"),
  d_true(),
  d_false(),
  d_interrupted(false),
  d_inPreregister(false),
  d_factsAsserted(context, false),
  d_preRegistrationVisitor(this, context),
  d_sharedTermsVisitor(d_sharedTerms),
  d_unconstrainedSimp(new UnconstrainedSimplifier(context, logicInfo)),
  d_bvToBoolPreprocessor()
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }

  // build model information if applicable
  d_curr_model = new theory::TheoryModel(userContext, "DefaultModel", true);
  d_curr_model_builder = new theory::TheoryEngineModelBuilder(this);

  StatisticsRegistry::registerStat(&d_combineTheoriesTime);
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

  PROOF (ProofManager::currentPM()->initTheoryProof(); );

  d_iteUtilities = new ITEUtilities(d_iteRemover.getContainsVisitor());
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

  delete d_unconstrainedSimp;

  delete d_iteUtilities;
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
      Theory::Set theories = NodeVisitor<PreRegisterVisitor>::run(d_preRegistrationVisitor, preprocessed);
      theories = Theory::setRemove(THEORY_BOOL, theories);
      // Remove the top theory, if any more that means multiple theories were involved
      bool multipleTheories = Theory::setRemove(Theory::theoryOf(preprocessed), theories);
      TheoryId i;
      // These checks don't work with finite model finding, because it
      // uses Rational constants to represent cardinality constraints,
      // even though arithmetic isn't actually involved.
      if(!options::finiteModelFind()) {
        while((i = Theory::setPop(theories)) != THEORY_LAST) {
          if(!d_logicInfo.isTheoryEnabled(i)) {
            LogicInfo newLogicInfo = d_logicInfo.getUnlockedCopy();
            newLogicInfo.enableTheory(i);
            newLogicInfo.lock();
            stringstream ss;
            ss << "The logic was specified as " << d_logicInfo.getLogicString()
               << ", which doesn't include " << i
               << ", but found a term in that theory." << endl
               << "You might want to extend your logic to "
               << newLogicInfo.getLogicString() << endl;
            throw LogicException(ss.str());
          }
        }
      }
      if (multipleTheories) {
        // Collect the shared terms if there are multiple theories
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
        Trace(tag) << "--------------------------------------------" << endl;
        Trace(tag) << "Assertions of " << theory->getId() << ": " << endl;
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
          Trace(tag) << "Shared terms of " << theory->getId() << ": " << endl;
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
       theoryOf(THEORY)->check(effort); \
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

    Debug("theory") << "TheoryEngine::check(" << effort << "): d_factsAsserted = " << (d_factsAsserted ? "true" : "false") << endl;

    // If in full effort, we have a fake new assertion just to jumpstart the checking
    if (Theory::fullEffort(effort)) {
      d_factsAsserted = true;
    }

    // Check until done
    while (d_factsAsserted && !d_inConflict && !d_lemmasAdded) {

      Debug("theory") << "TheoryEngine::check(" << effort << "): running check" << endl;

      Trace("theory::assertions") << endl;
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

      Debug("theory") << "TheoryEngine::check(" << effort << "): running propagation after the initial check" << endl;

      // We are still satisfiable, propagate as much as possible
      propagate(effort);

      // We do combination if all has been processed and we are in fullcheck
      if (Theory::fullEffort(effort) && d_logicInfo.isSharingEnabled() && !d_factsAsserted && !d_lemmasAdded) {
        // Do the combination
        Debug("theory") << "TheoryEngine::check(" << effort << "): running combination" << endl;
        combineTheories();
      }
    }

    // Must consult quantifiers theory for last call to ensure sat, or otherwise add a lemma
    if( effort == Theory::EFFORT_FULL && ! d_inConflict && ! needCheck() ) {
      //d_theoryTable[THEORY_STRINGS]->check(Theory::EFFORT_LAST_CALL);
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

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas") << endl;

    if(!d_inConflict && Theory::fullEffort(effort) && d_masterEqualityEngine != NULL && !d_lemmasAdded) {
      AlwaysAssert(d_masterEqualityEngine->consistent());
    }
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

  Debug("sharing") << "TheoryEngine::combineTheories()" << endl;

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

  Debug("sharing") << "TheoryEngine::combineTheories(): care graph size = " << careGraph.size() << endl;

  // Now add splitters for the ones we are interested in
  CareGraph::const_iterator care_it = careGraph.begin();
  CareGraph::const_iterator care_it_end = careGraph.end();
  for (; care_it != care_it_end; ++ care_it) {
    const CarePair& carePair = *care_it;

    Debug("sharing") << "TheoryEngine::combineTheories(): checking " << carePair.a << " = " << carePair.b << " from " << carePair.theory << endl;

    Assert(d_sharedTerms.isShared(carePair.a) || carePair.a.isConst());
    Assert(d_sharedTerms.isShared(carePair.b) || carePair.b.isConst());

    // The equality in question (order for no repetition)
    Node equality = carePair.a.eqNode(carePair.b);

    // We need to split on it
    Debug("sharing") << "TheoryEngine::combineTheories(): requesting a split " << endl;
    lemma(equality.orNode(equality.notNode()), false, false, carePair.theory);
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
    for(unsigned i = 0; i < d_possiblePropagations.size(); ++i) {
      Node atom = d_possiblePropagations[i];
      bool value;
      if(d_propEngine->hasValue(atom, value)) {
        continue;
      }
      // Doesn't have a value, check it (and the negation)
      if(d_hasPropagated.find(atom) == d_hasPropagated.end()) {
        Dump("missed-t-propagations")
          << CommentCommand("Completeness check for T-propagations; expect invalid")
          << EchoCommand(atom.toString())
          << QueryCommand(atom.toExpr())
          << EchoCommand(atom.notNode().toString())
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
  Debug("model") << "TheoryEngine::getModel()" << endl;
  if( d_logicInfo.isQuantified() ) {
    Debug("model") << "Get model from quantifiers engine." << endl;
    return d_quantEngine->getModel();
  } else {
    Debug("model") << "Get default model." << endl;
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
  bool CVC4_UNUSED wasInConflict = d_inConflict;

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasPostsolve) { \
      theoryOf(THEORY)->postsolve(); \
      Assert(! d_inConflict || wasInConflict, "conflict raised during postsolve()"); \
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
    Trace("theory::assertToTheory") << "TheoryEngine::markPropagation(): already there" << endl;
    return false;
  }

  Trace("theory::assertToTheory") << "TheoryEngine::markPropagation(): marking [" << d_propagationMapTimestamp << "] " << assertion << ", " << toTheoryId << " from " << originalAssertion << ", " << fromTheoryId << endl;

  // Mark the propagation
  d_propagationMap[toAssert] = toExplain;
  d_propagationMapTimestamp = d_propagationMapTimestamp + 1;

  return true;
}


void TheoryEngine::assertToTheory(TNode assertion, TNode originalAssertion, theory::TheoryId toTheoryId, theory::TheoryId fromTheoryId) {

  Trace("theory::assertToTheory") << "TheoryEngine::assertToTheory(" << assertion << ", " << toTheoryId << ", " << fromTheoryId << ")" << endl;

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
    Assert(assertion == originalAssertion);
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
          Trace("theory::propagate") << "TheoryEngine::assertToTheory(" << assertion << ", " << toTheoryId << ", " << fromTheoryId << "): conflict (no sharing)" << endl;
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
    if (markPropagation(assertion, originalAssertion, toTheoryId, fromTheoryId)) {
      d_sharedTerms.assertEquality(atom, polarity, assertion);
    }
    return;
  }

  // Things from the SAT solver are already normalized, so they go
  // directly to the apropriate theory
  if (fromTheoryId == THEORY_SAT_SOLVER) {
    // We know that this is normalized, so just send it off to the theory
    if (markPropagation(assertion, originalAssertion, toTheoryId, fromTheoryId)) {
      // Is it preregistered
      bool preregistered = d_propEngine->isSatLiteral(assertion) && Theory::theoryOf(assertion) == toTheoryId;
      // We assert it
      theoryOf(toTheoryId)->assertFact(assertion, preregistered);
      // Mark that we have more information
      d_factsAsserted = true;
    }
    return;
  }

  // Propagations to the SAT solver are just enqueued for pickup by
  // the SAT solver later
  if (toTheoryId == THEORY_SAT_SOLVER) {
    if (markPropagation(assertion, originalAssertion, toTheoryId, fromTheoryId)) {
      // Enqueue for propagation to the SAT solver
      d_propagatedLiterals.push_back(assertion);
      // Check for propositional conflicts
      bool value;
      if (d_propEngine->hasValue(assertion, value) && !value) {
          Trace("theory::propagate") << "TheoryEngine::assertToTheory(" << assertion << ", " << toTheoryId << ", " << fromTheoryId << "): conflict (sharing)" << endl;
        d_inConflict = true;
      }
    }
    return;
  }

  Assert(atom.getKind() == kind::EQUAL);

  // Normalize
  Node normalizedLiteral = Rewriter::rewrite(assertion);

  // See if it rewrites false directly -> conflict
  if (normalizedLiteral.isConst()) {
    if (!normalizedLiteral.getConst<bool>()) {
      // Mark the propagation for explanations
      if (markPropagation(normalizedLiteral, originalAssertion, toTheoryId, fromTheoryId)) {
        // Get the explanation (conflict will figure out where it came from)
        conflict(normalizedLiteral, toTheoryId);
      } else {
        Unreachable();
      }
      return;
    }
  }

  // Try and assert (note that we assert the non-normalized one)
  if (markPropagation(assertion, originalAssertion, toTheoryId, fromTheoryId)) {
    // Check if has been pre-registered with the theory
    bool preregistered = d_propEngine->isSatLiteral(assertion) && Theory::theoryOf(assertion) == toTheoryId;
    // Assert away
    theoryOf(toTheoryId)->assertFact(assertion, preregistered);
    d_factsAsserted = true;
  }

  return;
}

void TheoryEngine::assertFact(TNode literal)
{
  Trace("theory") << "TheoryEngine::assertFact(" << literal << ")" << endl;

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
      assertToTheory(literal, literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
      // Shared terms manager will assert to interested theories directly, as the terms become shared
      assertToTheory(literal, literal, /* to */ THEORY_BUILTIN, /* from */ THEORY_SAT_SOLVER);

      // Now, let's check for any atom triggers from lemmas
      AtomRequests::atom_iterator it = d_atomRequests.getAtomIterator(atom);
      while (!it.done()) {
        const AtomRequests::Request& request = it.get();
        Node toAssert = polarity ? (Node) request.atom : request.atom.notNode();
        Debug("theory::atoms") << "TheoryEngine::assertFact(" << literal << "): sending requested " << toAssert << endl;
        assertToTheory(toAssert, literal, request.toTheory, THEORY_SAT_SOLVER);
        it.next();
      }

    } else {
      // Not an equality, just assert to the appropriate theory
      assertToTheory(literal, literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
    }
  } else {
    // Assert the fact to the appropriate theory directly
    assertToTheory(literal, literal, /* to */ Theory::theoryOf(atom), /* from */ THEORY_SAT_SOLVER);
  }
}

bool TheoryEngine::propagate(TNode literal, theory::TheoryId theory) {

  Debug("theory::propagate") << "TheoryEngine::propagate(" << literal << ", " << theory << ")" << endl;

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
      assertToTheory(literal, literal, /* to */ THEORY_SAT_SOLVER, /* from */ theory);
    }
    if (theory != THEORY_BUILTIN) {
      // Assert to the shared terms database
      assertToTheory(literal, literal, /* to */ THEORY_BUILTIN, /* from */ theory);
    }
  } else {
    // Just send off to the SAT solver
    Assert(d_propEngine->isSatLiteral(literal));
    assertToTheory(literal, literal, /* to */ THEORY_SAT_SOLVER, /* from */ theory);
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
  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << "): current propagation index = " << d_propagationMapTimestamp << endl;

  bool polarity = node.getKind() != kind::NOT;
  TNode atom = polarity ? node : node[0];

  // If we're not in shared mode, explanations are simple
  if (!d_logicInfo.isSharingEnabled()) {
    Node explanation = theoryOf(atom)->explain(node);
    Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << endl;
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

  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << endl;

  return explanation;
}

struct AtomsCollect {

  std::vector<TNode> d_atoms;
  std::hash_set<TNode, TNodeHashFunction> d_visited;

public:

  typedef void return_type;

  bool alreadyVisited(TNode current, TNode parent) {
    // Check if already visited
    if (d_visited.find(current) != d_visited.end()) return true;
    // Don't visit non-boolean
    if (!current.getType().isBoolean()) return true;
    // New node
    return false;
  }

  void visit(TNode current, TNode parent) {
    if (Theory::theoryOf(current) != theory::THEORY_BOOL) {
      d_atoms.push_back(current);
    }
    d_visited.insert(current);
  }

  void start(TNode node) {}
  void done(TNode node) {}

  std::vector<TNode> getAtoms() const {
    return d_atoms;
  }
};

void TheoryEngine::ensureLemmaAtoms(const std::vector<TNode>& atoms, theory::TheoryId atomsTo) {
  for (unsigned i = 0; i < atoms.size(); ++ i) {

    // Non-equality atoms are either owned by theory or they don't make sense
    if (atoms[i].getKind() != kind::EQUAL) {
      continue;
    }

    // The equality
    Node eq = atoms[i];
    // Simple normalization to not repeat stuff
    if (eq[0] > eq[1]) {
      eq = eq[1].eqNode(eq[0]);
    }

    // Rewrite the equality
    Node eqNormalized = Rewriter::rewrite(atoms[i]);

    Debug("theory::atoms") << "TheoryEngine::ensureLemmaAtoms(): " << eq << " with nf " << eqNormalized << endl;

    // If the equality is a boolean constant, we send immediately
    if (eqNormalized.isConst()) {
      if (eqNormalized.getConst<bool>()) {
        assertToTheory(eq, eqNormalized, /** to */ atomsTo, /** Sat solver */ theory::THEORY_SAT_SOLVER);
      } else {
        assertToTheory(eq.notNode(), eqNormalized.notNode(), /** to */ atomsTo, /** Sat solver */ theory::THEORY_SAT_SOLVER);
      }
      continue;
    }

    Assert(eqNormalized.getKind() == kind::EQUAL);


    // If the normalization did the just flips, keep the flip
    if (eqNormalized[0] == eq[1] && eqNormalized[1] == eq[0]) {
      eq = eqNormalized;
    }

    // Check if the equality is already known by the sat solver
    if (d_propEngine->isSatLiteral(eqNormalized)) {
      bool value;
      if (d_propEngine->hasValue(eqNormalized, value)) {
        if (value) {
          assertToTheory(eq, eqNormalized, atomsTo, theory::THEORY_SAT_SOLVER);
          continue;
        } else {
          assertToTheory(eq.notNode(), eqNormalized.notNode(), atomsTo, theory::THEORY_SAT_SOLVER);
          continue;
        }
      }
    }

    // If the theory is asking about a different form, or the form is ok but if will go to a different theory
    // then we must figure it out
    if (eqNormalized != eq || Theory::theoryOf(eq) != atomsTo) {
      // If you get eqNormalized, send atoms[i] to atomsTo
      d_atomRequests.add(eqNormalized, eq, atomsTo);
    }
  }
}

theory::LemmaStatus TheoryEngine::lemma(TNode node, bool negated, bool removable, theory::TheoryId atomsTo) {

  // Do we need to check atoms
  if (atomsTo != theory::THEORY_LAST) {
    Debug("theory::atoms") << "TheoryEngine::lemma(" << node << ", " << atomsTo << ")" << endl;
    AtomsCollect collectAtoms;
    NodeVisitor<AtomsCollect>::run(collectAtoms, node);
    ensureLemmaAtoms(collectAtoms.getAtoms(), atomsTo);
  }

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

  if(Debug.isOn("lemma-ites")) {
    Debug("lemma-ites") << "removed ITEs from lemma: " << node << endl;
    Debug("lemma-ites") << " + now have the following "
                        << additionalLemmas.size() << " lemma(s):" << endl;
    for(std::vector<Node>::const_iterator i = additionalLemmas.begin();
        i != additionalLemmas.end();
        ++i) {
      Debug("lemma-ites") << " + " << *i << endl;
    }
    Debug("lemma-ites") << endl;
  }

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

  Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << ")" << endl;

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
    Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << "): full = " << fullConflict << endl;
    Assert(properConflict(fullConflict));
    lemma(fullConflict, true, true, THEORY_LAST);
  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    lemma(conflict, true, true, THEORY_LAST);
  }
}

void TheoryEngine::ppBvToBool(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  d_bvToBoolPreprocessor.liftBoolToBV(assertions, new_assertions);
}

Node TheoryEngine::ppSimpITE(TNode assertion)
{
  if(!d_iteRemover.containsTermITE(assertion)){
    return assertion;
  }else{

    Node result = d_iteUtilities->simpITE(assertion);
    Node res_rewritten = Rewriter::rewrite(result);

    if(options::simplifyWithCareEnabled()){
      Chat() << "starting simplifyWithCare()" << endl;
      Node postSimpWithCare = d_iteUtilities->simplifyWithCare(res_rewritten);
      Chat() << "ending simplifyWithCare()"
             << " post simplifyWithCare()" << postSimpWithCare.getId() << endl;
      result = Rewriter::rewrite(postSimpWithCare);
    }else{
      result = res_rewritten;
    }

    return result;
  }
}

bool TheoryEngine::donePPSimpITE(std::vector<Node>& assertions){
  bool result = true;
  if(d_iteUtilities->simpIteDidALotOfWorkHeuristic()){
    if(options::compressItes()){
      result = d_iteUtilities->compress(assertions);
    }

    if(result){
      // if false, don't bother to reclaim memory here.
      NodeManager* nm = NodeManager::currentNM();
      if(nm->poolSize() >= options::zombieHuntThreshold()){
        Chat() << "..ite simplifier did quite a bit of work.. " << nm->poolSize() << endl;
        Chat() << "....node manager contains " << nm->poolSize() << " nodes before cleanup" << endl;
        d_iteUtilities->clear();
        Rewriter::garbageCollect();
        d_iteRemover.garbageCollect();
        nm->reclaimZombiesUntil(options::zombieHuntThreshold());
        Chat() << "....node manager contains " << nm->poolSize() << " nodes after cleanup" << endl;
      }
    }
  }
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

    Debug("theory::explain") << "TheoryEngine::explain(): processing [" << toExplain.timestamp << "] " << toExplain.node << " sent from " << toExplain.theory << endl;

    // If a true constant or a negation of a false constant we can ignore it
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
      Debug("theory::explain") << "TheoryEngine::explain(): expanding " << toExplain.node << " got from " << toExplain.theory << endl;
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
    Debug("theory::explain") << "TheoryEngine::explain(): got explanation " << explanation << " got from " << toExplain.theory << endl;
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
  d_unconstrainedSimp->processAssertions(assertions);
}


void TheoryEngine::setUserAttribute(const std::string& attr, Node n) {
  Trace("te-attr") << "set user attribute " << attr << " " << n << endl;
  if( d_attr_handle.find( attr )!=d_attr_handle.end() ){
    for( size_t i=0; i<d_attr_handle[attr].size(); i++ ){
      d_attr_handle[attr][i]->setUserAttribute(attr, n);
    }
  } else {
    //unhandled exception?
  }
}

void TheoryEngine::handleUserAttribute(const char* attr, Theory* t) {
  Trace("te-attr") << "Handle user attribute " << attr << " " << t << endl;
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
          if(val != d_true) {
            stringstream ss;
            ss << theoryId << " has an asserted fact that the model doesn't satisfy." << endl
               << "The fact: " << assertion << endl
               << "Model value: " << val << endl;
            InternalError(ss.str());
          }
        }
      }
    }
  }
}
