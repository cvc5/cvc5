/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine
 **
 ** The theory engine.
 **/

#include "theory/theory_engine.h"

#include <list>
#include <vector>

#include "decision/decision_engine.h"
#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "options/bv_options.h"
#include "options/options.h"
#include "options/proof_options.h"
#include "options/quantifiers_options.h"
#include "proof/cnf_proof.h"
#include "proof/lemma_proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "smt/ite_removal.h"
#include "smt/logic_exception.h"
#include "smt_util/lemma_output_channel.h"
#include "smt_util/node_visitor.h"
#include "theory/arith/arith_ite_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/ite_utilities.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "theory/uf/equality_engine.h"
#include "theory/unconstrained_simplifier.h"
#include "util/resource_manager.h"

using namespace std;

using namespace CVC4::theory;

namespace CVC4 {

inline void flattenAnd(Node n, std::vector<TNode>& out){
  Assert(n.getKind() == kind::AND);
  for(Node::iterator i=n.begin(), i_end=n.end(); i != i_end; ++i){
    Node curr = *i;
    if(curr.getKind() == kind::AND){
      flattenAnd(curr, out);
    }else{
      out.push_back(curr);
    }
  }
}

inline Node flattenAnd(Node n){
  std::vector<TNode> out;
  flattenAnd(n, out);
  return NodeManager::currentNM()->mkNode(kind::AND, out);
}

theory::LemmaStatus TheoryEngine::EngineOutputChannel::lemma(TNode lemma,
                                                             ProofRule rule,
                                                             bool removable,
                                                             bool preprocess,
                                                             bool sendAtoms) {
  Debug("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")"
                         << ", preprocess = " << preprocess << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  PROOF({ registerLemmaRecipe(lemma, lemma, preprocess, d_theory); });

  theory::LemmaStatus result =
      d_engine->lemma(lemma, rule, false, removable, preprocess,
                      sendAtoms ? d_theory : theory::THEORY_LAST);
  return result;
}

void TheoryEngine::EngineOutputChannel::registerLemmaRecipe(Node lemma, Node originalLemma, bool preprocess, theory::TheoryId theoryId) {
  // During CNF conversion, conjunctions will be broken down into
  // multiple lemmas. In order for the recipes to match, we have to do
  // the same here.
  NodeManager* nm = NodeManager::currentNM();

  if (preprocess)
    lemma = d_engine->preprocess(lemma);

  bool negated = (lemma.getKind() == kind::NOT);
  Node nnLemma = negated ? lemma[0] : lemma;

  switch (nnLemma.getKind()) {

  case kind::AND:
    if (!negated) {
      for (unsigned i = 0; i < nnLemma.getNumChildren(); ++i)
        registerLemmaRecipe(nnLemma[i], originalLemma, false, theoryId);
    } else {
      NodeBuilder<> builder(kind::OR);
      for (unsigned i = 0; i < nnLemma.getNumChildren(); ++i)
        builder << nnLemma[i].negate();

      Node disjunction = (builder.getNumChildren() == 1) ? builder[0] : builder;
      registerLemmaRecipe(disjunction, originalLemma, false, theoryId);
    }
    break;

  case kind::IFF:
    if (!negated) {
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0], nnLemma[1].negate()), originalLemma, false, theoryId);
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0].negate(), nnLemma[1]), originalLemma, false, theoryId);
    } else {
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0], nnLemma[1]), originalLemma, false, theoryId);
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0].negate(), nnLemma[1].negate()), originalLemma, false, theoryId);
    }
    break;

  case kind::ITE:
    if (!negated) {
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0].negate(), nnLemma[1]), originalLemma, false, theoryId);
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0], nnLemma[2]), originalLemma, false, theoryId);
    } else {
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0].negate(), nnLemma[1].negate()), originalLemma, false, theoryId);
      registerLemmaRecipe(nm->mkNode(kind::OR, nnLemma[0], nnLemma[2].negate()), originalLemma, false, theoryId);
    }
    break;

  default:
    break;
  }

  // Theory lemmas have one step that proves the empty clause
  LemmaProofRecipe proofRecipe;
  Node emptyNode;
  LemmaProofRecipe::ProofStep proofStep(theoryId, emptyNode);

  // Remember the original lemma, so we can report this later when asked to
  proofRecipe.setOriginalLemma(originalLemma);

  // Record the assertions and rewrites
  Node rewritten;
  if (lemma.getKind() == kind::OR) {
    for (unsigned i = 0; i < lemma.getNumChildren(); ++i) {
      rewritten = theory::Rewriter::rewrite(lemma[i]);
      if (rewritten != lemma[i]) {
        proofRecipe.addRewriteRule(lemma[i].negate(), rewritten.negate());
      }
      proofStep.addAssertion(lemma[i]);
      proofRecipe.addBaseAssertion(rewritten);
    }
  } else {
    rewritten = theory::Rewriter::rewrite(lemma);
    if (rewritten != lemma) {
      proofRecipe.addRewriteRule(lemma.negate(), rewritten.negate());
    }
    proofStep.addAssertion(lemma);
    proofRecipe.addBaseAssertion(rewritten);
  }
  proofRecipe.addStep(proofStep);
  ProofManager::getCnfProof()->setProofRecipe(&proofRecipe);
}

theory::LemmaStatus TheoryEngine::EngineOutputChannel::splitLemma(
    TNode lemma, bool removable) {
  Debug("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")" << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  Debug("pf::explain") << "TheoryEngine::EngineOutputChannel::splitLemma( "
                       << lemma << " )" << std::endl;
  theory::LemmaStatus result =
      d_engine->lemma(lemma, RULE_SPLIT, false, removable, false, d_theory);
  return result;
}

bool TheoryEngine::EngineOutputChannel::propagate(TNode literal)
  throw(AssertionException, UnsafeInterruptException) {
  Debug("theory::propagate") << "EngineOutputChannel<" << d_theory << ">::propagate(" << literal << ")" << std::endl;
  ++ d_statistics.propagations;
  d_engine->d_outputChannelUsed = true;
  return d_engine->propagate(literal, d_theory);
}

void TheoryEngine::EngineOutputChannel::conflict(TNode conflictNode, Proof* pf)
  throw(AssertionException, UnsafeInterruptException) {
  Trace("theory::conflict") << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode << ")" << std::endl;
  Assert (pf == NULL); // Theory shouldn't be producing proofs yet
  ++ d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  d_engine->conflict(conflictNode, d_theory);
}

void TheoryEngine::finishInit() {
  // initialize the quantifiers engine
  d_quantEngine = new QuantifiersEngine(d_context, d_userContext, this);

  //initialize the model
  if( d_logicInfo.isQuantified() ) {
    d_curr_model = d_quantEngine->getModel();
  } else {
    d_curr_model = new theory::TheoryModel(d_userContext, "DefaultModel", true);
    d_aloc_curr_model = true;
  }

  if (d_logicInfo.isQuantified()) {
    d_quantEngine->finishInit();
    Assert(d_masterEqualityEngine == 0);
    d_masterEqualityEngine = new eq::EqualityEngine(d_masterEENotify,getSatContext(), "theory::master", false);

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
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->eqNotifyNewClass( t );
  }
}

void TheoryEngine::eqNotifyPreMerge(TNode t1, TNode t2){
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->eqNotifyPreMerge( t1, t2 );
  }
}

void TheoryEngine::eqNotifyPostMerge(TNode t1, TNode t2){
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->eqNotifyPostMerge( t1, t2 );
  }
}

void TheoryEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason){
  if (d_logicInfo.isQuantified()) {
    d_quantEngine->eqNotifyDisequal( t1, t2, reason );
  }
}


TheoryEngine::TheoryEngine(context::Context* context,
                           context::UserContext* userContext,
                           RemoveITE& iteRemover,
                           const LogicInfo& logicInfo,
                           LemmaChannels* channels)
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
  d_aloc_curr_model(false),
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
  d_resourceManager(NodeManager::currentResourceManager()),
  d_channels(channels),
  d_inPreregister(false),
  d_factsAsserted(context, false),
  d_preRegistrationVisitor(this, context),
  d_sharedTermsVisitor(d_sharedTerms),
  d_unconstrainedSimp(new UnconstrainedSimplifier(context, logicInfo)),
  d_bvToBoolPreprocessor(),
  d_theoryAlternatives(),
  d_attr_handle(),
  d_arithSubstitutionsAdded("theory::arith::zzz::arith::substitutions", 0)
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST;
      ++ theoryId)
  {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }

  // build model information if applicable
  d_curr_model_builder = new theory::TheoryEngineModelBuilder(this);

  smtStatisticsRegistry()->registerStat(&d_combineTheoriesTime);
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

#ifdef CVC4_PROOF
  ProofManager::currentPM()->initTheoryProofEngine();
#endif

  d_iteUtilities = new ITEUtilities(d_iteRemover.getContainsVisitor());

  smtStatisticsRegistry()->registerStat(&d_arithSubstitutionsAdded);
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
  if( d_aloc_curr_model ){
    delete d_curr_model;
  }

  delete d_quantEngine;

  delete d_masterEqualityEngine;

  smtStatisticsRegistry()->unregisterStat(&d_combineTheoriesTime);

  delete d_unconstrainedSimp;

  delete d_iteUtilities;

  smtStatisticsRegistry()->unregisterStat(&d_arithSubstitutionsAdded);
}

void TheoryEngine::interrupt() throw(ModalException) {
  d_interrupted = true;
}

void TheoryEngine::preRegister(TNode preprocessed) {

  Debug("theory") << "TheoryEngine::preRegister( " << preprocessed << ")" << std::endl;
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
  // spendResource();

  // Reset the interrupt flag
  d_interrupted = false;

#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    if (theory::TheoryTraits<THEORY>::hasCheck && d_logicInfo.isTheoryEnabled(THEORY)) { \
       theoryOf(THEORY)->check(effort); \
       if (d_inConflict) { \
         Debug("conflict") << THEORY << " in conflict. " << std::endl; \
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

      if(Theory::fullEffort(effort)) {
        Trace("theory::assertions::fulleffort") << endl;
        if (Trace.isOn("theory::assertions::fulleffort")) {
          printAssertions("theory::assertions::fulleffort");
        }
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
      if (Theory::fullEffort(effort) && d_logicInfo.isSharingEnabled() && !d_factsAsserted && !d_lemmasAdded && !d_inConflict) {
        // Do the combination
        Debug("theory") << "TheoryEngine::check(" << effort << "): running combination" << endl;
        combineTheories();
        if(d_logicInfo.isQuantified()){
          d_quantEngine->notifyCombineTheories();
        }
      }
    }

    // Must consult quantifiers theory for last call to ensure sat, or otherwise add a lemma
    if( effort == Theory::EFFORT_FULL && ! d_inConflict && ! needCheck() ) {
      Trace("theory::assertions-model") << endl;
      if (Trace.isOn("theory::assertions-model")) {
        printAssertions("theory::assertions-model");
      }
      //checks for theories requiring the model go at last call
      bool builtModel = false;
      for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
        if( theoryId!=THEORY_QUANTIFIERS ){
          Theory* theory = d_theoryTable[theoryId];
          if (theory && d_logicInfo.isTheoryEnabled(theoryId)) {
            if( theory->needsCheckLastEffort() ){
              if( !builtModel ){
                builtModel = true;
                d_curr_model_builder->buildModel(d_curr_model, false);
              }
              theory->check(Theory::EFFORT_LAST_CALL);
            }
          }
        }
      }
      if( ! d_inConflict && ! needCheck() ){
        if(d_logicInfo.isQuantified()) {
          // quantifiers engine must pass effort last call check
          d_quantEngine->check(Theory::EFFORT_LAST_CALL);
          // if returning incomplete or SAT, we have ensured that d_curr_model has been built with fullModel=true
        } else if(options::produceModels()) {
          // must build model at this point
          d_curr_model_builder->buildModel(d_curr_model, true);
        }
      }
    }

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas");
    Debug("theory") << ", need check = " << (needCheck() ? "YES" : "NO") << endl;

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

  Trace("combineTheories") << "TheoryEngine::combineTheories()" << endl;

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

  Trace("combineTheories") << "TheoryEngine::combineTheories(): care graph size = " << careGraph.size() << endl;

  // Now add splitters for the ones we are interested in
  CareGraph::const_iterator care_it = careGraph.begin();
  CareGraph::const_iterator care_it_end = careGraph.end();

  for (; care_it != care_it_end; ++ care_it) {
    const CarePair& carePair = *care_it;

    Debug("combineTheories") << "TheoryEngine::combineTheories(): checking " << carePair.a << " = " << carePair.b << " from " << carePair.theory << endl;

    Assert(d_sharedTerms.isShared(carePair.a) || carePair.a.isConst());
    Assert(d_sharedTerms.isShared(carePair.b) || carePair.b.isConst());

    // The equality in question (order for no repetition)
    Node equality = carePair.a.eqNode(carePair.b);
    // EqualityStatus es = getEqualityStatus(carePair.a, carePair.b);
    // Debug("combineTheories") << "TheoryEngine::combineTheories(): " <<
    //   (es == EQUALITY_TRUE_AND_PROPAGATED ? "EQUALITY_TRUE_AND_PROPAGATED" :
    //   es == EQUALITY_FALSE_AND_PROPAGATED ? "EQUALITY_FALSE_AND_PROPAGATED" :
    //   es == EQUALITY_TRUE ? "EQUALITY_TRUE" :
    //   es == EQUALITY_FALSE ? "EQUALITY_FALSE" :
    //   es == EQUALITY_TRUE_IN_MODEL ? "EQUALITY_TRUE_IN_MODEL" :
    //   es == EQUALITY_FALSE_IN_MODEL ? "EQUALITY_FALSE_IN_MODEL" :
    //   es == EQUALITY_UNKNOWN ? "EQUALITY_UNKNOWN" :
    //    "Unexpected case") << endl;

    // We need to split on it
    Debug("combineTheories") << "TheoryEngine::combineTheories(): requesting a split " << endl;

    lemma(equality.orNode(equality.notNode()), RULE_INVALID, false, false, false, carePair.theory);

    // This code is supposed to force preference to follow what the theory models already have
    // but it doesn't seem to make a big difference - need to explore more -Clark
    // if (true) {
    //   if (es == EQUALITY_TRUE || es == EQUALITY_TRUE_IN_MODEL) {
    Node e = ensureLiteral(equality);
    d_propEngine->requirePhase(e, true);
    //   }
    //   else if (es == EQUALITY_FALSE_IN_MODEL) {
    //     Node e = ensureLiteral(equality);
    //     d_propEngine->requirePhase(e, false);
    //   }
    // }
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
  unsigned min_priority = 0;
  Node dec;
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
  if (theory::TheoryTraits<THEORY>::hasGetNextDecisionRequest && d_logicInfo.isTheoryEnabled(THEORY)) { \
    unsigned priority; \
    Node n = theoryOf(THEORY)->getNextDecisionRequest( priority ); \
    if(! n.isNull() && ( dec.isNull() || priority<min_priority ) ) { \
      dec = n; \
      min_priority = priority; \
    } \
  }

  // Request decision from each theory using the statement above
  CVC4_FOR_EACH_THEORY;

  return dec;
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

void TheoryEngine::postProcessModel( theory::TheoryModel* m ){
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_logicInfo.isTheoryEnabled(theoryId)) {
      Trace("model-builder-debug") << "  PostProcessModel on theory: " << theoryId << endl;
      d_theoryTable[theoryId]->postProcessModel( m );
    }
  }
}

/* get model */
TheoryModel* TheoryEngine::getModel() {
  return d_curr_model;
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
    newTerm = Rewriter::rewrite(term);
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
  // spendResource();

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

void TheoryEngine::notifyPreprocessedAssertions( std::vector< Node >& assertions ){
  // call all the theories
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST; ++theoryId) {
    if(d_theoryTable[theoryId]) {
      theoryOf(theoryId)->ppNotifyAssertions( assertions );
    }
  }
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

  Trace("theory::assertToTheory") << "TheoryEngine::assertToTheory(" << assertion << ", " << originalAssertion << "," << toTheoryId << ", " << fromTheoryId << ")" << endl;

  Assert(toTheoryId != fromTheoryId);
  if(toTheoryId != THEORY_SAT_SOLVER &&
     ! d_logicInfo.isTheoryEnabled(toTheoryId)) {
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

  // spendResource();

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

  // spendResource();

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
    // We could be propagating a unit-clause lemma. In this case, we need to provide a
    // recipe.
    // TODO: Consider putting this someplace else? This is the only refence to the proof
    // manager in this class.

    PROOF({
        LemmaProofRecipe proofRecipe;
        proofRecipe.addBaseAssertion(literal);

        Node emptyNode;
        LemmaProofRecipe::ProofStep proofStep(theory, emptyNode);
        proofStep.addAssertion(literal);
        proofRecipe.addStep(proofStep);

        ProofManager::getCnfProof()->setProofRecipe(&proofRecipe);
      });

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
  if (var.isConst()) return var;  // FIXME: HACK!!!
  Assert(d_sharedTerms.isShared(var));
  return theoryOf(Theory::theoryOf(var.getType()))->getModelValue(var);
}


Node TheoryEngine::ensureLiteral(TNode n) {
  Debug("ensureLiteral") << "rewriting: " << n << std::endl;
  Node rewritten = Rewriter::rewrite(n);
  Debug("ensureLiteral") << "      got: " << rewritten << std::endl;
  Node preprocessed = preprocess(rewritten);
  Debug("ensureLiteral") << "preprocessed: " << preprocessed << std::endl;
  d_propEngine->ensureLiteral(preprocessed);
  return preprocessed;
}


void TheoryEngine::printInstantiations( std::ostream& out ) {
  if( d_quantEngine ){
    d_quantEngine->printInstantiations( out );
  }else{
    out << "Internal error : instantiations not available when quantifiers are not present." << std::endl;
  }
}

void TheoryEngine::printSynthSolution( std::ostream& out ) {
  if( d_quantEngine ){
    d_quantEngine->printSynthSolution( out );
  }else{
    out << "Internal error : synth solution not available when quantifiers are not present." << std::endl;
  }
}

void TheoryEngine::getInstantiatedQuantifiedFormulas( std::vector< Node >& qs ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiatedQuantifiedFormulas( qs );
  }else{
    Assert( false );
  }
}

void TheoryEngine::getInstantiations( Node q, std::vector< Node >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiations( q, insts );
  }else{
    Assert( false );
  }
}

void TheoryEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiationTermVectors( q, tvecs );
  }else{
    Assert( false );
  }
}

void TheoryEngine::getInstantiations( std::map< Node, std::vector< Node > >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiations( insts );
  }else{
    Assert( false );
  }
}

void TheoryEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiationTermVectors( insts );
  }else{
    Assert( false );
  }
}

Node TheoryEngine::getInstantiatedConjunction( Node q ) {
  if( d_quantEngine ){
    return d_quantEngine->getInstantiatedConjunction( q );
  }else{
    Assert( false );
    return Node::null();
  }
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

Node TheoryEngine::getExplanationAndRecipe(TNode node, LemmaProofRecipe* proofRecipe) {
  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << "): current propagation index = " << d_propagationMapTimestamp << endl;

  bool polarity = node.getKind() != kind::NOT;
  TNode atom = polarity ? node : node[0];

  // If we're not in shared mode, explanations are simple
  if (!d_logicInfo.isSharingEnabled()) {
    Debug("theory::explain") << "TheoryEngine::getExplanation: sharing is NOT enabled. "
                             << " Responsible theory is: "
                             << theoryOf(atom)->getId() << std::endl;

    Node explanation = theoryOf(atom)->explain(node);
    Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << endl;
    PROOF({
        if(proofRecipe) {
          Node emptyNode;
          LemmaProofRecipe::ProofStep proofStep(theoryOf(atom)->getId(), emptyNode);
          proofStep.addAssertion(node);
          proofRecipe->addBaseAssertion(node);

          if (explanation.getKind() == kind::AND) {
            // If the explanation is a conjunction, the recipe for the corresponding lemma is
            // the negation of its conjuncts.
            Node flat = flattenAnd(explanation);
            for (unsigned i = 0; i < flat.getNumChildren(); ++i) {
              if (flat[i].isConst() && flat[i].getConst<bool>()) {
                ++ i;
                continue;
              }
              if (flat[i].getKind() == kind::NOT &&
                  flat[i][0].isConst() && !flat[i][0].getConst<bool>()) {
                ++ i;
                continue;
              }
              Debug("theory::explain") << "TheoryEngine::getExplanationAndRecipe: adding recipe assertion: "
                                       << flat[i].negate() << std::endl;
              proofStep.addAssertion(flat[i].negate());
              proofRecipe->addBaseAssertion(flat[i].negate());
            }
          } else {
            // The recipe for proving it is by negating it. "True" is not an acceptable reason.
            if (!((explanation.isConst() && explanation.getConst<bool>()) ||
                  (explanation.getKind() == kind::NOT &&
                   explanation[0].isConst() && !explanation[0].getConst<bool>()))) {
              proofStep.addAssertion(explanation.negate());
              proofRecipe->addBaseAssertion(explanation.negate());
            }
          }

          proofRecipe->addStep(proofStep);
        }
      });

    return explanation;
  }

  Debug("theory::explain") << "TheoryEngine::getExplanation: sharing IS enabled" << std::endl;

  // Initial thing to explain
  NodeTheoryPair toExplain(node, THEORY_SAT_SOLVER, d_propagationMapTimestamp);
  Assert(d_propagationMap.find(toExplain) != d_propagationMap.end());

  NodeTheoryPair nodeExplainerPair = d_propagationMap[toExplain];
  Debug("theory::explain") << "TheoryEngine::getExplanation: explainer for node "
                           << nodeExplainerPair.node
                           << " is theory: " << nodeExplainerPair.theory << std::endl;
  TheoryId explainer = nodeExplainerPair.theory;

  // Create the workplace for explanations
  std::vector<NodeTheoryPair> explanationVector;
  explanationVector.push_back(d_propagationMap[toExplain]);
  // Process the explanation
  if (proofRecipe) {
    Node emptyNode;
    LemmaProofRecipe::ProofStep proofStep(explainer, emptyNode);
    proofStep.addAssertion(node);
    proofRecipe->addStep(proofStep);
    proofRecipe->addBaseAssertion(node);
  }

  getExplanation(explanationVector, proofRecipe);
  Node explanation = mkExplanation(explanationVector);

  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => " << explanation << endl;

  return explanation;
}

Node TheoryEngine::getExplanation(TNode node) {
  LemmaProofRecipe *dontCareRecipe = NULL;
  return getExplanationAndRecipe(node, dontCareRecipe);
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

theory::LemmaStatus TheoryEngine::lemma(TNode node,
                                        ProofRule rule,
                                        bool negated,
                                        bool removable,
                                        bool preprocess,
                                        theory::TheoryId atomsTo) {
  // For resource-limiting (also does a time check).
  // spendResource();

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
  if(d_channels->getLemmaOutputChannel() != NULL) {
    d_channels->getLemmaOutputChannel()->notifyNewLemma(node.toExpr());
  }

  std::vector<Node> additionalLemmas;
  IteSkolemMap iteSkolemMap;

  // Run theory preprocessing, maybe
  Node ppNode = preprocess ? this->preprocess(node) : Node(node);

  // Remove the ITEs
  additionalLemmas.push_back(ppNode);
  d_iteRemover.run(additionalLemmas, iteSkolemMap);
  additionalLemmas[0] = theory::Rewriter::rewrite(additionalLemmas[0]);

  if(Debug.isOn("lemma-ites")) {
    Debug("lemma-ites") << "removed ITEs from lemma: " << ppNode << endl;
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
  d_propEngine->assertLemma(additionalLemmas[0], negated, removable, rule, node);
  for (unsigned i = 1; i < additionalLemmas.size(); ++ i) {
    additionalLemmas[i] = theory::Rewriter::rewrite(additionalLemmas[i]);
    d_propEngine->assertLemma(additionalLemmas[i], false, removable, rule, node);
  }

  // WARNING: Below this point don't assume additionalLemmas[0] to be not negated.
  if(negated) {
    additionalLemmas[0] = additionalLemmas[0].notNode();
    negated = false;
  }

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

  LemmaProofRecipe* proofRecipe = NULL;
  PROOF({
      proofRecipe = new LemmaProofRecipe;
      Node emptyNode;
      LemmaProofRecipe::ProofStep proofStep(theoryId, emptyNode);

      if (conflict.getKind() == kind::AND) {
        for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
          proofStep.addAssertion(conflict[i].negate());
        }
      } else {
        proofStep.addAssertion(conflict.negate());
      }

      proofRecipe->addStep(proofStep);
    });

  // In the multiple-theories case, we need to reconstruct the conflict
  if (d_logicInfo.isSharingEnabled()) {
    // Create the workplace for explanations
    std::vector<NodeTheoryPair> explanationVector;
    explanationVector.push_back(NodeTheoryPair(conflict, theoryId, d_propagationMapTimestamp));

    // Process the explanation
    getExplanation(explanationVector, proofRecipe);
    PROOF(ProofManager::getCnfProof()->setProofRecipe(proofRecipe));
    Node fullConflict = mkExplanation(explanationVector);
    Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << "): full = " << fullConflict << endl;
    Assert(properConflict(fullConflict));
    lemma(fullConflict, RULE_CONFLICT, true, true, false, THEORY_LAST);

  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    PROOF({
        if (conflict.getKind() == kind::AND) {
          // If the conflict is a conjunction, the corresponding lemma is derived by negating
          // its conjuncts.
          for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
            if (conflict[i].isConst() && conflict[i].getConst<bool>()) {
              ++ i;
              continue;
            }
            if (conflict[i].getKind() == kind::NOT &&
                conflict[i][0].isConst() && !conflict[i][0].getConst<bool>()) {
              ++ i;
              continue;
            }
            proofRecipe->getStep(0)->addAssertion(conflict[i].negate());
            proofRecipe->addBaseAssertion(conflict[i].negate());
          }
        } else {
          proofRecipe->getStep(0)->addAssertion(conflict.negate());
          proofRecipe->addBaseAssertion(conflict.negate());
        }

        ProofManager::getCnfProof()->setProofRecipe(proofRecipe);
      });

    lemma(conflict, RULE_CONFLICT, true, true, false, THEORY_LAST);
  }

  PROOF({
      delete proofRecipe;
      proofRecipe = NULL;
    });
}

void TheoryEngine::staticInitializeBVOptions(const std::vector<Node>& assertions) {
  bool useSlicer = true;
  if (options::bitvectorEqualitySlicer() == bv::BITVECTOR_SLICER_ON) {
    if (options::incrementalSolving())
      throw ModalException("Slicer does not currently support incremental mode. Use --bv-eq-slicer=off");
    if (options::produceModels())
      throw ModalException("Slicer does not currently support model generation. Use --bv-eq-slicer=off");
    useSlicer = true;

  } else if (options::bitvectorEqualitySlicer() == bv::BITVECTOR_SLICER_OFF) {
    return;

  } else if (options::bitvectorEqualitySlicer() == bv::BITVECTOR_SLICER_AUTO) {
    if (options::incrementalSolving() ||
        options::produceModels())
      return;

    useSlicer = true;
    bv::utils::TNodeBoolMap cache;
    for (unsigned i = 0; i < assertions.size(); ++i) {
      useSlicer = useSlicer && bv::utils::isCoreTerm(assertions[i], cache);
    }
  }

  if (useSlicer) {
    bv::TheoryBV* bv_theory = (bv::TheoryBV*)d_theoryTable[THEORY_BV];
    bv_theory->enableCoreTheorySlicer();
  }

}

void TheoryEngine::ppBvToBool(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  d_bvToBoolPreprocessor.liftBvToBool(assertions, new_assertions);
}

bool  TheoryEngine::ppBvAbstraction(const std::vector<Node>& assertions, std::vector<Node>& new_assertions) {
  bv::TheoryBV* bv_theory = (bv::TheoryBV*)d_theoryTable[THEORY_BV];
  return bv_theory->applyAbstraction(assertions, new_assertions);
}

void TheoryEngine::mkAckermanizationAsssertions(std::vector<Node>& assertions) {
  bv::TheoryBV* bv_theory = (bv::TheoryBV*)d_theoryTable[THEORY_BV];
  bv_theory->mkAckermanizationAsssertions(assertions);
}

Node TheoryEngine::ppSimpITE(TNode assertion)
{
  if (!d_iteRemover.containsTermITE(assertion)) {
    return assertion;
  } else {
    Node result = d_iteUtilities->simpITE(assertion);
    Node res_rewritten = Rewriter::rewrite(result);

    if(options::simplifyWithCareEnabled()){
      Chat() << "starting simplifyWithCare()" << endl;
      Node postSimpWithCare = d_iteUtilities->simplifyWithCare(res_rewritten);
      Chat() << "ending simplifyWithCare()"
             << " post simplifyWithCare()" << postSimpWithCare.getId() << endl;
      result = Rewriter::rewrite(postSimpWithCare);
    } else {
      result = res_rewritten;
    }
    return result;
  }
}

bool TheoryEngine::donePPSimpITE(std::vector<Node>& assertions){
  // This pass does not support dependency tracking yet
  // (learns substitutions from all assertions so just
  // adding addDependence is not enough)
  if (options::unsatCores() || options::fewerPreprocessingHoles()) {
    return true;
  }
  bool result = true;
  bool simpDidALotOfWork = d_iteUtilities->simpIteDidALotOfWorkHeuristic();
  if(simpDidALotOfWork){
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
        Rewriter::clearCaches();
        d_iteRemover.garbageCollect();
        nm->reclaimZombiesUntil(options::zombieHuntThreshold());
        Chat() << "....node manager contains " << nm->poolSize() << " nodes after cleanup" << endl;
      }
    }
  }

  // Do theory specific preprocessing passes
  if(d_logicInfo.isTheoryEnabled(theory::THEORY_ARITH)
     && !options::incrementalSolving() ){
    if(!simpDidALotOfWork){
      ContainsTermITEVisitor& contains = *d_iteRemover.getContainsVisitor();
      arith::ArithIteUtils aiteu(contains, d_userContext, getModel());
      bool anyItes = false;
      for(size_t i = 0;  i < assertions.size(); ++i){
        Node curr = assertions[i];
        if(contains.containsTermITE(curr)){
          anyItes = true;
          Node res = aiteu.reduceVariablesInItes(curr);
          Debug("arith::ite::red") << "@ " << i << " ... " << curr << endl << "   ->" << res << endl;
          if(curr != res){
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            assertions[i] = Rewriter::rewrite(more);
          }
        }
      }
      if(!anyItes){
        unsigned prevSubCount = aiteu.getSubCount();
        aiteu.learnSubstitutions(assertions);
        if(prevSubCount < aiteu.getSubCount()){
          d_arithSubstitutionsAdded += aiteu.getSubCount() - prevSubCount;
          bool anySuccess = false;
          for(size_t i = 0, N =  assertions.size();  i < N; ++i){
            Node curr = assertions[i];
            Node next = Rewriter::rewrite(aiteu.applySubstitutions(curr));
            Node res = aiteu.reduceVariablesInItes(next);
            Debug("arith::ite::red") << "@ " << i << " ... " << next << endl << "   ->" << res << endl;
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            if(more != next){
              anySuccess = true;
              break;
            }
          }
          for(size_t i = 0, N =  assertions.size();  anySuccess && i < N; ++i){
            Node curr = assertions[i];
            Node next = Rewriter::rewrite(aiteu.applySubstitutions(curr));
            Node res = aiteu.reduceVariablesInItes(next);
            Debug("arith::ite::red") << "@ " << i << " ... " << next << endl << "   ->" << res << endl;
            Node more = aiteu.reduceConstantIteByGCD(res);
            Debug("arith::ite::red") << "  gcd->" << more << endl;
            assertions[i] = Rewriter::rewrite(more);
          }
        }
      }
    }
  }
  return result;
}

void TheoryEngine::getExplanation(std::vector<NodeTheoryPair>& explanationVector, LemmaProofRecipe* proofRecipe) {
  Assert(explanationVector.size() > 0);

  unsigned i = 0; // Index of the current literal we are processing
  unsigned j = 0; // Index of the last literal we are keeping

  std::set<Node> inputAssertions;
  PROOF(inputAssertions = proofRecipe->getStep(0)->getAssertions(););

  while (i < explanationVector.size()) {
    // Get the current literal to explain
    NodeTheoryPair toExplain = explanationVector[i];

    Debug("theory::explain") << "[i=" << i << "] TheoryEngine::explain(): processing [" << toExplain.timestamp << "] " << toExplain.node << " sent from " << toExplain.theory << endl;


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
      Debug("theory::explain") << "\tLiteral came from THEORY_SAT_SOLVER. Kepping it." << endl;
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
      Debug("theory::explain") << "\tTerm was propagated by another theory (theory = "
                               << theoryOf((*find).second.theory)->getId() << ")" << std::endl;
      // There is some propagation, check if its a timely one
      if ((*find).second.timestamp < toExplain.timestamp) {
        Debug("theory::explain") << "\tRelevant timetsamp, pushing "
                                 << (*find).second.node << "to index = " << explanationVector.size() << std::endl;
        explanationVector.push_back((*find).second);
        ++i;

        PROOF({
            if (toExplain.node != (*find).second.node) {
              Debug("pf::explain") << "TheoryEngine::getExplanation: Rewrite alert! toAssert = " << toExplain.node
                                   << ", toExplain = " << (*find).second.node << std::endl;

              if (proofRecipe) {
                proofRecipe->addRewriteRule(toExplain.node, (*find).second.node);
              }
            }
          })

        continue;
      }
    }

    // It was produced by the theory, so ask for an explanation
    Node explanation;
    if (toExplain.theory == THEORY_BUILTIN) {
      explanation = d_sharedTerms.explain(toExplain.node);
      Debug("theory::explain") << "\tTerm was propagated by THEORY_BUILTIN. Explanation: " << explanation << std::endl;
    } else {
      explanation = theoryOf(toExplain.theory)->explain(toExplain.node);
      Debug("theory::explain") << "\tTerm was propagated by owner theory: "
                               << theoryOf(toExplain.theory)->getId()
                               << ". Explanation: " << explanation << std::endl;
    }

    Debug("theory::explain") << "TheoryEngine::explain(): got explanation " << explanation << " got from " << toExplain.theory << endl;
    Assert(explanation != toExplain.node, "wasn't sent to you, so why are you explaining it trivially");
    // Mark the explanation
    NodeTheoryPair newExplain(explanation, toExplain.theory, toExplain.timestamp);
    explanationVector.push_back(newExplain);

    ++ i;

    PROOF({
        if (proofRecipe) {
          // If we're expanding the target node of the explanation (this is the first expansion...),
          // we don't want to add it as a separate proof step. It is already part of the assertions.
          if (inputAssertions.find(toExplain.node) == inputAssertions.end()) {
            LemmaProofRecipe::ProofStep proofStep(toExplain.theory, toExplain.node);
            if (explanation.getKind() == kind::AND) {
              Node flat = flattenAnd(explanation);
              for (unsigned k = 0; k < flat.getNumChildren(); ++ k) {
                // If a true constant or a negation of a false constant we can ignore it
                if (! ((flat[k].isConst() && flat[k].getConst<bool>()) ||
                       (flat[k].getKind() == kind::NOT && flat[k][0].isConst() && !flat[k][0].getConst<bool>()))) {
                  proofStep.addAssertion(flat[k].negate());
                }
              }
            } else {
             if (! ((explanation.isConst() && explanation.getConst<bool>()) ||
                    (explanation.getKind() == kind::NOT && explanation[0].isConst() && !explanation[0].getConst<bool>()))) {
               proofStep.addAssertion(explanation.negate());
             }
            }
            proofRecipe->addStep(proofStep);
          }
        }
      });
  }

  // Keep only the relevant literals
  explanationVector.resize(j);

  PROOF({
      if (proofRecipe) {
        // The remaining literals are the base of the proof
        for (unsigned k = 0; k < explanationVector.size(); ++k) {
          proofRecipe->addBaseAssertion(explanationVector[k].node.negate());
        }
      }
    });
}

void TheoryEngine::ppUnconstrainedSimp(vector<Node>& assertions)
{
  d_unconstrainedSimp->processAssertions(assertions);
}


void TheoryEngine::setUserAttribute(const std::string& attr, Node n, std::vector<Node>& node_values, std::string str_value) {
  Trace("te-attr") << "set user attribute " << attr << " " << n << endl;
  if( d_attr_handle.find( attr )!=d_attr_handle.end() ){
    for( size_t i=0; i<d_attr_handle[attr].size(); i++ ){
      d_attr_handle[attr][i]->setUserAttribute(attr, n, node_values, str_value);
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

std::pair<bool, Node> TheoryEngine::entailmentCheck(theory::TheoryOfMode mode, TNode lit, const EntailmentCheckParameters* params, EntailmentCheckSideEffects* seffects) {
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  theory::TheoryId tid = theory::Theory::theoryOf(mode, atom);
  theory::Theory* th = theoryOf(tid);

  Assert(th != NULL);
  Assert(params == NULL || tid == params->getTheoryId());
  Assert(seffects == NULL || tid == seffects->getTheoryId());

  return th->entailmentCheck(lit, params, seffects);
}

void TheoryEngine::spendResource(unsigned ammount) {
  d_resourceManager->spendResource(ammount);
}

void TheoryEngine::enableTheoryAlternative(const std::string& name){
  Debug("TheoryEngine::enableTheoryAlternative")
      << "TheoryEngine::enableTheoryAlternative(" << name << ")" << std::endl;

  d_theoryAlternatives.insert(name);
}

bool TheoryEngine::useTheoryAlternative(const std::string& name) {
  return d_theoryAlternatives.find(name) != d_theoryAlternatives.end();
}


TheoryEngine::Statistics::Statistics(theory::TheoryId theory):
    conflicts(mkName("theory<", theory, ">::conflicts"), 0),
    propagations(mkName("theory<", theory, ">::propagations"), 0),
    lemmas(mkName("theory<", theory, ">::lemmas"), 0),
    requirePhase(mkName("theory<", theory, ">::requirePhase"), 0),
    flipDecision(mkName("theory<", theory, ">::flipDecision"), 0),
    restartDemands(mkName("theory<", theory, ">::restartDemands"), 0)
{
  smtStatisticsRegistry()->registerStat(&conflicts);
  smtStatisticsRegistry()->registerStat(&propagations);
  smtStatisticsRegistry()->registerStat(&lemmas);
  smtStatisticsRegistry()->registerStat(&requirePhase);
  smtStatisticsRegistry()->registerStat(&flipDecision);
  smtStatisticsRegistry()->registerStat(&restartDemands);
}

TheoryEngine::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&conflicts);
  smtStatisticsRegistry()->unregisterStat(&propagations);
  smtStatisticsRegistry()->unregisterStat(&lemmas);
  smtStatisticsRegistry()->unregisterStat(&requirePhase);
  smtStatisticsRegistry()->unregisterStat(&flipDecision);
  smtStatisticsRegistry()->unregisterStat(&restartDemands);
}

}/* CVC4 namespace */
