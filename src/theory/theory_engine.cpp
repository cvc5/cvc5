/*********************                                                        */
/*! \file theory_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include "base/map_util.h"
#include "decision/decision_engine.h"
#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_visitor.h"
#include "options/bv_options.h"
#include "options/options.h"
#include "options/quantifiers_options.h"
#include "options/theory_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/logic_exception.h"
#include "smt/term_formula_removal.h"
#include "theory/arith/arith_ite_utils.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/care_graph.h"
#include "theory/combination_care_graph.h"
#include "theory/decision_manager.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers_engine.h"
#include "theory/relevance_manager.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_id.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "theory/uf/equality_engine.h"
#include "util/resource_manager.h"

using namespace std;

using namespace CVC4::preprocessing;
using namespace CVC4::theory;

namespace CVC4 {

/* -------------------------------------------------------------------------- */

namespace theory {

/**
 * IMPORTANT: The order of the theories is important. For example, strings
 *            depends on arith, quantifiers needs to come as the very last.
 *            Do not change this order.
 */

#define CVC4_FOR_EACH_THEORY                                     \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_BUILTIN)   \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_BOOL)      \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_UF)        \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_ARITH)     \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_BV)        \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_FP)        \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_ARRAYS)    \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_DATATYPES) \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_SEP)       \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_SETS)      \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_STRINGS)   \
  CVC4_FOR_EACH_THEORY_STATEMENT(CVC4::theory::THEORY_QUANTIFIERS)

}  // namespace theory

/* -------------------------------------------------------------------------- */

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

/**
 * Compute the string for a given theory id. In this module, we use
 * THEORY_SAT_SOLVER as an id, which is not a normal id but maps to
 * THEORY_LAST. Thus, we need our own string conversion here.
 *
 * @param id The theory id
 * @return The string corresponding to the theory id
 */
std::string getTheoryString(theory::TheoryId id)
{
  if (id == theory::THEORY_SAT_SOLVER)
  {
    return "THEORY_SAT_SOLVER";
  }
  else
  {
    std::stringstream ss;
    ss << id;
    return ss.str();
  }
}

void TheoryEngine::finishInit() {
  // NOTE: This seems to be required since
  // theory::TheoryTraits<THEORY>::isParametric cannot be accessed without
  // using the CVC4_FOR_EACH_THEORY_STATEMENT macro. -AJR
  std::vector<theory::Theory*> paraTheories;
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY)   \
  if (theory::TheoryTraits<THEORY>::isParametric \
      && d_logicInfo.isTheoryEnabled(THEORY))    \
  {                                              \
    paraTheories.push_back(theoryOf(THEORY));    \
  }
  // Collect the parametric theories, which are given to the theory combination
  // manager below
  CVC4_FOR_EACH_THEORY;

  // Initialize the theory combination architecture
  if (options::tcMode() == options::TcMode::CARE_GRAPH)
  {
    d_tc.reset(new CombinationCareGraph(*this, paraTheories, d_pnm));
  }
  else
  {
    Unimplemented() << "TheoryEngine::finishInit: theory combination mode "
                    << options::tcMode() << " not supported";
  }
  // create the relevance filter if any option requires it
  if (options::relevanceFilter())
  {
    d_relManager.reset(
        new RelevanceManager(d_userContext, theory::Valuation(this)));
  }

  // initialize the quantifiers engine
  if (d_logicInfo.isQuantified())
  {
    // initialize the quantifiers engine
    d_quantEngine =
        new QuantifiersEngine(d_context, d_userContext, this, d_pnm);
  }
  // initialize the theory combination manager, which decides and allocates the
  // equality engines to use for all theories.
  d_tc->finishInit();

  // set the core equality engine on quantifiers engine
  if (d_logicInfo.isQuantified())
  {
    d_quantEngine->setMasterEqualityEngine(d_tc->getCoreEqualityEngine());
  }

  // finish initializing the theories by linking them with the appropriate
  // utilities and then calling their finishInit method.
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST; ++ theoryId) {
    Theory* t = d_theoryTable[theoryId];
    if (t == nullptr)
    {
      continue;
    }
    // setup the pointers to the utilities
    const EeTheoryInfo* eeti = d_tc->getEeTheoryInfo(theoryId);
    Assert(eeti != nullptr);
    // the theory's official equality engine is the one specified by the
    // equality engine manager
    t->setEqualityEngine(eeti->d_usedEe);
    // set the quantifiers engine
    t->setQuantifiersEngine(d_quantEngine);
    // set the decision manager for the theory
    t->setDecisionManager(d_decManager.get());
    // finish initializing the theory
    t->finishInit();
  }
}

TheoryEngine::TheoryEngine(context::Context* context,
                           context::UserContext* userContext,
                           ResourceManager* rm,
                           RemoveTermFormulas& iteRemover,
                           const LogicInfo& logicInfo)
    : d_propEngine(nullptr),
      d_context(context),
      d_userContext(userContext),
      d_logicInfo(logicInfo),
      d_pnm(nullptr),
      d_sharedTerms(this, context),
      d_tc(nullptr),
      d_quantEngine(nullptr),
      d_decManager(new DecisionManager(userContext)),
      d_relManager(nullptr),
      d_preRegistrationVisitor(this, context),
      d_sharedTermsVisitor(d_sharedTerms),
      d_eager_model_building(false),
      d_possiblePropagations(context),
      d_hasPropagated(context),
      d_inConflict(context, false),
      d_inSatMode(false),
      d_hasShutDown(false),
      d_incomplete(context, false),
      d_propagationMap(context),
      d_propagationMapTimestamp(context, 0),
      d_propagatedLiterals(context),
      d_propagatedLiteralsIndex(context, 0),
      d_atomRequests(context),
      d_tpp(*this, iteRemover),
      d_combineTheoriesTime("TheoryEngine::combineTheoriesTime"),
      d_true(),
      d_false(),
      d_interrupted(false),
      d_resourceManager(rm),
      d_inPreregister(false),
      d_factsAsserted(context, false),
      d_attr_handle(),
      d_arithSubstitutionsAdded("theory::arith::zzz::arith::substitutions", 0)
{
  for(TheoryId theoryId = theory::THEORY_FIRST; theoryId != theory::THEORY_LAST;
      ++ theoryId)
  {
    d_theoryTable[theoryId] = NULL;
    d_theoryOut[theoryId] = NULL;
  }

  smtStatisticsRegistry()->registerStat(&d_combineTheoriesTime);
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);

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

  delete d_quantEngine;

  smtStatisticsRegistry()->unregisterStat(&d_combineTheoriesTime);
  smtStatisticsRegistry()->unregisterStat(&d_arithSubstitutionsAdded);
}

void TheoryEngine::interrupt() { d_interrupted = true; }
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

      // the atom should not have free variables
      Debug("theory") << "TheoryEngine::preRegister: " << preprocessed
                      << std::endl;
      Assert(!expr::hasFreeVar(preprocessed));

      // Pre-register the terms in the atom
      theory::TheoryIdSet theories = NodeVisitor<PreRegisterVisitor>::run(
          d_preRegistrationVisitor, preprocessed);
      theories = TheoryIdSetUtil::setRemove(THEORY_BOOL, theories);
      // Remove the top theory, if any more that means multiple theories were
      // involved
      bool multipleTheories =
          TheoryIdSetUtil::setRemove(Theory::theoryOf(preprocessed), theories);
      if (Configuration::isAssertionBuild())
      {
        TheoryId i;
        // This should never throw an exception, since theories should be
        // guaranteed to be initialized.
        // These checks don't work with finite model finding, because it
        // uses Rational constants to represent cardinality constraints,
        // even though arithmetic isn't actually involved.
        if (!options::finiteModelFind())
        {
          while ((i = TheoryIdSetUtil::setPop(theories)) != THEORY_LAST)
          {
            if (!d_logicInfo.isTheoryEnabled(i))
            {
              LogicInfo newLogicInfo = d_logicInfo.getUnlockedCopy();
              newLogicInfo.enableTheory(i);
              newLogicInfo.lock();
              std::stringstream ss;
              ss << "The logic was specified as " << d_logicInfo.getLogicString()
                << ", which doesn't include " << i
                << ", but found a term in that theory." << std::endl
                << "You might want to extend your logic to "
                << newLogicInfo.getLogicString() << std::endl;
              throw LogicException(ss.str());
            }
          }
        }
      }
      if (multipleTheories) {
        // Collect the shared terms if there are multiple theories
        NodeVisitor<SharedTermsVisitor>::run(d_sharedTermsVisitor,
                                             preprocessed);
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
        {
          context::CDList<Assertion>::const_iterator it = theory->facts_begin(),
                                                     it_end =
                                                         theory->facts_end();
          for (unsigned i = 0; it != it_end; ++it, ++i)
          {
            if ((*it).d_isPreregistered)
            {
              Trace(tag) << "[" << i << "]: ";
            }
            else
            {
              Trace(tag) << "(" << i << "): ";
            }
            Trace(tag) << (*it).d_assertion << endl;
          }
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
          Node assertionNode = (*it).d_assertion;
          // Purify all the terms

          if ((*it).d_isPreregistered)
          {
            Dump(tag) << CommentCommand("Preregistered");
          }
          else
          {
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
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY)                      \
  if (theory::TheoryTraits<THEORY>::hasCheck                        \
      && d_logicInfo.isTheoryEnabled(THEORY))                       \
  {                                                                 \
    theoryOf(THEORY)->check(effort);                                \
    if (d_inConflict)                                               \
    {                                                               \
      Debug("conflict") << THEORY << " in conflict. " << std::endl; \
      break;                                                        \
    }                                                               \
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
      // Reset round for the relevance manager, which notice only sets a flag
      // to indicate that its information must be recomputed.
      if (d_relManager != nullptr)
      {
        d_relManager->resetRound();
      }
      d_tc->resetRound();
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
        {
          TimerStat::CodeTimer combineTheoriesTimer(d_combineTheoriesTime);
          d_tc->combineTheories();
        }
        if(d_logicInfo.isQuantified()){
          d_quantEngine->notifyCombineTheories();
        }
      }
    }

    // Must consult quantifiers theory for last call to ensure sat, or otherwise add a lemma
    if( Theory::fullEffort(effort) && ! d_inConflict && ! needCheck() ) {
      Trace("theory::assertions-model") << endl;
      if (Trace.isOn("theory::assertions-model")) {
        printAssertions("theory::assertions-model");
      }
      // reset the model in the combination engine
      d_tc->resetModel();
      //checks for theories requiring the model go at last call
      for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
        if( theoryId!=THEORY_QUANTIFIERS ){
          Theory* theory = d_theoryTable[theoryId];
          if (theory && d_logicInfo.isTheoryEnabled(theoryId)) {
            if( theory->needsCheckLastEffort() ){
              if (!d_tc->buildModel())
              {
                break;
              }
              theory->check(Theory::EFFORT_LAST_CALL);
            }
          }
        }
      }
      if (!d_inConflict)
      {
        if(d_logicInfo.isQuantified()) {
          // quantifiers engine must check at last call effort
          d_quantEngine->check(Theory::EFFORT_LAST_CALL);
        }
      }
      if (!d_inConflict && !needCheck())
      {
        // If d_eager_model_building is false, then we only mark that we
        // are in "SAT mode". We build the model later only if the user asks
        // for it via getBuiltModel.
        d_inSatMode = true;
        if (d_eager_model_building)
        {
          d_tc->buildModel();
        }
      }
    }

    Debug("theory") << "TheoryEngine::check(" << effort << "): done, we are " << (d_inConflict ? "unsat" : "sat") << (d_lemmasAdded ? " with new lemmas" : " with no new lemmas");
    Debug("theory") << ", need check = " << (needCheck() ? "YES" : "NO") << endl;

    if( Theory::fullEffort(effort) && !d_inConflict && !needCheck()) {
      // Do post-processing of model from the theories (e.g. used for THEORY_SEP
      // to construct heap model)
      d_tc->postProcessModel(d_incomplete.get());
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

void TheoryEngine::propagate(Theory::Effort effort)
{
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

Node TheoryEngine::getNextDecisionRequest()
{
  return d_decManager->getNextDecisionRequest();
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

TheoryModel* TheoryEngine::getModel()
{
  Assert(d_tc != nullptr);
  TheoryModel* m = d_tc->getModel();
  Assert(m != nullptr);
  return m;
}

TheoryModel* TheoryEngine::getBuiltModel()
{
  Assert(d_tc != nullptr);
  // If this method was called, we should be in SAT mode, and produceModels
  // should be true.
  AlwaysAssert(options::produceModels());
  if (!d_inSatMode)
  {
    // not available, perhaps due to interuption.
    return nullptr;
  }
  // must build model at this point
  if (!d_tc->buildModel())
  {
    return nullptr;
  }
  return d_tc->getModel();
}

bool TheoryEngine::buildModel()
{
  Assert(d_tc != nullptr);
  return d_tc->buildModel();
}

bool TheoryEngine::getSynthSolutions(
    std::map<Node, std::map<Node, Node>>& sol_map)
{
  if (d_quantEngine)
  {
    return d_quantEngine->getSynthSolutions(sol_map);
  }
  // we are not in a quantified logic, there is no synthesis solution
  return false;
}

bool TheoryEngine::presolve() {
  // Reset the interrupt flag
  d_interrupted = false;

  // Reset the decision manager. This clears its decision strategies that are
  // no longer valid in this user context.
  d_decManager->presolve();

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
  // no longer in SAT mode
  d_inSatMode = false;
  // Reset the interrupt flag
  d_interrupted = false;
  bool CVC4_UNUSED wasInConflict = d_inConflict;

  try {
    // Definition of the statement that is to be run by every theory
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY)    \
  if (theory::TheoryTraits<THEORY>::hasPostsolve) \
  {                                               \
    theoryOf(THEORY)->postsolve();                \
    Assert(!d_inConflict || wasInConflict)        \
        << "conflict raised during postsolve()";  \
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

bool TheoryEngine::isRelevant(Node lit) const
{
  if (d_relManager != nullptr)
  {
    return d_relManager->isRelevant(lit);
  }
  // otherwise must assume its relevant
  return true;
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

  d_tpp.clearCache();
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

void TheoryEngine::preprocessStart() { d_tpp.clearCache(); }

Node TheoryEngine::preprocess(TNode assertion) {
  TrustNode trn = d_tpp.theoryPreprocess(assertion);
  if (trn.isNull())
  {
    // no change
    return assertion;
  }
  return trn.getNode();
}

void TheoryEngine::notifyPreprocessedAssertions(
    const std::vector<Node>& assertions) {
  // call all the theories
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId) {
    if (d_theoryTable[theoryId]) {
      theoryOf(theoryId)->ppNotifyAssertions(assertions);
    }
  }
  if (d_relManager != nullptr)
  {
    d_relManager->notifyPreprocessedAssertions(assertions);
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
          Trace("dtview::conflict")
              << ":THEORY-CONFLICT: " << assertion << std::endl;
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
    Assert(atom.getKind() == kind::EQUAL)
        << "atom should be an EQUALity, not `" << atom << "'";
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
        Trace("theory::propagate")
            << "TheoryEngine::assertToTheory(" << assertion << ", "
            << toTheoryId << ", " << fromTheoryId << "): conflict (sharing)"
            << endl;
        Trace("dtview::conflict")
            << ":THEORY-CONFLICT: " << assertion << std::endl;
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
        theory::TheoryIdSet theories =
            d_sharedTerms.getTheoriesToNotify(atom, term);
        for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++ id) {
          if (TheoryIdSetUtil::setContains(id, theories))
          {
            theoryOf(id)->addSharedTerm(term);
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
      // Shared terms manager will assert to interested theories directly, as
      // the terms become shared
      assertToTheory(literal, literal, /* to */ THEORY_BUILTIN, /* from */ THEORY_SAT_SOLVER);

      // Now, let's check for any atom triggers from lemmas
      AtomRequests::atom_iterator it = d_atomRequests.getAtomIterator(atom);
      while (!it.done()) {
        const AtomRequests::Request& request = it.get();
        Node toAssert =
            polarity ? (Node)request.d_atom : request.d_atom.notNode();
        Debug("theory::atoms") << "TheoryEngine::assertFact(" << literal << "): sending requested " << toAssert << endl;
        assertToTheory(
            toAssert, literal, request.d_toTheory, THEORY_SAT_SOLVER);
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

  Trace("dtview::prop") << std::string(d_context->getLevel(), ' ')
                        << ":THEORY-PROP: " << literal << endl;

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
    // Just send off to the SAT solver
    Assert(d_propEngine->isSatLiteral(literal));
    assertToTheory(literal, literal, /* to */ THEORY_SAT_SOLVER, /* from */ theory);
  }

  return !d_inConflict;
}

const LogicInfo& TheoryEngine::getLogicInfo() const { return d_logicInfo; }

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
  if (var.isConst())
  {
    // the model value of a constant must be itself
    return var;
  }
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
    Assert(false);
  }
}

void TheoryEngine::printSynthSolution( std::ostream& out ) {
  if( d_quantEngine ){
    d_quantEngine->printSynthSolution( out );
  }else{
    out << "Internal error : synth solution not available when quantifiers are not present." << std::endl;
    Assert(false);
  }
}

void TheoryEngine::getInstantiatedQuantifiedFormulas( std::vector< Node >& qs ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiatedQuantifiedFormulas( qs );
  }else{
    Assert(false);
  }
}

void TheoryEngine::getInstantiations( Node q, std::vector< Node >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiations( q, insts );
  }else{
    Assert(false);
  }
}

void TheoryEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiationTermVectors( q, tvecs );
  }else{
    Assert(false);
  }
}

void TheoryEngine::getInstantiations( std::map< Node, std::vector< Node > >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiations( insts );
  }else{
    Assert(false);
  }
}

void TheoryEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  if( d_quantEngine ){
    d_quantEngine->getInstantiationTermVectors( insts );
  }else{
    Assert(false);
  }
}

Node TheoryEngine::getInstantiatedConjunction( Node q ) {
  if( d_quantEngine ){
    return d_quantEngine->getInstantiatedConjunction( q );
  }else{
    Assert(false);
    return Node::null();
  }
}


static Node mkExplanation(const std::vector<NodeTheoryPair>& explanation) {

  std::set<TNode> all;
  for (unsigned i = 0; i < explanation.size(); ++ i) {
    Assert(explanation[i].d_theory == THEORY_SAT_SOLVER);
    all.insert(explanation[i].d_node);
  }

  if (all.size() == 0) {
    // Normalize to true
    return NodeManager::currentNM()->mkConst<bool>(true);
  }

  if (all.size() == 1) {
    // All the same, or just one
    return explanation[0].d_node;
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

Node TheoryEngine::getExplanation(TNode node)
{
  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node
                           << "): current propagation index = "
                           << d_propagationMapTimestamp << endl;

  bool polarity = node.getKind() != kind::NOT;
  TNode atom = polarity ? node : node[0];

  // If we're not in shared mode, explanations are simple
  if (!d_logicInfo.isSharingEnabled())
  {
    Debug("theory::explain")
        << "TheoryEngine::getExplanation: sharing is NOT enabled. "
        << " Responsible theory is: " << theoryOf(atom)->getId() << std::endl;

    TrustNode texplanation = theoryOf(atom)->explain(node);
    Node explanation = texplanation.getNode();
    Debug("theory::explain") << "TheoryEngine::getExplanation(" << node
                             << ") => " << explanation << endl;
    return explanation;
  }

  Debug("theory::explain") << "TheoryEngine::getExplanation: sharing IS enabled"
                           << std::endl;

  // Initial thing to explain
  NodeTheoryPair toExplain(node, THEORY_SAT_SOLVER, d_propagationMapTimestamp);
  Assert(d_propagationMap.find(toExplain) != d_propagationMap.end());

  NodeTheoryPair nodeExplainerPair = d_propagationMap[toExplain];
  Debug("theory::explain")
      << "TheoryEngine::getExplanation: explainer for node "
      << nodeExplainerPair.d_node
      << " is theory: " << nodeExplainerPair.d_theory << std::endl;

  // Create the workplace for explanations
  std::vector<NodeTheoryPair> explanationVector;
  explanationVector.push_back(d_propagationMap[toExplain]);
  // Process the explanation
  getExplanation(explanationVector);
  Node explanation = mkExplanation(explanationVector);

  Debug("theory::explain") << "TheoryEngine::getExplanation(" << node << ") => "
                           << explanation << endl;

  return explanation;
}

struct AtomsCollect {

  std::vector<TNode> d_atoms;
  std::unordered_set<TNode, TNodeHashFunction> d_visited;

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
    }else if( eqNormalized.getKind() != kind::EQUAL){
      Assert(eqNormalized.getKind() == kind::BOOLEAN_TERM_VARIABLE
             || (eqNormalized.getKind() == kind::NOT
                 && eqNormalized[0].getKind() == kind::BOOLEAN_TERM_VARIABLE));
      // this happens for Boolean term equalities V = true that are rewritten to V, we should skip
      //  TODO : revisit this
      continue;
    }

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
                                        bool negated,
                                        theory::LemmaProperty p,
                                        theory::TheoryId atomsTo)
{
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
    if (!negated) {
      n = node.negate();
    }
    Dump("t-lemmas") << CommentCommand("theory lemma: expect valid")
                     << CheckSatCommand(n.toExpr());
  }
  bool removable = isLemmaPropertyRemovable(p);
  bool preprocess = isLemmaPropertyPreprocess(p);

  // call preprocessor
  std::vector<TrustNode> newLemmas;
  std::vector<Node> newSkolems;
  TrustNode tlemma = d_tpp.preprocess(node, newLemmas, newSkolems, preprocess);

  // !!!!!!! temporary, until this method is fully updated from proof-new
  if (tlemma.isNull())
  {
    tlemma = TrustNode::mkTrustLemma(node);
  }

  // must use an assertion pipeline due to decision engine below
  AssertionPipeline lemmas;
  // make the assertion pipeline
  lemmas.push_back(tlemma.getNode());
  lemmas.updateRealAssertionsEnd();
  Assert(newSkolems.size() == newLemmas.size());
  for (size_t i = 0, nsize = newLemmas.size(); i < nsize; i++)
  {
    // store skolem mapping here
    IteSkolemMap& imap = lemmas.getIteSkolemMap();
    imap[newSkolems[i]] = lemmas.size();
    lemmas.push_back(newLemmas[i].getNode());
  }

  // If specified, we must add this lemma to the set of those that need to be
  // justified, where note we pass all auxiliary lemmas in lemmas, since these
  // by extension must be justified as well.
  if (d_relManager != nullptr && isLemmaPropertyNeedsJustify(p))
  {
    d_relManager->notifyPreprocessedAssertions(lemmas.ref());
  }

  // assert lemmas to prop engine
  for (size_t i = 0, lsize = lemmas.size(); i < lsize; ++i)
  {
    d_propEngine->assertLemma(lemmas[i], i == 0 && negated, removable);
  }

  // WARNING: Below this point don't assume lemmas[0] to be not negated.
  if(negated) {
    lemmas.replace(0, lemmas[0].notNode());
    negated = false;
  }

  // assert to decision engine
  if (!removable)
  {
    d_propEngine->addAssertionsToDecisionEngine(lemmas);
  }

  // Mark that we added some lemmas
  d_lemmasAdded = true;

  // Lemma analysis isn't online yet; this lemma may only live for this
  // user level.
  Node retLemma = lemmas[0];
  if (lemmas.size() > 1)
  {
    // the returned lemma is the conjunction of all additional lemmas.
    retLemma = NodeManager::currentNM()->mkNode(kind::AND, lemmas.ref());
  }
  return theory::LemmaStatus(retLemma, d_userContext->getLevel());
}

void TheoryEngine::conflict(TNode conflict, TheoryId theoryId) {

  Debug("theory::conflict") << "TheoryEngine::conflict(" << conflict << ", " << theoryId << ")" << endl;

  Trace("dtview::conflict") << ":THEORY-CONFLICT: " << conflict << std::endl;

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
    lemma(fullConflict,
          true,
          LemmaProperty::REMOVABLE,
          THEORY_LAST);
  } else {
    // When only one theory, the conflict should need no processing
    Assert(properConflict(conflict));
    lemma(conflict, true, LemmaProperty::REMOVABLE, THEORY_LAST);
  }
}

void TheoryEngine::getExplanation(
    std::vector<NodeTheoryPair>& explanationVector)
{
  Assert(explanationVector.size() > 0);

  unsigned i = 0; // Index of the current literal we are processing
  unsigned j = 0; // Index of the last literal we are keeping

  // cache of nodes we have already explained by some theory
  std::unordered_map<Node, size_t, NodeHashFunction> cache;

  while (i < explanationVector.size()) {
    // Get the current literal to explain
    NodeTheoryPair toExplain = explanationVector[i];

    Debug("theory::explain")
        << "[i=" << i << "] TheoryEngine::explain(): processing ["
        << toExplain.d_timestamp << "] " << toExplain.d_node << " sent from "
        << toExplain.d_theory << endl;

    if (cache.find(toExplain.d_node) != cache.end()
        && cache[toExplain.d_node] < toExplain.d_timestamp)
    {
      ++i;
      continue;
    }
    cache[toExplain.d_node] = toExplain.d_timestamp;

    // If a true constant or a negation of a false constant we can ignore it
    if (toExplain.d_node.isConst() && toExplain.d_node.getConst<bool>())
    {
      ++ i;
      continue;
    }
    if (toExplain.d_node.getKind() == kind::NOT && toExplain.d_node[0].isConst()
        && !toExplain.d_node[0].getConst<bool>())
    {
      ++ i;
      continue;
    }

    // If from the SAT solver, keep it
    if (toExplain.d_theory == THEORY_SAT_SOLVER)
    {
      Debug("theory::explain") << "\tLiteral came from THEORY_SAT_SOLVER. Kepping it." << endl;
      explanationVector[j++] = explanationVector[i++];
      continue;
    }

    // If an and, expand it
    if (toExplain.d_node.getKind() == kind::AND)
    {
      Debug("theory::explain")
          << "TheoryEngine::explain(): expanding " << toExplain.d_node
          << " got from " << toExplain.d_theory << endl;
      for (unsigned k = 0; k < toExplain.d_node.getNumChildren(); ++k)
      {
        NodeTheoryPair newExplain(
            toExplain.d_node[k], toExplain.d_theory, toExplain.d_timestamp);
        explanationVector.push_back(newExplain);
      }
      ++ i;
      continue;
    }

    // See if it was sent to the theory by another theory
    PropagationMap::const_iterator find = d_propagationMap.find(toExplain);
    if (find != d_propagationMap.end()) {
      Debug("theory::explain")
          << "\tTerm was propagated by another theory (theory = "
          << getTheoryString((*find).second.d_theory) << ")" << std::endl;
      // There is some propagation, check if its a timely one
      if ((*find).second.d_timestamp < toExplain.d_timestamp)
      {
        Debug("theory::explain")
            << "\tRelevant timetsamp, pushing " << (*find).second.d_node
            << "to index = " << explanationVector.size() << std::endl;
        explanationVector.push_back((*find).second);
        ++i;

        continue;
      }
    }

    Node explanation;
    if (toExplain.d_theory == THEORY_BUILTIN)
    {
      explanation = d_sharedTerms.explain(toExplain.d_node);
      Debug("theory::explain") << "\tTerm was propagated by THEORY_BUILTIN. Explanation: " << explanation << std::endl;
    }
    else
    {
      TrustNode texp = theoryOf(toExplain.d_theory)->explain(toExplain.d_node);
      explanation = texp.getNode();
      Debug("theory::explain") << "\tTerm was propagated by owner theory: "
                               << theoryOf(toExplain.d_theory)->getId()
                               << ". Explanation: " << explanation << std::endl;
    }

    Debug("theory::explain")
        << "TheoryEngine::explain(): got explanation " << explanation
        << " got from " << toExplain.d_theory << endl;
    Assert(explanation != toExplain.d_node)
        << "wasn't sent to you, so why are you explaining it trivially";
    // Mark the explanation
    NodeTheoryPair newExplain(
        explanation, toExplain.d_theory, toExplain.d_timestamp);
    explanationVector.push_back(newExplain);

    ++ i;
  }

  // Keep only the relevant literals
  explanationVector.resize(j);
}

void TheoryEngine::setUserAttribute(const std::string& attr,
                                    Node n,
                                    const std::vector<Node>& node_values,
                                    const std::string& str_value)
{
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

void TheoryEngine::checkTheoryAssertionsWithModel(bool hardFailure) {
  for(TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId) {
    Theory* theory = d_theoryTable[theoryId];
    if(theory && d_logicInfo.isTheoryEnabled(theoryId)) {
      for(context::CDList<Assertion>::const_iterator it = theory->facts_begin(),
            it_end = theory->facts_end();
          it != it_end;
          ++it) {
        Node assertion = (*it).d_assertion;
        if (!isRelevant(assertion))
        {
          // not relevant, skip
          continue;
        }
        Node val = d_tc->getModel()->getValue(assertion);
        if (val != d_true)
        {
          std::stringstream ss;
          ss << " " << theoryId
             << " has an asserted fact that the model doesn't satisfy." << endl
             << "The fact: " << assertion << endl
             << "Model value: " << val << endl;
          if (hardFailure)
          {
            if (val == d_false)
            {
              // Always an error if it is false
              InternalError() << ss.str();
            }
            else
            {
              // Otherwise just a warning. Notice this case may happen for
              // assertions with unevaluable operators, e.g. transcendental
              // functions. It also may happen for separation logic, where
              // check-model support is limited.
              Warning() << ss.str();
            }
          }
        }
      }
    }
  }
}

std::pair<bool, Node> TheoryEngine::entailmentCheck(options::TheoryOfMode mode,
                                                    TNode lit)
{
  TNode atom = (lit.getKind() == kind::NOT) ? lit[0] : lit;
  if( atom.getKind()==kind::AND || atom.getKind()==kind::OR || atom.getKind()==kind::IMPLIES ){
    //Boolean connective, recurse
    std::vector< Node > children;
    bool pol = (lit.getKind()!=kind::NOT);
    bool is_conjunction = pol==(lit.getKind()==kind::AND);
    for( unsigned i=0; i<atom.getNumChildren(); i++ ){
      Node ch = atom[i];
      if( pol==( lit.getKind()==kind::IMPLIES && i==0 ) ){
        ch = atom[i].negate();
      }
      std::pair<bool, Node> chres = entailmentCheck(mode, ch);
      if( chres.first ){
        if( !is_conjunction ){
          return chres;
        }else{
          children.push_back( chres.second );
        }
      }else if( !chres.first && is_conjunction ){
        return std::pair<bool, Node>(false, Node::null());
      }
    }
    if( is_conjunction ){
      return std::pair<bool, Node>(true, NodeManager::currentNM()->mkNode(kind::AND, children));
    }else{
      return std::pair<bool, Node>(false, Node::null());
    }
  }else if( atom.getKind()==kind::ITE || ( atom.getKind()==kind::EQUAL && atom[0].getType().isBoolean() ) ){
    bool pol = (lit.getKind()!=kind::NOT);
    for( unsigned r=0; r<2; r++ ){
      Node ch = atom[0];
      if( r==1 ){
        ch = ch.negate();
      }
      std::pair<bool, Node> chres = entailmentCheck(mode, ch);
      if( chres.first ){
        Node ch2 = atom[ atom.getKind()==kind::ITE ? r+1 : 1 ];
        if( pol==( atom.getKind()==kind::ITE ? true : r==1 ) ){
          ch2 = ch2.negate();
        }
        std::pair<bool, Node> chres2 = entailmentCheck(mode, ch2);
        if( chres2.first ){
          return std::pair<bool, Node>(true, NodeManager::currentNM()->mkNode(kind::AND, chres.second, chres2.second));
        }else{
          break;
        }
      }
    }
    return std::pair<bool, Node>(false, Node::null());
  }else{
    //it is a theory atom
    theory::TheoryId tid = theory::Theory::theoryOf(mode, atom);
    theory::Theory* th = theoryOf(tid);

    Assert(th != NULL);
    Trace("theory-engine-entc") << "Entailment check : " << lit << std::endl;

    std::pair<bool, Node> chres = th->entailmentCheck(lit);
    return chres;
  }
}

void TheoryEngine::spendResource(ResourceManager::Resource r)
{
  d_resourceManager->spendResource(r);
}

}/* CVC4 namespace */
