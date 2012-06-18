/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway, kshitij
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include <vector>
#include <string>
#include <iterator>
#include <utility>
#include <sstream>
#include <stack>
#include <ext/hash_map>

#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "decision/decision_engine.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"
#include "prop/prop_engine.h"
#include "smt/bad_option_exception.h"
#include "smt/modal_exception.h"
#include "smt/no_such_function_exception.h"
#include "smt/smt_engine.h"
#include "theory/theory_engine.h"
#include "proof/proof_manager.h"
#include "util/proof.h"
#include "util/boolean_simplification.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/options.h"
#include "util/output.h"
#include "util/hash.h"
#include "theory/substitutions.h"
#include "theory/builtin/theory_builtin.h"
#include "theory/booleans/theory_bool.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/uf/theory_uf.h"
#include "theory/arith/theory_arith.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/bv/theory_bv.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/theory_traits.h"
#include "theory/logic_info.h"
#include "util/ite_removal.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {

namespace smt {

/**
 * Representation of a defined function.  We keep these around in
 * SmtEngine to permit expanding definitions late (and lazily), to
 * support getValue() over defined functions, to support user output
 * in terms of defined functions, etc.
 */
class DefinedFunction {
  Node d_func;
  vector<Node> d_formals;
  Node d_formula;
public:
  DefinedFunction() {}
  DefinedFunction(Node func, vector<Node> formals, Node formula) :
    d_func(func),
    d_formals(formals),
    d_formula(formula) {
  }
  Node getFunction() const { return d_func; }
  vector<Node> getFormals() const { return d_formals; }
  Node getFormula() const { return d_formula; }
};/* class DefinedFunction */

/**
 * This is an inelegant solution, but for the present, it will work.
 * The point of this is to separate the public and private portions of
 * the SmtEngine class, so that smt_engine.h doesn't
 * include "expr/node.h", which is a private CVC4 header (and can lead
 * to linking errors due to the improper inlining of non-visible symbols
 * into user code!).
 *
 * The "real" solution (that which is usually implemented) is to move
 * ALL the implementation to SmtEnginePrivate and maintain a
 * heap-allocated instance of it in SmtEngine.  SmtEngine (the public
 * one) becomes an "interface shell" which simply acts as a forwarder
 * of method calls.
 */
class SmtEnginePrivate {
  SmtEngine& d_smt;

  /** The assertions yet to be preprocessed */
  vector<Node> d_assertionsToPreprocess;

  /** Learned literals */
  vector<Node> d_nonClausalLearnedLiterals;

  /** Size of assertions array when preprocessing starts */
  unsigned d_realAssertionsEnd;

  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;

  /** Assertions to push to sat */
  vector<Node> d_assertionsToCheck;

  /** Map from skolem variables to index in d_assertionsToCheck containing
   * corresponding introduced Boolean ite */
  IteSkolemMap d_iteSkolemMap;

  /** The top level substitutions */
  SubstitutionMap d_topLevelSubstitutions;

  /**
   * The last substitution that the SAT layer was told about.
   * In incremental settings, substitutions cannot be performed
   * "backward," only forward.  So SAT needs to be told of all
   * substitutions that are going to be done.  This iterator
   * holds the last substitution from d_topLevelSubstitutions
   * that was pushed out to SAT.
   * If d_lastSubstitutionPos == d_topLevelSubstitutions.end(),
   * then nothing has been pushed out yet. */
  context::CDO<SubstitutionMap::iterator> d_lastSubstitutionPos;

  static const bool d_doConstantProp = true;

  /**
   * Runs the nonclausal solver and tries to solve all the assigned
   * theory literals.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool nonClausalSimplify();

  /**
   * Performs static learning on the assertions.
   */
  void staticLearning();

  /**
   * Remove ITEs from the assertions.
   */
  void removeITEs();

  // Simplify ITE structure
  void simpITE();

  // Simplify based on unconstrained values
  void unconstrainedSimp();

  /**
   * Any variable in a assertion that is declared as a subtype type
   * (predicate subtype or integer subrange type) must be constrained
   * to be in that type.
   */
  void constrainSubtypes(TNode n, std::vector<Node>& assertions)
    throw(AssertionException);

  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions() throw(NoSuchFunctionException, AssertionException);

public:

  SmtEnginePrivate(SmtEngine& smt) :
    d_smt(smt),
    d_nonClausalLearnedLiterals(),
    d_propagator(d_nonClausalLearnedLiterals, true, true),
    d_topLevelSubstitutions(smt.d_userContext),
    d_lastSubstitutionPos(smt.d_userContext, d_topLevelSubstitutions.end()) {
  }

  Node applySubstitutions(TNode node) const {
    return Rewriter::rewrite(d_topLevelSubstitutions.apply(node));
  }

  /**
   * Process the assertions that have been asserted.
   */
  void processAssertions();

  /**
   * Process a user pop.  Clears out the non-context-dependent stuff in this
   * SmtEnginePrivate.  Necessary to clear out our assertion vectors in case
   * someone does a push-assert-pop without a check-sat.
   */
  void notifyPop() {
    d_assertionsToPreprocess.clear();
    d_nonClausalLearnedLiterals.clear();
    d_assertionsToCheck.clear();
  }

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   */
  void addFormula(TNode n)
    throw(NoSuchFunctionException, AssertionException);

  /**
   * Expand definitions in n.
   */
  Node expandDefinitions(TNode n, hash_map<TNode, Node, TNodeHashFunction>& cache)
    throw(NoSuchFunctionException, AssertionException);

};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

using namespace CVC4::smt;

SmtEngine::SmtEngine(ExprManager* em) throw(AssertionException) :
  d_context(em->getContext()),
  d_userLevels(),
  d_userContext(new UserContext()),
  d_exprManager(em),
  d_nodeManager(d_exprManager->getNodeManager()),
  d_decisionEngine(NULL),
  d_theoryEngine(NULL),
  d_propEngine(NULL),
  d_definedFunctions(NULL),
  d_assertionList(NULL),
  d_assignments(NULL),
  d_logic(),
  d_fullyInited(false),
  d_problemExtended(false),
  d_queryMade(false),
  d_needPostsolve(false),
  d_earlyTheoryPP(true),
  d_timeBudgetCumulative(0),
  d_timeBudgetPerCall(0),
  d_resourceBudgetCumulative(0),
  d_resourceBudgetPerCall(0),
  d_cumulativeTimeUsed(0),
  d_cumulativeResourceUsed(0),
  d_status(),
  d_private(new smt::SmtEnginePrivate(*this)),
  d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
  d_nonclausalSimplificationTime("smt::SmtEngine::nonclausalSimplificationTime"),
  d_numConstantProps("smt::SmtEngine::numConstantProps", 0),
  d_staticLearningTime("smt::SmtEngine::staticLearningTime"),
  d_simpITETime("smt::SmtEngine::simpITETime"),
  d_unconstrainedSimpTime("smt::SmtEngine::unconstrainedSimpTime"),
  d_iteRemovalTime("smt::SmtEngine::iteRemovalTime"),
  d_theoryPreprocessTime("smt::SmtEngine::theoryPreprocessTime"),
  d_cnfConversionTime("smt::SmtEngine::cnfConversionTime"),
  d_numAssertionsPre("smt::SmtEngine::numAssertionsPreITERemoval", 0),
  d_numAssertionsPost("smt::SmtEngine::numAssertionsPostITERemoval", 0) {

  NodeManagerScope nms(d_nodeManager);

  StatisticsRegistry::registerStat(&d_definitionExpansionTime);
  StatisticsRegistry::registerStat(&d_nonclausalSimplificationTime);
  StatisticsRegistry::registerStat(&d_numConstantProps);
  StatisticsRegistry::registerStat(&d_staticLearningTime);
  StatisticsRegistry::registerStat(&d_simpITETime);
  StatisticsRegistry::registerStat(&d_unconstrainedSimpTime);
  StatisticsRegistry::registerStat(&d_iteRemovalTime);
  StatisticsRegistry::registerStat(&d_theoryPreprocessTime);
  StatisticsRegistry::registerStat(&d_cnfConversionTime);
  StatisticsRegistry::registerStat(&d_numAssertionsPre);
  StatisticsRegistry::registerStat(&d_numAssertionsPost);

  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context, d_userContext, const_cast<const LogicInfo&>(d_logic));

  // Add the theories
#ifdef CVC4_FOR_EACH_THEORY_STATEMENT
#undef CVC4_FOR_EACH_THEORY_STATEMENT
#endif
#define CVC4_FOR_EACH_THEORY_STATEMENT(THEORY) \
    d_theoryEngine->addTheory<TheoryTraits<THEORY>::theory_class>(THEORY);
  CVC4_FOR_EACH_THEORY;

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_userContext->push();
  d_context->push();

  d_definedFunctions = new(true) DefinedFunctionMap(d_userContext);

  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(Options::current()->interactive ||
     Options::current()->incrementalSolving) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new(true) AssertionList(d_userContext);
  }

  if(Options::current()->perCallResourceLimit != 0) {
    setResourceLimit(Options::current()->perCallResourceLimit, false);
  }
  if(Options::current()->cumulativeResourceLimit != 0) {
    setResourceLimit(Options::current()->cumulativeResourceLimit, true);
  }
  if(Options::current()->perCallMillisecondLimit != 0) {
    setTimeLimit(Options::current()->perCallMillisecondLimit, false);
  }
  if(Options::current()->cumulativeMillisecondLimit != 0) {
    setTimeLimit(Options::current()->cumulativeMillisecondLimit, true);
  }
}

void SmtEngine::finishInit() {
  d_decisionEngine = new DecisionEngine(d_context, d_userContext);
  d_decisionEngine->init();   // enable appropriate strategies

  d_propEngine = new PropEngine(d_theoryEngine, d_decisionEngine, d_context);

  d_theoryEngine->setPropEngine(d_propEngine);
  d_theoryEngine->setDecisionEngine(d_decisionEngine);

}

void SmtEngine::finalOptionsAreSet() {
  if(d_fullyInited) {
    return;
  }

  finishInit();                 // finish initalization, creating prop
                                // engine etc.

  AlwaysAssert( d_propEngine->getAssertionLevel() == 0,
                "The PropEngine has pushed but the SmtEngine "
                "hasn't finished initializing!" );

  d_fullyInited = true;
  d_logic.lock();

  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(true));
  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(false).notNode());
}

void SmtEngine::shutdown() {
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << QuitCommand();
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  if(d_propEngine != NULL) d_propEngine->shutdown();
  if(d_theoryEngine != NULL) d_theoryEngine->shutdown();
  if(d_decisionEngine != NULL) d_decisionEngine->shutdown();
}

SmtEngine::~SmtEngine() throw() {
  NodeManagerScope nms(d_nodeManager);

  try {
    while(Options::current()->incrementalSolving && d_userContext->getLevel() > 1) {
      internalPop();
    }

    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_context->pop();
    d_userContext->pop();

    if(d_assignments != NULL) {
      d_assignments->deleteSelf();
    }

    if(d_assertionList != NULL) {
      d_assertionList->deleteSelf();
    }

    d_definedFunctions->deleteSelf();

    StatisticsRegistry::unregisterStat(&d_definitionExpansionTime);
    StatisticsRegistry::unregisterStat(&d_nonclausalSimplificationTime);
    StatisticsRegistry::unregisterStat(&d_numConstantProps);
    StatisticsRegistry::unregisterStat(&d_staticLearningTime);
    StatisticsRegistry::unregisterStat(&d_simpITETime);
    StatisticsRegistry::unregisterStat(&d_unconstrainedSimpTime);
    StatisticsRegistry::unregisterStat(&d_iteRemovalTime);
    StatisticsRegistry::unregisterStat(&d_theoryPreprocessTime);
    StatisticsRegistry::unregisterStat(&d_cnfConversionTime);
    StatisticsRegistry::unregisterStat(&d_numAssertionsPre);
    StatisticsRegistry::unregisterStat(&d_numAssertionsPost);

    delete d_private;
    delete d_userContext;

    delete d_theoryEngine;
    delete d_propEngine;
    //delete d_decisionEngine;
  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << endl
              << e << endl;
  }
}

void SmtEngine::setLogic(const LogicInfo& logic) throw(ModalException) {
  NodeManagerScope nms(d_nodeManager);

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetBenchmarkLogicCommand(logic.getLogicString());
  }

  d_logic = logic;
  setLogicInternal();
}

void SmtEngine::setLogic(const std::string& s) throw(ModalException) {
  NodeManagerScope nms(d_nodeManager);

  setLogic(LogicInfo(s));
}

// This function is called when d_logic has just been changed.
// The LogicInfo isn't passed in explicitly, because that might
// tempt people in the code to use the (potentially unlocked)
// version that's passed in, leading to assert-fails in certain
// uses of the CVC4 library.
void SmtEngine::setLogicInternal() throw(AssertionException) {
  Assert(!d_fullyInited, "setting logic in SmtEngine but the engine has already finished initializing for this run");

  d_logic.lock();

  // Set the options for the theoryOf
  if(!Options::current()->theoryOfModeSetByUser) {
    if(d_logic.isSharingEnabled() && !d_logic.isTheoryEnabled(THEORY_BV)) {
      Theory::setTheoryOfMode(theory::THEORY_OF_TERM_BASED);
    } else {
      Theory::setTheoryOfMode(theory::THEORY_OF_TYPE_BASED);
    }
  } else {
    Theory::setTheoryOfMode(Options::current()->theoryOfMode);
  }

  // by default, symmetry breaker is on only for QF_UF
  if(! Options::current()->ufSymmetryBreakerSetByUser) {
    bool qf_uf = d_logic.isPure(THEORY_UF) && !d_logic.isQuantified();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf << std::endl;
    NodeManager::currentNM()->getOptions()->ufSymmetryBreaker = qf_uf;
  }
  // by default, nonclausal simplification is off for QF_SAT and for quantifiers
  if(! Options::current()->simplificationModeSetByUser) {
    bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
    bool quantifiers = d_logic.isQuantified();
    Trace("smt") << "setting simplification mode to <" << d_logic.getLogicString() << "> " << (!qf_sat && !quantifiers) << std::endl;
    NodeManager::currentNM()->getOptions()->simplificationMode = (qf_sat || quantifiers ? Options::SIMPLIFICATION_MODE_NONE : Options::SIMPLIFICATION_MODE_BATCH);
  }

  // If in arrays, set the UF handler to arrays
  if(d_logic.isTheoryEnabled(THEORY_ARRAY) && !d_logic.isQuantified()) {
    Theory::setUninterpretedSortOwner(THEORY_ARRAY);
  } else {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }
  // Turn on ite simplification for QF_LIA and QF_AUFBV
  if(! Options::current()->doITESimpSetByUser) {
    bool iteSimp = !d_logic.isQuantified() &&
      ((d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areRealsUsed()) ||
       (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_UF) && d_logic.isTheoryEnabled(THEORY_BV)));
    Trace("smt") << "setting ite simplification to " << iteSimp << std::endl;
    NodeManager::currentNM()->getOptions()->doITESimp = iteSimp;
  }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if(! Options::current()->repeatSimpSetByUser) {
    bool repeatSimp = !d_logic.isQuantified() &&
      (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_UF) && d_logic.isTheoryEnabled(THEORY_BV));
    Trace("smt") << "setting repeat simplification to " << repeatSimp << std::endl;
    NodeManager::currentNM()->getOptions()->repeatSimp = repeatSimp;
  }
  // Turn on unconstrained simplification for QF_AUFBV
  if(! Options::current()->unconstrainedSimpSetByUser || Options::current()->incrementalSolving) {
    //    bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
    //    bool uncSimp = false && !qf_sat && !Options::current()->incrementalSolving;
    bool uncSimp = !Options::current()->incrementalSolving && !d_logic.isQuantified() &&
      (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_BV));
    Trace("smt") << "setting unconstrained simplification to " << uncSimp << std::endl;
    NodeManager::currentNM()->getOptions()->unconstrainedSimp = uncSimp;
  }
  // Turn on arith rewrite equalities only for pure arithmetic
  if(! Options::current()->arithRewriteEqSetByUser) {
    bool arithRewriteEq = d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq << std::endl;
    NodeManager::currentNM()->getOptions()->arithRewriteEq = arithRewriteEq;
  }
  if(!  Options::current()->arithHeuristicPivotsSetByUser){
    int16_t heuristicPivots = 5;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      if(d_logic.isDifferenceLogic()){
        heuristicPivots = -1;
      }else if(!d_logic.areIntegersUsed()){
        heuristicPivots = 0;
      }
    }
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots << std::endl;
    NodeManager::currentNM()->getOptions()->arithHeuristicPivots = heuristicPivots;
  }
  if(! Options::current()->arithPivotThresholdSetByUser){
    uint16_t pivotThreshold = 2;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      if(d_logic.isDifferenceLogic()){
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold << std::endl;
    NodeManager::currentNM()->getOptions()->arithPivotThreshold = pivotThreshold;
  }
  if(! Options::current()->arithStandardCheckVarOrderPivotsSetByUser){
    int16_t varOrderPivots = -1;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  " << varOrderPivots << std::endl;
    NodeManager::currentNM()->getOptions()->arithStandardCheckVarOrderPivots = varOrderPivots;
  }
  // Turn off early theory preprocessing if arithRewriteEq is on
  if (NodeManager::currentNM()->getOptions()->arithRewriteEq) {
    d_earlyTheoryPP = false;
  }
  // Turn on justification heuristic of the decision engine for QF_BV and QF_AUFBV
  // and also use it in stop-only mode for QF_AUFLIA, QF_LRA and Quantifiers
  if(!Options::current()->decisionModeSetByUser) {
    Options::DecisionMode decMode =
      //QF_BV
      (not d_logic.isQuantified() &&
        d_logic.isPure(THEORY_BV)
        ) ||
      //QF_AUFBV
      (not d_logic.isQuantified() &&
       d_logic.isTheoryEnabled(THEORY_ARRAY) &&
       d_logic.isTheoryEnabled(THEORY_UF) &&
       d_logic.isTheoryEnabled(THEORY_BV)
       ) ||
      //QF_AUFLIA (and may be ends up enabling QF_AUFLRA?)
      (not d_logic.isQuantified() &&
       d_logic.isTheoryEnabled(THEORY_ARRAY) &&
       d_logic.isTheoryEnabled(THEORY_UF) &&
       d_logic.isTheoryEnabled(THEORY_ARITH)
       ) ||
      // QF_LRA
      (not d_logic.isQuantified() &&
       d_logic.isPure(THEORY_ARITH)
       ) ||
      // Quantifiers
      d_logic.isQuantified()
      ? Options::DECISION_STRATEGY_JUSTIFICATION
      : Options::DECISION_STRATEGY_INTERNAL;

    bool stoponly =
      // QF_AUFLIA
      (not d_logic.isQuantified() &&
       d_logic.isTheoryEnabled(THEORY_ARRAY) &&
       d_logic.isTheoryEnabled(THEORY_UF) &&
       d_logic.isTheoryEnabled(THEORY_ARITH)
       ) ||
      // QF_LRA
      (not d_logic.isQuantified() &&
       d_logic.isPure(THEORY_ARITH)
       ) ||
      // Quantifiers
      d_logic.isQuantified()
      ? true : false;

    Trace("smt") << "setting decision mode to " << decMode << std::endl;
    NodeManager::currentNM()->getOptions()->decisionMode = decMode;
    NodeManager::currentNM()->getOptions()->decisionOptions.stopOnly = stoponly;
  }
}

void SmtEngine::setInfo(const std::string& key, const SExpr& value)
  throw(BadOptionException, ModalException) {
  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;
  if(Dump.isOn("benchmark")) {
    if(key == ":status") {
      std::string s = value.getValue();
      BenchmarkStatus status =
        (s == "sat") ? SMT_SATISFIABLE :
          ((s == "unsat") ? SMT_UNSATISFIABLE : SMT_UNKNOWN);
      Dump("benchmark") << SetBenchmarkStatusCommand(status);
    } else {
      Dump("benchmark") << SetInfoCommand(key, value);
    }
  }

  // Check for CVC4-specific info keys (prefixed with "cvc4-" or "cvc4_")
  if(key.length() > 6) {
    string prefix = key.substr(0, 6);
    if(prefix == ":cvc4-" || prefix == ":cvc4_") {
      string cvc4key = key.substr(6);
      if(cvc4key == "logic") {
        if(! value.isAtom()) {
          throw BadOptionException("argument to (set-info :cvc4-logic ..) must be a string");
        }
        NodeManagerScope nms(d_nodeManager);
        d_logic = value.getValue();
        setLogicInternal();
        return;
      }
    }
  }

  // Check for standard info keys (SMT-LIB v1, SMT-LIB v2, ...)
  if(key == ":name" ||
     key == ":source" ||
     key == ":category" ||
     key == ":difficulty" ||
     key == ":smt-lib-version" ||
     key == ":notes") {
    // ignore these
    return;
  } else if(key == ":status") {
    string s;
    if(value.isAtom()) {
      s = value.getValue();
    }
    if(s != "sat" && s != "unsat" && s != "unknown") {
      throw BadOptionException("argument to (set-info :status ..) must be "
                               "`sat' or `unsat' or `unknown'");
    }
    d_status = Result(s);
    return;
  }
  throw BadOptionException();
}

SExpr SmtEngine::getInfo(const std::string& key) const
  throw(BadOptionException) {
  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if(key == ":all-statistics") {
    vector<SExpr> stats;
    for(StatisticsRegistry::const_iterator i = StatisticsRegistry::begin();
        i != StatisticsRegistry::end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i)->getName());
      v.push_back((*i)->getValue());
      stats.push_back(v);
    }
    return stats;
  } else if(key == ":error-behavior") {
    return SExpr("immediate-exit");
  } else if(key == ":name") {
    return Configuration::getName();
  } else if(key == ":version") {
    return Configuration::getVersionString();
  } else if(key == ":authors") {
    return Configuration::about();
  } else if(key == ":status") {
    return d_status.asSatisfiabilityResult().toString();
  } else if(key == ":reason-unknown") {
    if(d_status.isUnknown()) {
      stringstream ss;
      ss << d_status.whyUnknown();
      return ss.str();
    } else {
      throw ModalException("Can't get-info :reason-unknown when the "
                           "last result wasn't unknown!");
    }
  } else {
    throw BadOptionException();
  }
}

void SmtEngine::setOption(const std::string& key, const SExpr& value)
  throw(BadOptionException, ModalException) {

  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value);
  }

  if(key == ":print-success") {
    if(value.isAtom() && value.getValue() == "false") {
      *Options::current()->out << Command::printsuccess(false);
    } else if(value.isAtom() && value.getValue() == "true") {
      *Options::current()->out << Command::printsuccess(true);
    } else {
      throw BadOptionException();
    }
  } else if(key == ":expand-definitions") {
    throw BadOptionException();
  } else if(key == ":interactive-mode") {
    throw BadOptionException();
  } else if(key == ":regular-output-channel") {
    throw BadOptionException();
  } else if(key == ":diagnostic-output-channel") {
    throw BadOptionException();
  } else if(key == ":random-seed") {
    throw BadOptionException();
  } else if(key == ":verbosity") {
    throw BadOptionException();
  } else {
    // The following options can only be set at the beginning; we throw
    // a ModalException if someone tries.
    if(d_logic.isLocked()) {
      throw ModalException("logic already set; cannot set options");
    }

    if(key == ":produce-proofs") {
      throw BadOptionException();
    } else if(key == ":produce-unsat-cores") {
      throw BadOptionException();
    } else if(key == ":produce-models") {
      throw BadOptionException();
    } else if(key == ":produce-assignments") {
      throw BadOptionException();
    } else {
      throw BadOptionException();
    }
  }
}

SExpr SmtEngine::getOption(const std::string& key) const
  throw(BadOptionException) {

  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT getOption(" << key << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key);
  }
  if(key == ":print-success") {
    if(Command::printsuccess::getPrintSuccess(*Options::current()->out)) {
      return SExpr("true");
    } else {
      return SExpr("false");
    }
  } else if(key == ":expand-definitions") {
    throw BadOptionException();
  } else if(key == ":interactive-mode") {
    throw BadOptionException();
  } else if(key == ":produce-proofs") {
    throw BadOptionException();
  } else if(key == ":produce-unsat-cores") {
    throw BadOptionException();
  } else if(key == ":produce-models") {
    throw BadOptionException();
  } else if(key == ":produce-assignments") {
    throw BadOptionException();
  } else if(key == ":regular-output-channel") {
    return SExpr("stdout");
  } else if(key == ":diagnostic-output-channel") {
    return SExpr("stderr");
  } else if(key == ":random-seed") {
    throw BadOptionException();
  } else if(key == ":verbosity") {
    throw BadOptionException();
  } else {
    throw BadOptionException();
  }
}

void SmtEngine::defineFunction(Expr func,
                               const std::vector<Expr>& formals,
                               Expr formula) {
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  if(Dump.isOn("declarations")) {
    stringstream ss;
    ss << Expr::setlanguage(Expr::setlanguage::getLanguage(Dump.getStream()))
       << func;
    Dump("declarations") << DefineFunctionCommand(ss.str(), func, formals, formula);
  }
  NodeManagerScope nms(d_nodeManager);

  // type check body
  Type formulaType = formula.getType(Options::current()->typeChecking);

  Type funcType = func.getType();
  Type rangeType = funcType.isFunction() ?
    FunctionType(funcType).getRangeType() : funcType;
  if(formulaType != rangeType) {
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "Defined function's declared type does not match that of body\n"
       << "The function  : " << func << "\n"
       << "Its range type: " << rangeType << "\n"
       << "The body      : " << formula << "\n"
       << "Body type     : " << formulaType;
    throw TypeCheckingException(func, ss.str());
  }
  TNode funcNode = func.getTNode();
  vector<Node> formalsNodes;
  for(vector<Expr>::const_iterator i = formals.begin(),
        iend = formals.end();
      i != iend;
      ++i) {
    formalsNodes.push_back((*i).getNode());
  }
  TNode formulaNode = formula.getTNode();
  DefinedFunction def(funcNode, formalsNodes, formulaNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  d_definedFunctions->insert(funcNode, def);
}

Node SmtEnginePrivate::expandDefinitions(TNode n, hash_map<TNode, Node, TNodeHashFunction>& cache)
  throw(NoSuchFunctionException, AssertionException) {

  if(n.getKind() != kind::APPLY && n.getNumChildren() == 0) {
    // don't bother putting in the cache
    return n;
  }

  // maybe it's in the cache
  hash_map<TNode, Node, TNodeHashFunction>::iterator cacheHit = cache.find(n);
  if(cacheHit != cache.end()) {
    TNode ret = (*cacheHit).second;
    return ret.isNull() ? n : ret;
  }

  // otherwise expand it
  if(n.getKind() == kind::APPLY) {
    TNode func = n.getOperator();
    SmtEngine::DefinedFunctionMap::const_iterator i =
      d_smt.d_definedFunctions->find(func);
    DefinedFunction def = (*i).second;
    vector<Node> formals = def.getFormals();

    if(Debug.isOn("expand")) {
      Debug("expand") << "found: " << n << endl;
      Debug("expand") << " func: " << func << endl;
      string name = func.getAttribute(expr::VarNameAttr());
      Debug("expand") << "     : \"" << name << "\"" << endl;
    }
    if(i == d_smt.d_definedFunctions->end()) {
      throw NoSuchFunctionException(Expr(d_smt.d_exprManager, new Node(func)));
    }
    if(Debug.isOn("expand")) {
      Debug("expand") << " defn: " << def.getFunction() << endl
                      << "       [";
      if(formals.size() > 0) {
        copy( formals.begin(), formals.end() - 1,
              ostream_iterator<Node>(Debug("expand"), ", ") );
        Debug("expand") << formals.back();
      }
      Debug("expand") << "]" << endl
                      << "       " << def.getFunction().getType() << endl
                      << "       " << def.getFormula() << endl;
    }

    TNode fm = def.getFormula();
    Node instance = fm.substitute(formals.begin(), formals.end(),
                                  n.begin(), n.end());
    Debug("expand") << "made : " << instance << endl;

    Node expanded = expandDefinitions(instance, cache);
    cache[n] = (n == expanded ? Node::null() : expanded);
    return expanded;
  } else {
    Debug("expand") << "cons : " << n << endl;
    NodeBuilder<> nb(n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      Debug("expand") << "op   : " << n.getOperator() << endl;
      nb << n.getOperator();
    }
    for(TNode::iterator i = n.begin(),
          iend = n.end();
        i != iend;
        ++i) {
      Node expanded = expandDefinitions(*i, cache);
      Debug("expand") << "exchld: " << expanded << endl;
      nb << expanded;
    }
    Node node = nb;
    cache[n] = n == node ? Node::null() : node;
    return node;
  }
}

void SmtEnginePrivate::removeITEs() {
  d_smt.finalOptionsAreSet();

  Trace("simplify") << "SmtEnginePrivate::removeITEs()" << endl;

  // Remove all of the ITE occurrences and normalize
  RemoveITE::run(d_assertionsToCheck, d_iteSkolemMap);
  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
    d_assertionsToCheck[i] = Rewriter::rewrite(d_assertionsToCheck[i]);
  }
  
}

void SmtEnginePrivate::staticLearning() {
  d_smt.finalOptionsAreSet();

  TimerStat::CodeTimer staticLearningTimer(d_smt.d_staticLearningTime);

  Trace("simplify") << "SmtEnginePrivate::staticLearning()" << endl;

  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {

    NodeBuilder<> learned(kind::AND);
    learned << d_assertionsToCheck[i];
    d_smt.d_theoryEngine->ppStaticLearn(d_assertionsToCheck[i], learned);
    if(learned.getNumChildren() == 1) {
      learned.clear();
    } else {
      d_assertionsToCheck[i] = learned;
    }
  }
}


// returns false if it learns a conflict
bool SmtEnginePrivate::nonClausalSimplify() {
  d_smt.finalOptionsAreSet();

  TimerStat::CodeTimer nonclausalTimer(d_smt.d_nonclausalSimplificationTime);

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify()" << endl;

  d_propagator.initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Assert(Rewriter::rewrite(d_assertionsToPreprocess[i]) == d_assertionsToPreprocess[i]);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting " << d_assertionsToPreprocess[i] << endl;
    d_propagator.assert(d_assertionsToPreprocess[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (d_propagator.propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    d_assertionsToPreprocess.clear();
    d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
    d_propagator.finish();
    return false;
  }

  // No, conflict, go through the literals and solve them
  SubstitutionMap constantPropagations(d_smt.d_context);
  unsigned j = 0;
  for(unsigned i = 0, i_end = d_nonClausalLearnedLiterals.size(); i < i_end; ++ i) {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = d_nonClausalLearnedLiterals[i];
    Assert(Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Node learnedLiteralNew = d_topLevelSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew) {
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    for (;;) {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral) {
        break;
      }
      ++d_smt.d_numConstantProps;
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    // It might just simplify to a constant
    if (learnedLiteral.isConst()) {
      if (learnedLiteral.getConst<bool>()) {
        // If the learned literal simplifies to true, it's redundant
        continue;
      } else {
        // If the learned literal simplifies to false, we're in conflict
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict with "
                          << d_nonClausalLearnedLiterals[i] << endl;
        d_assertionsToPreprocess.clear();
        d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
        d_propagator.finish();
        return false;
      }
    }
    // Solve it with the corresponding theory
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "solving " << learnedLiteral << endl;
    Theory::PPAssertStatus solveStatus =
      d_smt.d_theoryEngine->solve(learnedLiteral, d_topLevelSubstitutions);

    switch (solveStatus) {
      case Theory::PP_ASSERT_STATUS_SOLVED: {
        // The literal should rewrite to true
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "solved " << learnedLiteral << endl;
        Assert(Rewriter::rewrite(d_topLevelSubstitutions.apply(learnedLiteral)).isConst());
        //        vector<pair<Node, Node> > equations;
        //        constantPropagations.simplifyLHS(d_topLevelSubstitutions, equations, true);
        //        if (equations.empty()) {
        //          break;
        //        }
        //        Assert(equations[0].first.isConst() && equations[0].second.isConst() && equations[0].first != equations[0].second);
        // else fall through
        break;
      }
      case Theory::PP_ASSERT_STATUS_CONFLICT:
        // If in conflict, we return false
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "conflict while solving "
                          << learnedLiteral << endl;
        d_assertionsToPreprocess.clear();
        d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
        d_propagator.finish();
        return false;
      default:
        if (d_doConstantProp && learnedLiteral.getKind() == kind::EQUAL && (learnedLiteral[0].isConst() || learnedLiteral[1].isConst())) {
          // constant propagation
          TNode t;
          TNode c;
          if (learnedLiteral[0].isConst()) {
            t = learnedLiteral[1];
            c = learnedLiteral[0];
          }
          else {
            t = learnedLiteral[0];
            c = learnedLiteral[1];
          }
          Assert(!t.isConst());
          Assert(constantPropagations.apply(t) == t);
          Assert(d_topLevelSubstitutions.apply(t) == t);
          constantPropagations.addSubstitution(t, c);
          // vector<pair<Node,Node> > equations;a
          // constantPropagations.simplifyLHS(t, c, equations, true);
          // if (!equations.empty()) {
          //   Assert(equations[0].first.isConst() && equations[0].second.isConst() && equations[0].first != equations[0].second);
          //   d_assertionsToPreprocess.clear();
          //   d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
          //   return;
          // }
          // d_topLevelSubstitutions.simplifyRHS(constantPropagations);
        }
        else {
          // Keep the literal
          d_nonClausalLearnedLiterals[j++] = d_nonClausalLearnedLiterals[i];
        }
        break;
    }

#ifdef CVC4_ASSERTIONS
    // Check data structure invariants:
    // 1. for each lhs of d_topLevelSubstitutions, does not appear anywhere in rhs of d_topLevelSubstitutions or anywhere in constantPropagations
    // 2. each lhs of constantPropagations rewrites to itself
    // 3. if l -> r is a constant propagation and l is a subterm of l' with l' -> r' another constant propagation, then l'[l/r] -> r' should be a
    //    constant propagation too
    // 4. each lhs of constantPropagations is different from each rhs
    SubstitutionMap::iterator pos = d_topLevelSubstitutions.begin();
    for (; pos != d_topLevelSubstitutions.end(); ++pos) {
      Assert((*pos).first.isVar());
      //      Assert(d_topLevelSubstitutions.apply((*pos).second) == (*pos).second);
    }
    for (pos = constantPropagations.begin(); pos != constantPropagations.end(); ++pos) {
      Assert((*pos).second.isConst());
      Assert(Rewriter::rewrite((*pos).first) == (*pos).first);
      // Node newLeft = d_topLevelSubstitutions.apply((*pos).first);
      // if (newLeft != (*pos).first) {
      //   newLeft = Rewriter::rewrite(newLeft);
      //   Assert(newLeft == (*pos).second ||
      //          (constantPropagations.hasSubstitution(newLeft) && constantPropagations.apply(newLeft) == (*pos).second));
      // }
      // newLeft = constantPropagations.apply((*pos).first);
      // if (newLeft != (*pos).first) {
      //   newLeft = Rewriter::rewrite(newLeft);
      //   Assert(newLeft == (*pos).second ||
      //          (constantPropagations.hasSubstitution(newLeft) && constantPropagations.apply(newLeft) == (*pos).second));
      // }
      Assert(constantPropagations.apply((*pos).second) == (*pos).second);
    }
#endif
  }
  // Resize the learnt
  d_nonClausalLearnedLiterals.resize(j);

  hash_set<TNode, TNodeHashFunction> s;
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Node assertion = d_assertionsToPreprocess[i];
    Node assertionNew = d_topLevelSubstitutions.apply(assertion);
    if (assertion != assertionNew) {
      assertion = Rewriter::rewrite(assertionNew);
    }
    Assert(Rewriter::rewrite(assertion) == assertion);
    for (;;) {
      assertionNew = constantPropagations.apply(assertion);
      if (assertionNew == assertion) {
        break;
      }
      ++d_smt.d_numConstantProps;
      assertion = Rewriter::rewrite(assertionNew);
    }
    s.insert(assertion);
    d_assertionsToCheck.push_back(assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: "
                      << assertion << endl;
  }
  d_assertionsToPreprocess.clear();

  NodeBuilder<> learnedBuilder(kind::AND);
  Assert(d_realAssertionsEnd <= d_assertionsToCheck.size());
  learnedBuilder << d_assertionsToCheck[d_realAssertionsEnd-1];

  if( Options::current()->incrementalSolving ||
      Options::current()->simplificationMode == Options::SIMPLIFICATION_MODE_INCREMENTAL ) {
    // Keep substitutions
    SubstitutionMap::iterator pos = d_lastSubstitutionPos;
    if(pos == d_topLevelSubstitutions.end()) {
      pos = d_topLevelSubstitutions.begin();
    } else {
      ++pos;
    }

    while(pos != d_topLevelSubstitutions.end()) {
      // Push out this substitution
      TNode lhs = (*pos).first, rhs = (*pos).second;
      Node n = NodeManager::currentNM()->mkNode(lhs.getType().isBoolean() ? kind::IFF : kind::EQUAL, lhs, rhs);
      learnedBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will notify SAT layer of substitution: " << n << endl;
      d_lastSubstitutionPos = pos;
      ++pos;
    }
  }

  for (unsigned i = 0; i < d_nonClausalLearnedLiterals.size(); ++ i) {
    Node learned = d_nonClausalLearnedLiterals[i];
    Node learnedNew = d_topLevelSubstitutions.apply(learned);
    if (learned != learnedNew) {
      learned = Rewriter::rewrite(learnedNew);
    }
    Assert(Rewriter::rewrite(learned) == learned);
    for (;;) {
      learnedNew = constantPropagations.apply(learned);
      if (learnedNew == learned) {
        break;
      }
      ++d_smt.d_numConstantProps;
      learned = Rewriter::rewrite(learnedNew);
    }
    if (s.find(learned) != s.end()) {
      continue;
    }
    s.insert(learned);
    learnedBuilder << learned;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal learned : "
                      << learned << endl;
  }
  d_nonClausalLearnedLiterals.clear();

  SubstitutionMap::iterator pos = constantPropagations.begin();
  for (; pos != constantPropagations.end(); ++pos) {
    Node cProp = (*pos).first.eqNode((*pos).second);
    if (s.find(cProp) != s.end()) {
      continue;
    }
    s.insert(cProp);
    learnedBuilder << cProp;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal constant propagation : "
                      << cProp << endl;
  }

  if(learnedBuilder.getNumChildren() > 1) {
    d_assertionsToCheck[d_realAssertionsEnd-1] = Rewriter::rewrite(Node(learnedBuilder));
  }

  d_propagator.finish();
  return true;
}


void SmtEnginePrivate::simpITE()
{
  TimerStat::CodeTimer simpITETimer(d_smt.d_simpITETime);

  Trace("simplify") << "SmtEnginePrivate::simpITE()" << endl;

  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {

    d_assertionsToCheck[i] = d_smt.d_theoryEngine->ppSimpITE(d_assertionsToCheck[i]);
  }
}


void SmtEnginePrivate::unconstrainedSimp()
{
  TimerStat::CodeTimer unconstrainedSimpTimer(d_smt.d_unconstrainedSimpTime);

  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << endl;
  d_smt.d_theoryEngine->ppUnconstrainedSimp(d_assertionsToCheck);
}


void SmtEnginePrivate::constrainSubtypes(TNode top, std::vector<Node>& assertions)
  throw(AssertionException) {

  Trace("constrainSubtypes") << "constrainSubtypes(): looking at " << top << endl;

  set<TNode> done;
  stack<TNode> worklist;
  worklist.push(top);
  done.insert(top);

  do {
    TNode n = worklist.top();
    worklist.pop();

    TypeNode t = n.getType();
    if(t.isPredicateSubtype()) {
      WarningOnce() << "Warning: CVC4 doesn't yet do checking that predicate subtypes are nonempty domains" << endl;
      Node pred = t.getSubtypePredicate();
      Kind k;
      // pred can be a LAMBDA, a function constant, or a datatype tester
      Trace("constrainSubtypes") << "constrainSubtypes(): pred.getType() == " << pred.getType() << endl;
      if(d_smt.d_definedFunctions->find(pred) != d_smt.d_definedFunctions->end()) {
        k = kind::APPLY;
      } else if(pred.getType().isTester()) {
        k = kind::APPLY_TESTER;
      } else {
        k = kind::APPLY_UF;
      }
      Node app = NodeManager::currentNM()->mkNode(k, pred, n);
      Trace("constrainSubtypes") << "constrainSubtypes(): assert(" << k << ") " << app << endl;
      assertions.push_back(app);
    } else if(t.isSubrange()) {
      SubrangeBounds bounds = t.getSubrangeBounds();
      Trace("constrainSubtypes") << "constrainSubtypes(): got bounds " << bounds << endl;
      if(bounds.lower.hasBound()) {
        Node c = NodeManager::currentNM()->mkConst(Rational(bounds.lower.getBound()));
        Node lb = NodeManager::currentNM()->mkNode(kind::LEQ, c, n);
        Trace("constrainSubtypes") << "constrainSubtypes(): assert " << lb << endl;
        assertions.push_back(lb);
      }
      if(bounds.upper.hasBound()) {
        Node c = NodeManager::currentNM()->mkConst(Rational(bounds.upper.getBound()));
        Node ub = NodeManager::currentNM()->mkNode(kind::LEQ, n, c);
        Trace("constrainSubtypes") << "constrainSubtypes(): assert " << ub << endl;
        assertions.push_back(ub);
      }
    }

    for(TNode::iterator i = n.begin(); i != n.end(); ++i) {
      if(done.find(*i) == done.end()) {
        worklist.push(*i);
        done.insert(*i);
      }
    }
  } while(! worklist.empty());
}

// returns false if simpflication led to "false"
bool SmtEnginePrivate::simplifyAssertions()
  throw(NoSuchFunctionException, AssertionException) {
  try {

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    if(Options::current()->simplificationMode != Options::SIMPLIFICATION_MODE_NONE) {
      // Perform non-clausal simplification
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << "performing non-clausal simplification" << endl;
      bool noConflict = nonClausalSimplify();
      if(!noConflict) return false;
    } else {
      Assert(d_assertionsToCheck.empty());
      d_assertionsToCheck.swap(d_assertionsToPreprocess);
    }

    Trace("smt") << "POST nonClasualSimplify" << std::endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    // Theory preprocessing
    if (d_smt.d_earlyTheoryPP) {
      TimerStat::CodeTimer codeTimer(d_smt.d_theoryPreprocessTime);
      // Call the theory preprocessors
      d_smt.d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
        Assert(Rewriter::rewrite(d_assertionsToCheck[i]) == d_assertionsToCheck[i]);
        d_assertionsToCheck[i] = d_smt.d_theoryEngine->preprocess(d_assertionsToCheck[i]);
        Assert(Rewriter::rewrite(d_assertionsToCheck[i]) == d_assertionsToCheck[i]);
      }
    }

    Trace("smt") << "POST theoryPP" << std::endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    // ITE simplification
    if(Options::current()->doITESimp) {
      simpITE();
    }

    Trace("smt") << "POST iteSimp" << std::endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    // Unconstrained simplification
    if(Options::current()->unconstrainedSimp) {
      unconstrainedSimp();
    }

    Trace("smt") << "POST unconstraintedSimp" << std::endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    if(Options::current()->repeatSimp && Options::current()->simplificationMode != Options::SIMPLIFICATION_MODE_NONE) {
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << " doing repeated simplification" << std::endl;
      d_assertionsToCheck.swap(d_assertionsToPreprocess);
      bool noConflict = nonClausalSimplify();
      if(!noConflict) return false;
    }

    Trace("smt") << "POST repeatSimp" << std::endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
  return true;
}

Result SmtEngine::check() {
  Assert(d_fullyInited);

  Trace("smt") << "SmtEngine::check()" << endl;

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  d_private->processAssertions();

  unsigned long millis = 0;
  if(d_timeBudgetCumulative != 0) {
    millis = getTimeRemaining();
    if(millis == 0) {
      return Result(Result::VALIDITY_UNKNOWN, Result::TIMEOUT);
    }
  }
  if(d_timeBudgetPerCall != 0 && (millis == 0 || d_timeBudgetPerCall < millis)) {
    millis = d_timeBudgetPerCall;
  }

  unsigned long resource = 0;
  if(d_resourceBudgetCumulative != 0) {
    resource = getResourceRemaining();
    if(resource == 0) {
      return Result(Result::VALIDITY_UNKNOWN, Result::RESOURCEOUT);
    }
  }
  if(d_resourceBudgetPerCall != 0 && (resource == 0 || d_resourceBudgetPerCall < resource)) {
    resource = d_resourceBudgetPerCall;
  }

  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat(millis, resource);

  // PropEngine::checkSat() returns the actual amount used in these
  // variables.
  d_cumulativeTimeUsed += millis;
  d_cumulativeResourceUsed += resource;

  Trace("limit") << "SmtEngine::check(): cumulative millis " << d_cumulativeTimeUsed
                 << ", conflicts " << d_cumulativeResourceUsed << endl;

  return result;
}

Result SmtEngine::quickCheck() {
  Assert(d_fullyInited);
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN, Result::REQUIRES_FULL_CHECK);
}

void SmtEnginePrivate::processAssertions() {
  Assert(d_smt.d_fullyInited);

  Trace("smt") << "SmtEnginePrivate::processAssertions()" << endl;

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  // any assertions added beyond realAssertionsEnd must NOT affect the equisatisfiability
  d_realAssertionsEnd = d_assertionsToPreprocess.size();
  if (d_realAssertionsEnd == 0) {
    return;
  }

  // Any variables of subtype types need to be constrained properly.
  // Careful, here: constrainSubtypes() adds to the back of
  // d_assertionsToPreprocess, but we don't need to reprocess those.
  // We also can't use an iterator, because the vector may be moved in
  // memory during this loop.
  for(unsigned i = 0, i_end = d_assertionsToPreprocess.size(); i != i_end; ++i) {
    constrainSubtypes(d_assertionsToPreprocess[i], d_assertionsToPreprocess);
  }

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  if(!Options::current()->lazyDefinitionExpansion) {
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_definitionExpansionTime);
    hash_map<TNode, Node, TNodeHashFunction> cache;
    for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
      d_assertionsToPreprocess[i] =
        expandDefinitions(d_assertionsToPreprocess[i], cache);
    }
  }
    
  // Apply the substitutions we already have, and normalize
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "applying substitutions" << endl;
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Trace("simplify") << "applying to " << d_assertionsToPreprocess[i] << endl;
    d_assertionsToPreprocess[i] =
      Rewriter::rewrite(d_topLevelSubstitutions.apply(d_assertionsToPreprocess[i]));
    Trace("simplify") << "  got " << d_assertionsToPreprocess[i] << endl;
  }

  bool noConflict = simplifyAssertions();

  if(Options::current()->doStaticLearning) {
    // Perform static learning
    Trace("simplify") << "SmtEnginePrivate::simplify(): "
                      << "performing static learning" << endl;
    staticLearning();
  }

  {
    TimerStat::CodeTimer codeTimer(d_smt.d_iteRemovalTime);
    // Remove ITEs, updating d_iteSkolemMap
    d_smt.d_numAssertionsPre += d_assertionsToCheck.size();
    removeITEs();
    d_smt.d_numAssertionsPost += d_assertionsToCheck.size();
  }

  if(Options::current()->repeatSimp) {
    d_assertionsToCheck.swap(d_assertionsToPreprocess);
    noConflict &= simplifyAssertions();
    if (noConflict) {
      // Some skolem variables may have been solved for - which is a good thing -
      // but it means we have to move those ITE's back to the main set of assertions
      IteSkolemMap::iterator it = d_iteSkolemMap.begin();
      IteSkolemMap::iterator iend = d_iteSkolemMap.end();
      NodeBuilder<> builder(kind::AND);
      builder << d_assertionsToCheck[d_realAssertionsEnd-1];
      for (; it != iend; ++it) {
        if (d_topLevelSubstitutions.hasSubstitution((*it).first)) {
          builder << d_assertionsToCheck[(*it).second];
          d_assertionsToCheck[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
        }
      }
      if(builder.getNumChildren() > 1) {
        d_assertionsToCheck[d_realAssertionsEnd-1] = Rewriter::rewrite(Node(builder));
      }
      // For some reason this is needed for some benchmarks, such as
      // http://church.cims.nyu.edu/benchmarks/smtlib2/QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      // Figure it out later
      removeITEs();
      //      Assert(iteRewriteAssertionsEnd == d_assertionsToCheck.size());
    }
  }

  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones
#ifdef CVC4_ASSERTIONS
  unsigned iteRewriteAssertionsEnd = d_assertionsToCheck.size();
#endif

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  Debug("smt") << "SmtEnginePrivate::processAssertions() POST SIMPLIFICATION" << endl;
  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  {
    TimerStat::CodeTimer codeTimer(d_smt.d_theoryPreprocessTime);
    // Call the theory preprocessors
    d_smt.d_theoryEngine->preprocessStart();
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      d_assertionsToCheck[i] = d_smt.d_theoryEngine->preprocess(d_assertionsToCheck[i]);
    }
  }

  if(Dump.isOn("assertions")) {
    // Push the simplified assertions to the dump output stream
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      Dump("assertions")
        << AssertCommand(BoolExpr(d_assertionsToCheck[i].toExpr()));
    }
  }

  // Push the formula to decision engine
  if(noConflict) {
    Assert(iteRewriteAssertionsEnd == d_assertionsToCheck.size());
    d_smt.d_decisionEngine->addAssertions
      (d_assertionsToCheck, d_realAssertionsEnd, d_iteSkolemMap);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  // Push the formula to SAT
  {
    TimerStat::CodeTimer codeTimer(d_smt.d_cnfConversionTime);
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      d_smt.d_propEngine->assertFormula(d_assertionsToCheck[i]);
    }
  }

  d_assertionsToCheck.clear();
  d_iteSkolemMap.clear();
}

void SmtEnginePrivate::addFormula(TNode n)
  throw(NoSuchFunctionException, AssertionException) {

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << ")" << endl;

  // Add the normalized formula to the queue
  d_assertionsToPreprocess.push_back(Rewriter::rewrite(n));

  // If the mode of processing is incremental prepreocess and assert immediately
  if (Options::current()->simplificationMode == Options::SIMPLIFICATION_MODE_INCREMENTAL) {
    processAssertions();
  }
}

void SmtEngine::ensureBoolean(const BoolExpr& e) {
  Type type = e.getType(Options::current()->typeChecking);
  Type boolType = d_exprManager->booleanType();
  if(type != boolType) {
    stringstream ss;
    ss << Expr::setlanguage(language::toOutputLanguage(Options::current()->inputLanguage))
       << "Expected " << boolType << "\n"
       << "The assertion : " << e << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(e, ss.str());
  }
}

Result SmtEngine::checkSat(const BoolExpr& e) {

  Assert(e.isNull() || e.getExprManager() == d_exprManager);

  NodeManagerScope nms(d_nodeManager);

  finalOptionsAreSet();

  Trace("smt") << "SmtEngine::checkSat(" << e << ")" << endl;

  if(d_queryMade && !Options::current()->incrementalSolving) {
    throw ModalException("Cannot make multiple queries unless "
                         "incremental solving is enabled "
                         "(try --incremental)");
  }

  // Ensure that the expression is type-checked at this point, and Boolean
  if(!e.isNull()) {
    ensureBoolean(e);
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // Push the context
  internalPush();

  // Note that a query has been made
  d_queryMade = true;

  // Add the formula
  if(!e.isNull()) {
    d_problemExtended = true;
    d_private->addFormula(e.getNode());
  }

  // Run the check
  Result r = check().asSatisfiabilityResult();
  d_needPostsolve = true;

  // Dump the query if requested
  if(Dump.isOn("benchmark")) {
    // the expr already got dumped out if assertion-dumping is on
    Dump("benchmark") << CheckSatCommand();
  }

  // Pop the context
  internalPop();

  // Remember the status
  d_status = r;

  d_problemExtended = false;

  Trace("smt") << "SmtEngine::checkSat(" << e << ") => " << r << endl;

  return r;
}

Result SmtEngine::query(const BoolExpr& e) {

  Assert(!e.isNull());
  Assert(e.getExprManager() == d_exprManager);

  NodeManagerScope nms(d_nodeManager);

  finalOptionsAreSet();

  Trace("smt") << "SMT query(" << e << ")" << endl;

  if(d_queryMade && !Options::current()->incrementalSolving) {
    throw ModalException("Cannot make multiple queries unless "
                         "incremental solving is enabled "
                         "(try --incremental)");
  }

  // Ensure that the expression is type-checked at this point, and Boolean
  ensureBoolean(e);

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // Push the context
  internalPush();

  // Note that a query has been made
  d_queryMade = true;

  // Add the formula
  d_problemExtended = true;
  d_private->addFormula(e.getNode().notNode());

  // Run the check
  Result r = check().asValidityResult();
  d_needPostsolve = true;

  // Dump the query if requested
  if(Dump.isOn("benchmark")) {
    // the expr already got dumped out if assertion-dumping is on
    Dump("benchmark") << CheckSatCommand();
  }

  // Pop the context
  internalPop();

  // Remember the status
  d_status = r;

  d_problemExtended = false;

  Trace("smt") << "SMT query(" << e << ") ==> " << r << endl;

  return r;
}

Result SmtEngine::assertFormula(const BoolExpr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  Trace("smt") << "SmtEngine::assertFormula(" << e << ")" << endl;
  ensureBoolean(e);
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e);
  }
  d_private->addFormula(e.getNode());
  return quickCheck().asValidityResult();
}

Expr SmtEngine::simplify(const Expr& e) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  if( Options::current()->typeChecking ) {
    e.getType(true);// ensure expr is type-checked at this point
  }
  Trace("smt") << "SMT simplify(" << e << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SimplifyCommand(e);
  }
  return d_private->applySubstitutions(e).toExpr();
}

Expr SmtEngine::getValue(const Expr& e)
  throw(ModalException, AssertionException) {
  Assert(e.getExprManager() == d_exprManager);
  NodeManagerScope nms(d_nodeManager);

  // ensure expr is type-checked at this point
  Type type = e.getType(Options::current()->typeChecking);

  Trace("smt") << "SMT getValue(" << e << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetValueCommand(e);
  }
  if(!Options::current()->produceModels) {
    const char* msg =
      "Cannot get value when produce-models options is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::SAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get value unless immediately preceded by SAT/INVALID response.";
    throw ModalException(msg);
  }
  if(type.isFunction() || type.isPredicate() ||
     type.isKind() || type.isSortConstructor()) {
    const char* msg =
      "Cannot get value of a function, predicate, or sort.";
    throw ModalException(msg);
  }

  // Apply what was learned from preprocessing
  Node n = d_private->applySubstitutions(e.getNode());

  // Normalize for the theories
  n = Rewriter::rewrite(n);

  Trace("smt") << "--- getting value of " << n << endl;
  Node resultNode = d_theoryEngine->getValue(n);

  // type-check the result we got
  Assert(resultNode.isNull() || resultNode.getType() == n.getType());
  return Expr(d_exprManager, new Node(resultNode));
}

bool SmtEngine::addToAssignment(const Expr& e) throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  Type type = e.getType(Options::current()->typeChecking);
  // must be Boolean
  CheckArgument( type.isBoolean(), e,
                 "expected Boolean-typed variable or function application "
                 "in addToAssignment()" );
  Node n = e.getNode();
  // must be an APPLY of a zero-ary defined function, or a variable
  CheckArgument( ( ( n.getKind() == kind::APPLY &&
                     ( d_definedFunctions->find(n.getOperator()) !=
                       d_definedFunctions->end() ) &&
                     n.getNumChildren() == 0 ) ||
                   n.getMetaKind() == kind::metakind::VARIABLE ), e,
                 "expected variable or defined-function application "
                 "in addToAssignment(),\ngot %s", e.toString().c_str() );
  if(!Options::current()->produceAssignments) {
    return false;
  }
  if(d_assignments == NULL) {
    d_assignments = new(true) AssignmentSet(d_context);
  }
  d_assignments->insert(n);

  return true;
}

SExpr SmtEngine::getAssignment() throw(ModalException, AssertionException) {
  Trace("smt") << "SMT getAssignment()" << endl;
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssignmentCommand();
  }
  if(!Options::current()->produceAssignments) {
    const char* msg =
      "Cannot get the current assignment when "
      "produce-assignments option is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::SAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get the current assignment unless immediately "
      "preceded by SAT/INVALID response.";
    throw ModalException(msg);
  }

  if(d_assignments == NULL) {
    return SExpr();
  }

  vector<SExpr> sexprs;
  TypeNode boolType = d_nodeManager->booleanType();
  for(AssignmentSet::const_iterator i = d_assignments->begin(),
        iend = d_assignments->end();
      i != iend;
      ++i) {
    Assert((*i).getType() == boolType);

    // Normalize
    Node n = Rewriter::rewrite(*i);

    Trace("smt") << "--- getting value of " << n << endl;
    Node resultNode = d_theoryEngine->getValue(n);

    // type-check the result we got
    Assert(resultNode.isNull() || resultNode.getType() == boolType);

    vector<SExpr> v;
    if((*i).getKind() == kind::APPLY) {
      Assert((*i).getNumChildren() == 0);
      v.push_back((*i).getOperator().toString());
    } else {
      Assert((*i).getMetaKind() == kind::metakind::VARIABLE);
      v.push_back((*i).toString());
    }
    v.push_back(resultNode.toString());
    sexprs.push_back(v);
  }
  return SExpr(sexprs);
}

Proof* SmtEngine::getProof() throw(ModalException, AssertionException) {
  Trace("smt") << "SMT getProof()" << endl;
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetProofCommand();
  }
#ifdef CVC4_PROOF
  if(!Options::current()->proof) {
    const char* msg =
      "Cannot get a proof when produce-proofs option is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::UNSAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get a proof unless immediately preceded by UNSAT/VALID response.";
    throw ModalException(msg);
  }

  return ProofManager::getProof();
#else /* CVC4_PROOF */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* CVC4_PROOF */
}

vector<Expr> SmtEngine::getAssertions()
  throw(ModalException, AssertionException) {
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssertionsCommand();
  }
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!Options::current()->interactive) {
    const char* msg =
      "Cannot query the current assertion list when not in interactive mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

size_t SmtEngine::getStackLevel() const {
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT getStackLevel()" << endl;
  return d_context->getLevel();
}

void SmtEngine::push() {
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  Trace("smt") << "SMT push()" << endl;
  d_private->processAssertions();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PushCommand();
  }
  if(!Options::current()->incrementalSolving) {
    throw ModalException("Cannot push when not solving incrementally (use --incremental)");
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  d_userLevels.push_back(d_userContext->getLevel());
  internalPush();
  Trace("userpushpop") << "SmtEngine: pushed to level "
                       << d_userContext->getLevel() << endl;
}

void SmtEngine::pop() {
  NodeManagerScope nms(d_nodeManager);
  finalOptionsAreSet();
  Trace("smt") << "SMT pop()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PopCommand();
  }
  if(!Options::current()->incrementalSolving) {
    throw ModalException("Cannot pop when not solving incrementally (use --incremental)");
  }
  if(d_userContext->getLevel() == 0) {
    throw ModalException("Cannot pop beyond the first user frame");
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  AlwaysAssert(d_userLevels.size() > 0 && d_userLevels.back() < d_userContext->getLevel());
  while (d_userLevels.back() < d_userContext->getLevel()) {
    internalPop();
  }
  d_userLevels.pop_back();

  // Clear out assertion queues etc., in case anything is still in there
  d_private->notifyPop();

  Trace("userpushpop") << "SmtEngine: popped to level "
                       << d_userContext->getLevel() << endl;
  // FIXME: should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
  // Still, we want the right exit status after any final sequence
  // of pops... hm.
}

void SmtEngine::internalPush() {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPush()" << endl;
  if(Options::current()->incrementalSolving) {
    d_private->processAssertions();
    d_userContext->push();
    d_context->push();
    d_propEngine->push();
  }
}

void SmtEngine::internalPop() {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPop()" << endl;
  if(Options::current()->incrementalSolving) {
    d_propEngine->pop();
    d_context->pop();
    d_userContext->pop();
  }
}

void SmtEngine::interrupt() throw(ModalException) {
  d_propEngine->interrupt();
}

void SmtEngine::setResourceLimit(unsigned long units, bool cumulative) {
  if(cumulative) {
    Trace("limit") << "SmtEngine: setting cumulative resource limit to " << units << endl;
    d_resourceBudgetCumulative = (units == 0) ? 0 : (d_cumulativeResourceUsed + units);
  } else {
    Trace("limit") << "SmtEngine: setting per-call resource limit to " << units << endl;
    d_resourceBudgetPerCall = units;
  }
}

void SmtEngine::setTimeLimit(unsigned long millis, bool cumulative) {
  if(cumulative) {
    Trace("limit") << "SmtEngine: setting cumulative time limit to " << millis << " ms" << endl;
    d_timeBudgetCumulative = (millis == 0) ? 0 : (d_cumulativeTimeUsed + millis);
  } else {
    Trace("limit") << "SmtEngine: setting per-call time limit to " << millis << " ms" << endl;
    d_timeBudgetPerCall = millis;
  }
}

unsigned long SmtEngine::getResourceUsage() const {
  return d_cumulativeResourceUsed;
}

unsigned long SmtEngine::getTimeUsage() const {
  return d_cumulativeTimeUsed;
}

unsigned long SmtEngine::getResourceRemaining() const throw(ModalException) {
  if(d_resourceBudgetCumulative == 0) {
    throw ModalException("No cumulative resource limit is currently set");
  }

  return d_resourceBudgetCumulative <= d_cumulativeResourceUsed ? 0 :
    d_resourceBudgetCumulative - d_cumulativeResourceUsed;
}

unsigned long SmtEngine::getTimeRemaining() const throw(ModalException) {
  if(d_timeBudgetCumulative == 0) {
    throw ModalException("No cumulative time limit is currently set");
  }

  return d_timeBudgetCumulative <= d_cumulativeTimeUsed ? 0 :
    d_timeBudgetCumulative - d_cumulativeTimeUsed;
}

StatisticsRegistry* SmtEngine::getStatisticsRegistry() const {
  return d_exprManager->d_nodeManager->getStatisticsRegistry();
}

}/* CVC4 namespace */
