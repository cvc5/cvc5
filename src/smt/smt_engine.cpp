/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"

#include <algorithm>
#include <cctype>
#include <iterator>
#include <memory>
#include <sstream>
#include <stack>
#include <string>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "api/cvc4cpp.h"
#include "base/check.h"
#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "decision/decision_engine.h"
#include "expr/attribute.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "expr/node_self_iterator.h"
#include "expr/node_visitor.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/open_ostream.h"
#include "options/option_exception.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/prop_options.h"
#include "options/quantifiers_options.h"
#include "options/sep_options.h"
#include "options/set_language.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/theory_options.h"
#include "options/uf_options.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "preprocessing/preprocessing_pass_registry.h"
#include "printer/printer.h"
#include "proof/proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/expr_names.h"
#include "smt/command.h"
#include "smt/defined_function.h"
#include "smt/dump_manager.h"
#include "smt/listeners.h"
#include "smt/logic_request.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/options_manager.h"
#include "smt/process_assertions.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_engine_stats.h"
#include "smt/term_formula_removal.h"
#include "smt/update_ostream.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/nary_builder.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/strings/theory_strings.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "util/hash.h"
#include "util/proof.h"
#include "util/random.h"
#include "util/resource_manager.h"

#if (IS_LFSC_BUILD && IS_PROOFS_BUILD)
#include "lfscc.h"
#endif

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {

namespace proof {
extern const char* const plf_signatures;
}  // namespace proof

namespace smt {

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
class SmtEnginePrivate
{
  SmtEngine& d_smt;

  typedef unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
  typedef unordered_map<Node, bool, NodeHashFunction> NodeToBoolHashMap;

  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;

  /** Assertions in the preprocessing pipeline */
  AssertionPipeline d_assertions;

  /** Whether any assertions have been processed */
  CDO<bool> d_assertionsProcessed;

  // Cached true value
  Node d_true;

  /** The preprocessing pass context */
  std::unique_ptr<PreprocessingPassContext> d_preprocessingPassContext;

  /** Process assertions module */
  ProcessAssertions d_processor;

 public:
  IteSkolemMap& getIteSkolemMap() { return d_assertions.getIteSkolemMap(); }

  /** Instance of the ITE remover */
  RemoveTermFormulas d_iteRemover;

  /* Finishes the initialization of the private portion of SMTEngine. */
  void finishInit();

  /*------------------- sygus utils ------------------*/
  /**
   * sygus variables declared (from "declare-var" and "declare-fun" commands)
   *
   * The SyGuS semantics for declared variables is that they are implicitly
   * universally quantified in the constraints.
   */
  std::vector<Node> d_sygusVars;
  /** sygus constraints */
  std::vector<Node> d_sygusConstraints;
  /** functions-to-synthesize */
  std::vector<Node> d_sygusFunSymbols;
  /**
   * Whether we need to reconstruct the sygus conjecture.
   */
  CDO<bool> d_sygusConjectureStale;
  /*------------------- end of sygus utils ------------------*/

 public:
  SmtEnginePrivate(SmtEngine& smt)
      : d_smt(smt),
        d_propagator(true, true),
        d_assertions(),
        d_assertionsProcessed(smt.getUserContext(), false),
        d_processor(smt, *smt.getResourceManager()),
        d_iteRemover(smt.getUserContext()),
        d_sygusConjectureStale(smt.getUserContext(), true)
  {
    d_true = NodeManager::currentNM()->mkConst(true);
  }

  ~SmtEnginePrivate()
  {
    if(d_propagator.getNeedsFinish()) {
      d_propagator.finish();
      d_propagator.setNeedsFinish(false);
    }
  }

  void spendResource(ResourceManager::Resource r)
  {
    d_smt.getResourceManager()->spendResource(r);
  }

  ProcessAssertions* getProcessAssertions() { return &d_processor; }

  Node applySubstitutions(TNode node)
  {
    return Rewriter::rewrite(
        d_preprocessingPassContext->getTopLevelSubstitutions().apply(node));
  }

  /**
   * Process the assertions that have been asserted.
   */
  void processAssertions();

  /** Process a user push.
  */
  void notifyPush() {

  }

  /**
   * Process a user pop.  Clears out the non-context-dependent stuff in this
   * SmtEnginePrivate.  Necessary to clear out our assertion vectors in case
   * someone does a push-assert-pop without a check-sat. It also pops the
   * last map of expression names from notifyPush.
   */
  void notifyPop() {
    d_assertions.clear();
    d_propagator.getLearnedLiterals().clear();
    getIteSkolemMap().clear();
  }

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   * The arguments isInput and isAssumption are used for bookkeeping for proofs.
   * The argument maybeHasFv should be set to true if the assertion may have
   * free variables. By construction, assertions from the smt2 parser are
   * guaranteed not to have free variables. However, other cases such as
   * assertions from the SyGuS parser may have free variables (say if the
   * input contains an assert or define-fun-rec command).
   *
   * @param isAssumption If true, the formula is considered to be an assumption
   * (this is used to distinguish assertions and assumptions)
   */
  void addFormula(TNode n,
                  bool inUnsatCore,
                  bool inInput = true,
                  bool isAssumption = false,
                  bool maybeHasFv = false);
  /**
   * Simplify node "in" by expanding definitions and applying any
   * substitutions learned from preprocessing.
   */
  Node simplify(TNode in) {
    // Substitute out any abstract values in ex.
    // Expand definitions.
    NodeToNodeHashMap cache;
    Node n = d_processor.expandDefinitions(in, cache).toExpr();
    // Make sure we've done all preprocessing, etc.
    Assert(d_assertions.size() == 0);
    return applySubstitutions(n).toExpr();
  }
};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

SmtEngine::SmtEngine(ExprManager* em, Options* optr)
    : d_context(new Context()),
      d_userContext(new UserContext()),
      d_userLevels(),
      d_exprManager(em),
      d_nodeManager(d_exprManager->getNodeManager()),
      d_absValues(new AbstractValues(d_nodeManager)),
      d_exprNames(new ExprNames(d_userContext.get())),
      d_dumpm(new DumpManager(d_userContext.get())),
      d_routListener(new ResourceOutListener(*this)),
      d_snmListener(new SmtNodeManagerListener(*d_dumpm.get())),
      d_theoryEngine(nullptr),
      d_propEngine(nullptr),
      d_proofManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_definedFunctions(nullptr),
      d_abductSolver(nullptr),
      d_assertionList(nullptr),
      d_assignments(nullptr),
      d_defineCommands(),
      d_logic(),
      d_originalOptions(),
      d_isInternalSubsolver(false),
      d_pendingPops(0),
      d_fullyInited(false),
      d_queryMade(false),
      d_needPostsolve(false),
      d_globalNegation(false),
      d_status(),
      d_expectedStatus(),
      d_smtMode(SMT_MODE_START),
      d_private(nullptr),
      d_statisticsRegistry(nullptr),
      d_stats(nullptr),
      d_resourceManager(nullptr),
      d_scope(nullptr)
{
  // !!!!!!!!!!!!!!!!!!!!!! temporary hack: this makes the current SmtEngine
  // we are constructing the current SmtEngine in scope for the lifetime of
  // this SmtEngine, or until another SmtEngine is constructed (that SmtEngine
  // is then in scope during its lifetime). This is mostly to ensure that
  // options are always in scope, for e.g. printing expressions, which rely
  // on knowing the output language.
  // Notice that the SmtEngine may spawn new SmtEngine "subsolvers" internally.
  // These are created, used, and deleted in a modular fashion while not
  // interleaving calls to the master SmtEngine. Thus the hack here does not
  // break this use case.
  // On the other hand, this hack breaks use cases where multiple SmtEngine
  // objects are created by the user.
  d_scope.reset(new SmtScope(this));
  if (optr != nullptr)
  {
    // if we provided a set of options, copy their values to the options
    // owned by this SmtEngine.
    d_options.copyValues(*optr);
  }
  d_statisticsRegistry.reset(new StatisticsRegistry());
  d_resourceManager.reset(
      new ResourceManager(*d_statisticsRegistry.get(), d_options));
  d_optm.reset(new smt::OptionsManager(&d_options, d_resourceManager.get()));
  d_private.reset(new smt::SmtEnginePrivate(*this));
  // listen to node manager events
  d_nodeManager->subscribeEvents(d_snmListener.get());
  // listen to resource out
  d_resourceManager->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SmtEngineStatistics());
  
  // The ProofManager is constructed before any other proof objects such as
  // SatProof and TheoryProofs. The TheoryProofEngine and the SatProof are
  // initialized in TheoryEngine and PropEngine respectively.
  Assert(d_proofManager == nullptr);

  // d_proofManager must be created before Options has been finished
  // being parsed from the input file. Because of this, we cannot trust
  // that options::proof() is set correctly yet.
#ifdef CVC4_PROOF
  d_proofManager.reset(new ProofManager(getUserContext()));
#endif

  d_definedFunctions = new (true) DefinedFunctionMap(getUserContext());
}

void SmtEngine::finishInit()
{
  // Notice that finishInit is called when options are finalized. If we are
  // parsing smt2, this occurs at the moment we enter "Assert mode", page 52
  // of SMT-LIB 2.6 standard.

  // set the random seed
  Random::getRandom().setSeed(options::seed());

  // Call finish init on the options manager. This inializes the resource
  // manager based on the options, and sets up the best default options
  // based on our heuristics.
  d_optm->finishInit(d_logic, d_isInternalSubsolver);

  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine.reset(new TheoryEngine(getContext(),
                                        getUserContext(),
                                        getResourceManager(),
                                        d_private->d_iteRemover,
                                        const_cast<const LogicInfo&>(d_logic)));

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(getTheoryEngine(), id);
    //register with proof engine if applicable
#ifdef CVC4_PROOF
    ProofManager::currentPM()->getTheoryProofEngine()->registerTheory(d_theoryEngine->theoryOf(id));
#endif
  }

  Trace("smt-debug") << "Making decision engine..." << std::endl;

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  /* force destruction of referenced PropEngine to enforce that statistics
   * are unregistered by the obsolete PropEngine object before registered
   * again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new PropEngine(
      getTheoryEngine(), getContext(), getUserContext(), getResourceManager()));

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(getPropEngine());
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_userContext->push();
  d_context->push();

  Trace("smt-debug") << "Set up assertion list..." << std::endl;
  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(options::produceAssertions() ||
     options::incrementalSolving()) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new (true) AssertionList(getUserContext());
    d_globalDefineFunRecLemmas.reset(new std::vector<Node>());
  }

  // dump out a set-logic command only when raw-benchmark is disabled to avoid
  // dumping the command twice.
  if (Dump.isOn("benchmark") && !Dump.isOn("raw-benchmark"))
  {
      LogicInfo everything;
      everything.lock();
      Dump("benchmark") << CommentCommand(
          "CVC4 always dumps the most general, all-supported logic (below), as "
          "some internals might require the use of a logic more general than "
          "the input.")
                        << SetBenchmarkLogicCommand(
                               everything.getLogicString());
  }

  // initialize the dump manager
  d_dumpm->finishInit();

  // subsolvers
  if (options::produceAbducts())
  {
    d_abductSolver.reset(new AbductionSolver(this));
  }

  PROOF( ProofManager::currentPM()->setLogic(d_logic); );
  PROOF({
      for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
        ProofManager::currentPM()->getTheoryProofEngine()->
          finishRegisterTheory(d_theoryEngine->theoryOf(id));
      }
    });
  d_private->finishInit();
  Trace("smt-debug") << "SmtEngine::finishInit done" << std::endl;
}

void SmtEngine::finalOptionsAreSet() {
  if(d_fullyInited) {
    return;
  }

  if(! d_logic.isLocked()) {
    setLogicInternal();
  }

  // finish initialization, create the prop engine, etc.
  finishInit();

  AlwaysAssert(d_propEngine->getAssertionLevel() == 0)
      << "The PropEngine has pushed but the SmtEngine "
         "hasn't finished initializing!";

  d_fullyInited = true;
  Assert(d_logic.isLocked());
}

void SmtEngine::shutdown() {
  doPendingPops();

  while(options::incrementalSolving() && d_userContext->getLevel() > 1) {
    internalPop(true);
  }

  if (d_propEngine != nullptr)
  {
    d_propEngine->shutdown();
  }
  if (d_theoryEngine != nullptr)
  {
    d_theoryEngine->shutdown();
  }
}

SmtEngine::~SmtEngine()
{
  SmtScope smts(this);

  try {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_context->popto(0);
    d_userContext->popto(0);

    if(d_assignments != NULL) {
      d_assignments->deleteSelf();
    }

    d_globalDefineFunRecLemmas.reset();

    if(d_assertionList != NULL) {
      d_assertionList->deleteSelf();
    }

    d_definedFunctions->deleteSelf();

    //destroy all passes before destroying things that they refer to
    d_private->getProcessAssertions()->cleanup();

    // d_proofManager is always created when proofs are enabled at configure
    // time.  Because of this, this code should not be wrapped in PROOF() which
    // additionally checks flags such as options::proof().
    //
    // Note: the proof manager must be destroyed before the theory engine.
    // Because the destruction of the proofs depends on contexts owned be the
    // theory solvers.
#ifdef CVC4_PROOF
    d_proofManager.reset(nullptr);
#endif

    d_absValues.reset(nullptr);
    d_exprNames.reset(nullptr);
    d_dumpm.reset(nullptr);

    d_theoryEngine.reset(nullptr);
    d_propEngine.reset(nullptr);

    d_stats.reset(nullptr);
    d_private.reset(nullptr);
    d_nodeManager->unsubscribeEvents(d_snmListener.get());
    d_snmListener.reset(nullptr);
    d_routListener.reset(nullptr);
    d_optm.reset(nullptr);
    // d_resourceManager must be destroyed before d_statisticsRegistry
    d_resourceManager.reset(nullptr);
    d_statisticsRegistry.reset(nullptr);


    d_userContext.reset(nullptr);
    d_context.reset(nullptr);
  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << endl
              << e << endl;
  }
}

void SmtEngine::setLogic(const LogicInfo& logic)
{
  SmtScope smts(this);
  if(d_fullyInited) {
    throw ModalException("Cannot set logic in SmtEngine after the engine has "
                         "finished initializing.");
  }
  d_logic = logic;
  d_userLogic = logic;
  setLogicInternal();
}

void SmtEngine::setLogic(const std::string& s)
{
  SmtScope smts(this);
  try
  {
    setLogic(LogicInfo(s));
    // dump out a set-logic command
    if (Dump.isOn("raw-benchmark"))
    {
      Dump("raw-benchmark")
          << SetBenchmarkLogicCommand(d_logic.getLogicString());
    }
  }
  catch (IllegalArgumentException& e)
  {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) { setLogic(string(logic)); }
LogicInfo SmtEngine::getLogicInfo() const {
  return d_logic;
}

LogicInfo SmtEngine::getUserLogicInfo() const
{
  // Lock the logic to make sure that this logic can be queried. We create a
  // copy of the user logic here to keep this method const.
  LogicInfo res = d_userLogic;
  res.lock();
  return res;
}

void SmtEngine::notifyStartParsing(std::string filename)
{
  d_filename = filename;

  // Copy the original options. This is called prior to beginning parsing.
  // Hence reset should revert to these options, which note is after reading
  // the command line.
  d_originalOptions.copyValues(d_options);
}

std::string SmtEngine::getFilename() const { return d_filename; }
void SmtEngine::setLogicInternal()
{
  Assert(!d_fullyInited)
      << "setting logic in SmtEngine but the engine has already"
         " finished initializing for this run";
  d_logic.lock();
  d_userLogic.lock();
}

void SmtEngine::setProblemExtended()
{
  d_smtMode = SMT_MODE_ASSERT;
  d_assumptions.clear();
}

void SmtEngine::setInfo(const std::string& key, const CVC4::SExpr& value)
{
  SmtScope smts(this);

  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    if(key == "status") {
      string s = value.getValue();
      BenchmarkStatus status =
        (s == "sat") ? SMT_SATISFIABLE :
          ((s == "unsat") ? SMT_UNSATISFIABLE : SMT_UNKNOWN);
      Dump("benchmark") << SetBenchmarkStatusCommand(status);
    } else {
      Dump("benchmark") << SetInfoCommand(key, value);
    }
  }

  // Check for standard info keys (SMT-LIB v1, SMT-LIB v2, ...)
  if (key == "source" || key == "category" || key == "difficulty"
      || key == "notes" || key == "name" || key == "license")
  {
    // ignore these
    return;
  }
  else if (key == "filename")
  {
    d_filename = value.getValue();
    return;
  }
  else if (key == "smt-lib-version" && !options::inputLanguage.wasSetByUser())
  {
    language::input::Language ilang = language::input::LANG_AUTO;
    if( (value.isInteger() && value.getIntegerValue() == Integer(2)) ||
        (value.isRational() && value.getRationalValue() == Rational(2)) ||
        value.getValue() == "2" ||
        value.getValue() == "2.0" ) {
      ilang = language::input::LANG_SMTLIB_V2_0;
    } else if( (value.isRational() && value.getRationalValue() == Rational(5, 2)) ||
               value.getValue() == "2.5" ) {
      ilang = language::input::LANG_SMTLIB_V2_5;
    } else if( (value.isRational() && value.getRationalValue() == Rational(13, 5)) ||
               value.getValue() == "2.6" ) {
      ilang = language::input::LANG_SMTLIB_V2_6;
    }
    else
    {
      Warning() << "Warning: unsupported smt-lib-version: " << value << endl;
      throw UnrecognizedOptionException();
    }
    options::inputLanguage.set(ilang);
    // also update the output language
    if (!options::outputLanguage.wasSetByUser())
    {
      language::output::Language olang = language::toOutputLanguage(ilang);
      if (options::outputLanguage() != olang)
      {
        options::outputLanguage.set(olang);
        *options::out() << language::SetLanguage(olang);
      }
    }
    return;
  } else if(key == "status") {
    string s;
    if(value.isAtom()) {
      s = value.getValue();
    }
    if(s != "sat" && s != "unsat" && s != "unknown") {
      throw OptionException("argument to (set-info :status ..) must be "
                            "`sat' or `unsat' or `unknown'");
    }
    d_expectedStatus = Result(s, d_filename);
    return;
  }
  throw UnrecognizedOptionException();
}

bool SmtEngine::isValidGetInfoFlag(const std::string& key) const
{
  if (key == "all-statistics" || key == "error-behavior" || key == "name"
      || key == "version" || key == "authors" || key == "status"
      || key == "reason-unknown" || key == "assertion-stack-levels"
      || key == "all-options")
  {
    return true;
  }
  return false;
}

CVC4::SExpr SmtEngine::getInfo(const std::string& key) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if (!isValidGetInfoFlag(key))
  {
    throw UnrecognizedOptionException();
  }
  if (key == "all-statistics")
  {
    vector<SExpr> stats;
    for (StatisticsRegistry::const_iterator i =
             NodeManager::fromExprManager(d_exprManager)
                 ->getStatisticsRegistry()
                 ->begin();
         i
         != NodeManager::fromExprManager(d_exprManager)
                ->getStatisticsRegistry()
                ->end();
         ++i)
    {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    for (StatisticsRegistry::const_iterator i = d_statisticsRegistry->begin();
         i != d_statisticsRegistry->end();
         ++i)
    {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    return SExpr(stats);
  }
  if (key == "error-behavior")
  {
    return SExpr(SExpr::Keyword("immediate-exit"));
  }
  if (key == "name")
  {
    return SExpr(Configuration::getName());
  }
  if (key == "version")
  {
    return SExpr(Configuration::getVersionString());
  }
  if (key == "authors")
  {
    return SExpr(Configuration::about());
  }
  if (key == "status")
  {
    // sat | unsat | unknown
    switch (d_status.asSatisfiabilityResult().isSat())
    {
      case Result::SAT: return SExpr(SExpr::Keyword("sat"));
      case Result::UNSAT: return SExpr(SExpr::Keyword("unsat"));
      default: return SExpr(SExpr::Keyword("unknown"));
    }
  }
  if (key == "reason-unknown")
  {
    if (!d_status.isNull() && d_status.isUnknown())
    {
      stringstream ss;
      ss << d_status.whyUnknown();
      string s = ss.str();
      transform(s.begin(), s.end(), s.begin(), ::tolower);
      return SExpr(SExpr::Keyword(s));
    }
    else
    {
      throw RecoverableModalException(
          "Can't get-info :reason-unknown when the "
          "last result wasn't unknown!");
    }
  }
  if (key == "assertion-stack-levels")
  {
    AlwaysAssert(d_userLevels.size()
                 <= std::numeric_limits<unsigned long int>::max());
    return SExpr(static_cast<unsigned long int>(d_userLevels.size()));
  }
  Assert(key == "all-options");
  // get the options, like all-statistics
  std::vector<std::vector<std::string>> current_options =
      Options::current()->getOptions();
  return SExpr::parseListOfListOfAtoms(current_options);
}

void SmtEngine::debugCheckFormals(const std::vector<Expr>& formals, Expr func)
{
  for(std::vector<Expr>::const_iterator i = formals.begin(); i != formals.end(); ++i) {
    if((*i).getKind() != kind::BOUND_VARIABLE) {
      stringstream ss;
      ss << "All formal arguments to defined functions must be BOUND_VARIABLEs, but in the\n"
         << "definition of function " << func << ", formal\n"
         << "  " << *i << "\n"
         << "has kind " << (*i).getKind();
      throw TypeCheckingException(func, ss.str());
    }
  }
}

void SmtEngine::debugCheckFunctionBody(Expr formula,
                                       const std::vector<Expr>& formals,
                                       Expr func)
{
  Type formulaType = formula.getType(options::typeChecking());
  Type funcType = func.getType();
  // We distinguish here between definitions of constants and functions,
  // because the type checking for them is subtly different.  Perhaps we
  // should instead have SmtEngine::defineFunction() and
  // SmtEngine::defineConstant() for better clarity, although then that
  // doesn't match the SMT-LIBv2 standard...
  if(formals.size() > 0) {
    Type rangeType = FunctionType(funcType).getRangeType();
    if(! formulaType.isComparableTo(rangeType)) {
      stringstream ss;
      ss << "Type of defined function does not match its declaration\n"
         << "The function  : " << func << "\n"
         << "Declared type : " << rangeType << "\n"
         << "The body      : " << formula << "\n"
         << "Body type     : " << formulaType;
      throw TypeCheckingException(func, ss.str());
    }
  } else {
    if(! formulaType.isComparableTo(funcType)) {
      stringstream ss;
      ss << "Declared type of defined constant does not match its definition\n"
         << "The constant   : " << func << "\n"
         << "Declared type  : " << funcType << " " << Type::getTypeNode(funcType)->getId() << "\n"
         << "The definition : " << formula << "\n"
         << "Definition type: " << formulaType << " " << Type::getTypeNode(formulaType)->getId();
      throw TypeCheckingException(func, ss.str());
    }
  }
}

void SmtEngine::defineFunction(Expr func,
                               const std::vector<Expr>& formals,
                               Expr formula,
                               bool global)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  stringstream ss;
  ss << language::SetLanguage(
            language::SetLanguage::getLanguage(Dump.getStream()))
     << func;
  DefineFunctionCommand c(ss.str(), func, formals, formula, global);
  d_dumpm->addToModelCommandAndDump(
      c, ExprManager::VAR_FLAG_DEFINED, true, "declarations");

  PROOF(if (options::checkUnsatCores()) {
    d_defineCommands.push_back(c.clone());
  });

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  // Substitute out any abstract values in formula
  Node formNode = d_absValues->substituteAbstractValues(Node::fromExpr(formula));

  TNode funcNode = func.getTNode();
  vector<Node> formalsNodes;
  for(vector<Expr>::const_iterator i = formals.begin(),
        iend = formals.end();
      i != iend;
      ++i) {
    formalsNodes.push_back((*i).getNode());
  }
  DefinedFunction def(funcNode, formalsNodes, formNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  Debug("smt") << "definedFunctions insert " << funcNode << " " << formNode << endl;

  if (global)
  {
    d_definedFunctions->insertAtContextLevelZero(funcNode, def);
  }
  else
  {
    d_definedFunctions->insert(funcNode, def);
  }
}

void SmtEngine::defineFunctionsRec(
    const std::vector<Expr>& funcs,
    const std::vector<std::vector<Expr>>& formals,
    const std::vector<Expr>& formulas,
    bool global)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT defineFunctionsRec(...)" << endl;

  if (funcs.size() != formals.size() && funcs.size() != formulas.size())
  {
    stringstream ss;
    ss << "Number of functions, formals, and function bodies passed to "
          "defineFunctionsRec do not match:"
       << "\n"
       << "        #functions : " << funcs.size() << "\n"
       << "        #arg lists : " << formals.size() << "\n"
       << "  #function bodies : " << formulas.size() << "\n";
    throw ModalException(ss.str());
  }
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    // check formal argument list
    debugCheckFormals(formals[i], funcs[i]);
    // type check body
    debugCheckFunctionBody(formulas[i], formals[i], funcs[i]);
  }

  if (Dump.isOn("raw-benchmark"))
  {
    std::vector<api::Term> tFuncs = api::exprVectorToTerms(d_solver, funcs);
    std::vector<std::vector<api::Term>> tFormals;
    for (const std::vector<Expr>& formal : formals)
    {
      tFormals.emplace_back(api::exprVectorToTerms(d_solver, formal));
    }
    std::vector<api::Term> tFormulas =
        api::exprVectorToTerms(d_solver, formulas);
    Dump("raw-benchmark") << DefineFunctionRecCommand(
        d_solver, tFuncs, tFormals, tFormulas, global);
  }

  ExprManager* em = getExprManager();
  bool maybeHasFv = language::isInputLangSygus(options::inputLanguage());
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    // we assert a quantified formula
    Expr func_app;
    // make the function application
    if (formals[i].empty())
    {
      // it has no arguments
      func_app = funcs[i];
    }
    else
    {
      std::vector<Expr> children;
      children.push_back(funcs[i]);
      children.insert(children.end(), formals[i].begin(), formals[i].end());
      func_app = em->mkExpr(kind::APPLY_UF, children);
    }
    Expr lem = em->mkExpr(kind::EQUAL, func_app, formulas[i]);
    if (!formals[i].empty())
    {
      // set the attribute to denote this is a function definition
      std::string attr_name("fun-def");
      Expr aexpr = em->mkExpr(kind::INST_ATTRIBUTE, func_app);
      aexpr = em->mkExpr(kind::INST_PATTERN_LIST, aexpr);
      std::vector<Expr> expr_values;
      std::string str_value;
      setUserAttribute(attr_name, func_app, expr_values, str_value);
      // make the quantified formula
      Expr boundVars = em->mkExpr(kind::BOUND_VAR_LIST, formals[i]);
      lem = em->mkExpr(kind::FORALL, boundVars, lem, aexpr);
    }
    // assert the quantified formula
    //   notice we don't call assertFormula directly, since this would
    //   duplicate the output on raw-benchmark.
    Node n = d_absValues->substituteAbstractValues(Node::fromExpr(lem));
    if (d_assertionList != nullptr)
    {
      d_assertionList->push_back(n);
    }
    if (global && d_globalDefineFunRecLemmas != nullptr)
    {
      // Global definitions are asserted at check-sat-time because we have to
      // make sure that they are always present
      Assert(!language::isInputLangSygus(options::inputLanguage()));
      d_globalDefineFunRecLemmas->emplace_back(n);
    }
    else
    {
      d_private->addFormula(n, false, true, false, maybeHasFv);
    }
  }
}

void SmtEngine::defineFunctionRec(Expr func,
                                  const std::vector<Expr>& formals,
                                  Expr formula,
                                  bool global)
{
  std::vector<Expr> funcs;
  funcs.push_back(func);
  std::vector<std::vector<Expr> > formals_multi;
  formals_multi.push_back(formals);
  std::vector<Expr> formulas;
  formulas.push_back(formula);
  defineFunctionsRec(funcs, formals_multi, formulas, global);
}

bool SmtEngine::isDefinedFunction( Expr func ){
  Node nf = Node::fromExpr( func );
  Debug("smt") << "isDefined function " << nf << "?" << std::endl;
  return d_definedFunctions->find(nf) != d_definedFunctions->end();
}

void SmtEnginePrivate::finishInit()
{
  d_preprocessingPassContext.reset(
      new PreprocessingPassContext(&d_smt, &d_iteRemover, &d_propagator));

  // initialize the preprocessing passes
  d_processor.finishInit(d_preprocessingPassContext.get());
}

Result SmtEngine::check() {
  Assert(d_fullyInited);
  Assert(d_pendingPops == 0);

  Trace("smt") << "SmtEngine::check()" << endl;


  if (d_resourceManager->out())
  {
    Result::UnknownExplanation why = d_resourceManager->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::ENTAILMENT_UNKNOWN, why, d_filename);
  }
  d_resourceManager->beginCall();

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  d_private->processAssertions();
  Trace("smt") << "SmtEngine::check(): done processing assertions" << endl;

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  d_resourceManager->endCall();
  Trace("limit") << "SmtEngine::check(): cumulative millis "
                 << d_resourceManager->getTimeUsage() << ", resources "
                 << d_resourceManager->getResourceUsage() << endl;

  return Result(result, d_filename);
}

Result SmtEngine::quickCheck() {
  Assert(d_fullyInited);
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(
      Result::ENTAILMENT_UNKNOWN, Result::REQUIRES_FULL_CHECK, d_filename);
}

theory::TheoryModel* SmtEngine::getAvailableModel(const char* c) const
{
  if (!options::assignFunctionValues())
  {
    std::stringstream ss;
    ss << "Cannot " << c << " when --assign-function-values is false.";
    throw RecoverableModalException(ss.str().c_str());
  }

  if (d_smtMode != SMT_MODE_SAT && d_smtMode != SMT_MODE_SAT_UNKNOWN)
  {
    std::stringstream ss;
    ss << "Cannot " << c
       << " unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN "
          "response.";
    throw RecoverableModalException(ss.str().c_str());
  }

  if (!options::produceModels())
  {
    std::stringstream ss;
    ss << "Cannot " << c << " when produce-models options is off.";
    throw ModalException(ss.str().c_str());
  }

  TheoryModel* m = d_theoryEngine->getBuiltModel();

  if (m == nullptr)
  {
    std::stringstream ss;
    ss << "Cannot " << c
       << " since model is not available. Perhaps the most recent call to "
          "check-sat was interupted?";
    throw RecoverableModalException(ss.str().c_str());
  }

  return m;
}

void SmtEnginePrivate::processAssertions() {
  TimerStat::CodeTimer paTimer(d_smt.d_stats->d_processAssertionsTime);
  spendResource(ResourceManager::Resource::PreprocessStep);
  Assert(d_smt.d_fullyInited);
  Assert(d_smt.d_pendingPops == 0);

  if (d_assertions.size() == 0) {
    // nothing to do
    return;
  }
  if (d_assertionsProcessed && options::incrementalSolving()) {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    d_assertions.enableStoreSubstsInAsserts();
  }
  else
  {
    d_assertions.disableStoreSubstsInAsserts();
  }

  // process the assertions
  bool noConflict = d_processor.apply(d_assertions);

  //notify theory engine new preprocessed assertions
  d_smt.d_theoryEngine->notifyPreprocessedAssertions( d_assertions.ref() );

  // Push the formula to decision engine
  if (noConflict)
  {
    Chat() << "pushing to decision engine..." << endl;
    d_smt.d_propEngine->addAssertionsToDecisionEngine(d_assertions);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  // if incremental, compute which variables are assigned
  if (options::incrementalSolving())
  {
    d_preprocessingPassContext->recordSymbolsInAssertions(d_assertions.ref());
  }

  // Push the formula to SAT
  {
    Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_cnfConversionTime);
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      Chat() << "+ " << d_assertions[i] << std::endl;
      d_smt.d_propEngine->assertFormula(d_assertions[i]);
    }
  }

  d_assertionsProcessed = true;

  d_assertions.clear();
  getIteSkolemMap().clear();
}

void SmtEnginePrivate::addFormula(
    TNode n, bool inUnsatCore, bool inInput, bool isAssumption, bool maybeHasFv)
{
  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n
               << "), inUnsatCore = " << inUnsatCore
               << ", inInput = " << inInput
               << ", isAssumption = " << isAssumption << endl;

  // Ensure that it does not contain free variables
  if (maybeHasFv)
  {
    if (expr::hasFreeVar(n))
    {
      std::stringstream se;
      se << "Cannot process assertion with free variable.";
      if (language::isInputLangSygus(options::inputLanguage()))
      {
        // Common misuse of SyGuS is to use top-level assert instead of
        // constraint when defining the synthesis conjecture.
        se << " Perhaps you meant `constraint` instead of `assert`?";
      }
      throw ModalException(se.str().c_str());
    }
  }

  // Give it to proof manager
  PROOF(
    if( inInput ){
      // n is an input assertion
      if (inUnsatCore || options::unsatCores() || options::dumpUnsatCores() || options::checkUnsatCores() || options::fewerPreprocessingHoles()) {

        ProofManager::currentPM()->addCoreAssertion(n.toExpr());
      }
    }else{
      // n is the result of an unknown preprocessing step, add it to dependency map to null
      ProofManager::currentPM()->addDependence(n, Node::null());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n, isAssumption);
  //d_assertions.push_back(Rewriter::rewrite(n));
}

void SmtEngine::ensureBoolean(const Node& n)
{
  TypeNode type = n.getType(options::typeChecking());
  TypeNode boolType = NodeManager::currentNM()->booleanType();
  if(type != boolType) {
    stringstream ss;
    ss << "Expected " << boolType << "\n"
       << "The assertion : " << n << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(n.toExpr(), ss.str());
  }
}

Result SmtEngine::checkSat(const Expr& assumption, bool inUnsatCore)
{
  Dump("benchmark") << CheckSatCommand(assumption);
  return checkSatisfiability(assumption, inUnsatCore, false);
}

Result SmtEngine::checkSat(const vector<Expr>& assumptions, bool inUnsatCore)
{
  if (assumptions.empty())
  {
    Dump("benchmark") << CheckSatCommand();
  }
  else
  {
    Dump("benchmark") << CheckSatAssumingCommand(assumptions);
  }

  return checkSatisfiability(assumptions, inUnsatCore, false);
}

Result SmtEngine::checkEntailed(const Expr& expr, bool inUnsatCore)
{
  Dump("benchmark") << QueryCommand(expr, inUnsatCore);
  return checkSatisfiability(
             expr.isNull() ? std::vector<Expr>() : std::vector<Expr>{expr},
             inUnsatCore,
             true)
      .asEntailmentResult();
}

Result SmtEngine::checkEntailed(const vector<Expr>& exprs, bool inUnsatCore)
{
  return checkSatisfiability(exprs, inUnsatCore, true).asEntailmentResult();
}

Result SmtEngine::checkSatisfiability(const Expr& expr,
                                      bool inUnsatCore,
                                      bool isEntailmentCheck)
{
  return checkSatisfiability(
      expr.isNull() ? std::vector<Expr>() : std::vector<Expr>{expr},
      inUnsatCore,
      isEntailmentCheck);
}

Result SmtEngine::checkSatisfiability(const vector<Expr>& assumptions,
                                      bool inUnsatCore,
                                      bool isEntailmentCheck)
{
  try
  {
    SmtScope smts(this);
    finalOptionsAreSet();
    doPendingPops();

    Trace("smt") << "SmtEngine::"
                 << (isEntailmentCheck ? "checkEntailed" : "checkSat") << "("
                 << assumptions << ")" << endl;

    if(d_queryMade && !options::incrementalSolving()) {
      throw ModalException("Cannot make multiple queries unless "
                           "incremental solving is enabled "
                           "(try --incremental)");
    }

    // Note that a query has been made
    d_queryMade = true;
    // reset global negation
    d_globalNegation = false;

    bool didInternalPush = false;

    setProblemExtended();

    if (isEntailmentCheck)
    {
      size_t size = assumptions.size();
      if (size > 1)
      {
        /* Assume: not (BIGAND assumptions)  */
        d_assumptions.push_back(
            d_exprManager->mkExpr(kind::AND, assumptions).notExpr());
      }
      else if (size == 1)
      {
        /* Assume: not expr  */
        d_assumptions.push_back(assumptions[0].notExpr());
      }
    }
    else
    {
      /* Assume: BIGAND assumptions  */
      d_assumptions = assumptions;
    }

    if (!d_assumptions.empty())
    {
      internalPush();
      didInternalPush = true;
    }

    Result r(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    for (Expr e : d_assumptions)
    {
      // Substitute out any abstract values in ex.
      Node n = d_absValues->substituteAbstractValues(Node::fromExpr(e));
      // Ensure expr is type-checked at this point.
      ensureBoolean(n);

      /* Add assumption  */
      if (d_assertionList != NULL)
      {
        d_assertionList->push_back(n);
      }
      d_private->addFormula(n, inUnsatCore, true, true);
    }

    if (d_globalDefineFunRecLemmas != nullptr)
    {
      // Global definitions are asserted at check-sat-time because we have to
      // make sure that they are always present (they are essentially level
      // zero assertions)
      for (const Node& lemma : *d_globalDefineFunRecLemmas)
      {
        d_private->addFormula(lemma, false, true, false, false);
      }
    }

    r = check();

    if ((options::solveRealAsInt() || options::solveIntAsBV() > 0)
        && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    }
    // flipped if we did a global negation
    if (d_globalNegation)
    {
      Trace("smt") << "SmtEngine::process global negate " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        r = Result(Result::SAT);
      }
      else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        // only if satisfaction complete
        if (d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV))
        {
          r = Result(Result::UNSAT);
        }
        else
        {
          r = Result(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
        }
      }
      Trace("smt") << "SmtEngine::global negate returned " << r << std::endl;
    }

    d_needPostsolve = true;

    // Pop the context
    if (didInternalPush)
    {
      internalPop();
    }

    // Remember the status
    d_status = r;
    // Check against expected status
    if (!d_expectedStatus.isUnknown() && !d_status.isUnknown()
        && d_status != d_expectedStatus)
    {
      CVC4_FATAL() << "Expected result " << d_expectedStatus << " but got "
                   << d_status;
    }
    d_expectedStatus = Result();
    // Update the SMT mode
    if (d_status.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      d_smtMode = SMT_MODE_UNSAT;
    }
    else if (d_status.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      d_smtMode = SMT_MODE_SAT;
    }
    else
    {
      d_smtMode = SMT_MODE_SAT_UNKNOWN;
    }

    Trace("smt") << "SmtEngine::" << (isEntailmentCheck ? "query" : "checkSat")
                 << "(" << assumptions << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if(options::checkModels()) {
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if(options::checkProofs()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        checkProof();
      }
    }
    // Check that UNSAT results generate an unsat core correctly.
    if(options::checkUnsatCores()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
        checkUnsatCore();
      }
    }

    return r;
  } catch (UnsafeInterruptException& e) {
    AlwaysAssert(d_resourceManager->out());
    Result::UnknownExplanation why = d_resourceManager->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::SAT_UNKNOWN, why, d_filename);
  }
}

vector<Expr> SmtEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  SmtScope smts(this);
  if (!options::unsatAssumptions())
  {
    throw ModalException(
        "Cannot get unsat assumptions when produce-unsat-assumptions option "
        "is off.");
  }
  if (d_smtMode != SMT_MODE_UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get unsat assumptions unless immediately preceded by "
        "UNSAT/ENTAILED.");
  }
  finalOptionsAreSet();
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << GetUnsatAssumptionsCommand();
  }
  UnsatCore core = getUnsatCoreInternal();
  vector<Expr> res;
  for (const Expr& e : d_assumptions)
  {
    if (find(core.begin(), core.end(), e) != core.end()) { res.push_back(e); }
  }
  return res;
}

Result SmtEngine::assertFormula(const Node& formula, bool inUnsatCore)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();

  Trace("smt") << "SmtEngine::assertFormula(" << formula << ")" << endl;

  if (Dump.isOn("raw-benchmark")) {
    Dump("raw-benchmark") << AssertCommand(formula.toExpr());
  }

  // Substitute out any abstract values in ex
  Node n = d_absValues->substituteAbstractValues(formula);

  ensureBoolean(n);
  if(d_assertionList != NULL) {
    d_assertionList->push_back(n);
  }
  bool maybeHasFv = language::isInputLangSygus(options::inputLanguage());
  d_private->addFormula(n, inUnsatCore, true, false, maybeHasFv);
  return quickCheck().asEntailmentResult();
}/* SmtEngine::assertFormula() */

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SmtEngine::declareSygusVar(const std::string& id, Expr var, Type type)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  d_private->d_sygusVars.push_back(Node::fromExpr(var));
  Trace("smt") << "SmtEngine::declareSygusVar: " << var << "\n";
  Dump("raw-benchmark") << DeclareSygusVarCommand(id, var, type);
  // don't need to set that the conjecture is stale
}

void SmtEngine::declareSygusFunctionVar(const std::string& id,
                                        Expr var,
                                        Type type)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  d_private->d_sygusVars.push_back(Node::fromExpr(var));
  Trace("smt") << "SmtEngine::declareSygusFunctionVar: " << var << "\n";
  Dump("raw-benchmark") << DeclareSygusVarCommand(id, var, type);

  // don't need to set that the conjecture is stale
}

void SmtEngine::declareSynthFun(const std::string& id,
                                Expr func,
                                Type sygusType,
                                bool isInv,
                                const std::vector<Expr>& vars)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Node fn = Node::fromExpr(func);
  d_private->d_sygusFunSymbols.push_back(fn);
  if (!vars.empty())
  {
    Expr bvl = d_exprManager->mkExpr(kind::BOUND_VAR_LIST, vars);
    std::vector<Expr> attr_val_bvl;
    attr_val_bvl.push_back(bvl);
    setUserAttribute("sygus-synth-fun-var-list", func, attr_val_bvl, "");
  }
  // whether sygus type encodes syntax restrictions
  if (sygusType.isDatatype()
      && static_cast<DatatypeType>(sygusType).getDatatype().isSygus())
  {
    TypeNode stn = TypeNode::fromType(sygusType);
    Node sym = d_nodeManager->mkBoundVar("sfproxy", stn);
    std::vector<Expr> attr_value;
    attr_value.push_back(sym.toExpr());
    setUserAttribute("sygus-synth-grammar", func, attr_value, "");
  }
  Trace("smt") << "SmtEngine::declareSynthFun: " << func << "\n";
  Dump("raw-benchmark") << SynthFunCommand(id, func, sygusType, isInv, vars);
  // sygus conjecture is now stale
  setSygusConjectureStale();
}

void SmtEngine::assertSygusConstraint(const Node& constraint)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  d_private->d_sygusConstraints.push_back(constraint);

  Trace("smt") << "SmtEngine::assertSygusConstrant: " << constraint << "\n";
  Dump("raw-benchmark") << SygusConstraintCommand(constraint.toExpr());
  // sygus conjecture is now stale
  setSygusConjectureStale();
}

void SmtEngine::assertSygusInvConstraint(const Expr& inv,
                                         const Expr& pre,
                                         const Expr& trans,
                                         const Expr& post)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  // build invariant constraint

  // get variables (regular and their respective primed versions)
  std::vector<Node> terms, vars, primed_vars;
  terms.push_back(Node::fromExpr(inv));
  terms.push_back(Node::fromExpr(pre));
  terms.push_back(Node::fromExpr(trans));
  terms.push_back(Node::fromExpr(post));
  // variables are built based on the invariant type
  FunctionType t = static_cast<FunctionType>(inv.getType());
  std::vector<Type> argTypes = t.getArgTypes();
  for (const Type& ti : argTypes)
  {
    TypeNode tn = TypeNode::fromType(ti);
    vars.push_back(d_nodeManager->mkBoundVar(tn));
    d_private->d_sygusVars.push_back(vars.back());
    std::stringstream ss;
    ss << vars.back() << "'";
    primed_vars.push_back(d_nodeManager->mkBoundVar(ss.str(), tn));
    d_private->d_sygusVars.push_back(primed_vars.back());
  }

  // make relevant terms; 0 -> Inv, 1 -> Pre, 2 -> Trans, 3 -> Post
  for (unsigned i = 0; i < 4; ++i)
  {
    Node op = terms[i];
    Trace("smt-debug") << "Make inv-constraint term #" << i << " : " << op
                       << " with type " << op.getType() << "...\n";
    std::vector<Node> children;
    children.push_back(op);
    // transition relation applied over both variable lists
    if (i == 2)
    {
      children.insert(children.end(), vars.begin(), vars.end());
      children.insert(children.end(), primed_vars.begin(), primed_vars.end());
    }
    else
    {
      children.insert(children.end(), vars.begin(), vars.end());
    }
    terms[i] = d_nodeManager->mkNode(kind::APPLY_UF, children);
    // make application of Inv on primed variables
    if (i == 0)
    {
      children.clear();
      children.push_back(op);
      children.insert(children.end(), primed_vars.begin(), primed_vars.end());
      terms.push_back(d_nodeManager->mkNode(kind::APPLY_UF, children));
    }
  }
  // make constraints
  std::vector<Node> conj;
  conj.push_back(d_nodeManager->mkNode(kind::IMPLIES, terms[1], terms[0]));
  Node term0_and_2 = d_nodeManager->mkNode(kind::AND, terms[0], terms[2]);
  conj.push_back(d_nodeManager->mkNode(kind::IMPLIES, term0_and_2, terms[4]));
  conj.push_back(d_nodeManager->mkNode(kind::IMPLIES, terms[0], terms[3]));
  Node constraint = d_nodeManager->mkNode(kind::AND, conj);

  d_private->d_sygusConstraints.push_back(constraint);

  Trace("smt") << "SmtEngine::assertSygusInvConstrant: " << constraint << "\n";
  Dump("raw-benchmark") << SygusInvConstraintCommand(inv, pre, trans, post);
  // sygus conjecture is now stale
  setSygusConjectureStale();
}

Result SmtEngine::checkSynth()
{
  SmtScope smts(this);

  if (options::incrementalSolving())
  {
    // TODO (project #7)
    throw ModalException(
        "Cannot make check-synth commands when incremental solving is enabled");
  }
  Expr query;
  if (d_private->d_sygusConjectureStale)
  {
    // build synthesis conjecture from asserted constraints and declared
    // variables/functions
    Node sygusVar =
        d_nodeManager->mkSkolem("sygus", d_nodeManager->booleanType());
    Node inst_attr = d_nodeManager->mkNode(kind::INST_ATTRIBUTE, sygusVar);
    Node sygusAttr = d_nodeManager->mkNode(kind::INST_PATTERN_LIST, inst_attr);
    std::vector<Node> bodyv;
    Trace("smt") << "Sygus : Constructing sygus constraint...\n";
    unsigned n_constraints = d_private->d_sygusConstraints.size();
    Node body = n_constraints == 0
                    ? d_nodeManager->mkConst(true)
                    : (n_constraints == 1
                           ? d_private->d_sygusConstraints[0]
                           : d_nodeManager->mkNode(
                               kind::AND, d_private->d_sygusConstraints));
    body = body.notNode();
    Trace("smt") << "...constructed sygus constraint " << body << std::endl;
    if (!d_private->d_sygusVars.empty())
    {
      Node boundVars =
          d_nodeManager->mkNode(kind::BOUND_VAR_LIST, d_private->d_sygusVars);
      body = d_nodeManager->mkNode(kind::EXISTS, boundVars, body);
      Trace("smt") << "...constructed exists " << body << std::endl;
    }
    if (!d_private->d_sygusFunSymbols.empty())
    {
      Node boundVars = d_nodeManager->mkNode(kind::BOUND_VAR_LIST,
                                             d_private->d_sygusFunSymbols);
      body = d_nodeManager->mkNode(kind::FORALL, boundVars, body, sygusAttr);
    }
    Trace("smt") << "...constructed forall " << body << std::endl;

    // set attribute for synthesis conjecture
    setUserAttribute("sygus", sygusVar.toExpr(), {}, "");

    Trace("smt") << "Check synthesis conjecture: " << body << std::endl;
    Dump("raw-benchmark") << CheckSynthCommand();

    d_private->d_sygusConjectureStale = false;

    if (options::incrementalSolving())
    {
      // we push a context so that this conjecture is removed if we modify it
      // later
      internalPush();
      assertFormula(body, true);
    }
    else
    {
      query = body.toExpr();
    }
  }

  Result r = checkSatisfiability(query, true, false);

  // Check that synthesis solutions satisfy the conjecture
  if (options::checkSynthSol()
      && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    checkSynthSolution();
  }
  return r;
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

Node SmtEngine::postprocess(TNode node, TypeNode expectedType) const {
  return node;
}

Expr SmtEngine::simplify(const Expr& ex)
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT simplify(" << ex << ")" << endl;

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SimplifyCommand(ex);
  }

  Expr e = d_absValues->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  if( options::typeChecking() ) {
    e.getType(true); // ensure expr is type-checked at this point
  }

  // Make sure all preprocessing is done
  d_private->processAssertions();
  Node n = d_private->simplify(Node::fromExpr(e));
  n = postprocess(n, TypeNode::fromType(e.getType()));
  return n.toExpr();
}

Node SmtEngine::expandDefinitions(const Node& ex)
{
  d_private->spendResource(ResourceManager::Resource::PreprocessStep);

  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT expandDefinitions(" << ex << ")" << endl;

  // Substitute out any abstract values in ex.
  Node e = d_absValues->substituteAbstractValues(ex);
  if(options::typeChecking()) {
    // Ensure expr is type-checked at this point.
    e.getType(true);
  }

  unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_private->getProcessAssertions()->expandDefinitions(
      e, cache, /* expandOnly = */ true);
  n = postprocess(n, e.getType());

  return n;
}

// TODO(#1108): Simplify the error reporting of this method.
Expr SmtEngine::getValue(const Expr& ex) const
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetValueCommand(ex);
  }

  // Substitute out any abstract values in ex.
  Expr e = d_absValues->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  // Ensure expr is type-checked at this point.
  e.getType(options::typeChecking());

  // do not need to apply preprocessing substitutions (should be recorded
  // in model already)

  Node n = Node::fromExpr(e);
  Trace("smt") << "--- getting value of " << n << endl;
  TypeNode expectedType = n.getType();

  // Expand, then normalize
  unordered_map<Node, Node, NodeHashFunction> cache;
  n = d_private->getProcessAssertions()->expandDefinitions(n, cache);
  // There are two ways model values for terms are computed (for historical
  // reasons).  One way is that used in check-model; the other is that
  // used by the Model classes.  It's not clear to me exactly how these
  // two are different, but they need to be unified.  This ugly hack here
  // is to fix bug 554 until we can revamp boolean-terms and models [MGD]

  //AJR : necessary?
  if(!n.getType().isFunction()) {
    n = Rewriter::rewrite(n);
  }

  Trace("smt") << "--- getting value of " << n << endl;
  TheoryModel* m = getAvailableModel("get-value");
  Node resultNode;
  if(m != NULL) {
    resultNode = m->getValue(n);
  }
  Trace("smt") << "--- got value " << n << " = " << resultNode << endl;
  resultNode = postprocess(resultNode, expectedType);
  Trace("smt") << "--- model-post returned " << resultNode << endl;
  Trace("smt") << "--- model-post returned " << resultNode.getType() << endl;
  Trace("smt") << "--- model-post expected " << expectedType << endl;

  // type-check the result we got
  // Notice that lambdas have function type, which does not respect the subtype
  // relation, so we ignore them here.
  Assert(resultNode.isNull() || resultNode.getKind() == kind::LAMBDA
         || resultNode.getType().isSubtypeOf(expectedType))
      << "Run with -t smt for details.";

  // Ensure it's a constant, or a lambda (for uninterpreted functions). This
  // assertion only holds for models that do not have approximate values.
  Assert(m->hasApproximations() || resultNode.getKind() == kind::LAMBDA
         || resultNode.isConst());

  if(options::abstractValues() && resultNode.getType().isArray()) {
    resultNode = d_absValues->mkAbstractValue(resultNode);
    Trace("smt") << "--- abstract value >> " << resultNode << endl;
  }

  return resultNode.toExpr();
}

vector<Expr> SmtEngine::getValues(const vector<Expr>& exprs)
{
  vector<Expr> result;
  for (const Expr& e : exprs)
  {
    result.push_back(getValue(e));
  }
  return result;
}

bool SmtEngine::addToAssignment(const Expr& ex) {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  // Substitute out any abstract values in ex
  Node n = d_absValues->substituteAbstractValues(Node::fromExpr(ex));
  TypeNode type = n.getType(options::typeChecking());
  // must be Boolean
  PrettyCheckArgument(type.isBoolean(),
                      n,
                      "expected Boolean-typed variable or function application "
                      "in addToAssignment()");
  // must be a defined constant, or a variable
  PrettyCheckArgument(
      (((d_definedFunctions->find(n) != d_definedFunctions->end())
        && n.getNumChildren() == 0)
       || n.isVar()),
      n,
      "expected variable or defined-function application "
      "in addToAssignment(),\ngot %s",
      n.toString().c_str());
  if(!options::produceAssignments()) {
    return false;
  }
  if(d_assignments == NULL) {
    d_assignments = new (true) AssignmentSet(getContext());
  }
  d_assignments->insert(n);

  return true;
}

// TODO(#1108): Simplify the error reporting of this method.
vector<pair<Expr, Expr>> SmtEngine::getAssignment()
{
  Trace("smt") << "SMT getAssignment()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssignmentCommand();
  }
  if(!options::produceAssignments()) {
    const char* msg =
      "Cannot get the current assignment when "
      "produce-assignments option is off.";
    throw ModalException(msg);
  }

  // Get the model here, regardless of whether d_assignments is null, since
  // we should throw errors related to model availability whether or not
  // assignments is null.
  TheoryModel* m = getAvailableModel("get assignment");

  vector<pair<Expr,Expr>> res;
  if (d_assignments != nullptr)
  {
    TypeNode boolType = d_nodeManager->booleanType();
    for (AssignmentSet::key_iterator i = d_assignments->key_begin(),
                                     iend = d_assignments->key_end();
         i != iend;
         ++i)
    {
      Node as = *i;
      Assert(as.getType() == boolType);

      Trace("smt") << "--- getting value of " << as << endl;

      // Expand, then normalize
      unordered_map<Node, Node, NodeHashFunction> cache;
      Node n = d_private->getProcessAssertions()->expandDefinitions(as, cache);
      n = Rewriter::rewrite(n);

      Trace("smt") << "--- getting value of " << n << endl;
      Node resultNode;
      if (m != nullptr)
      {
        resultNode = m->getValue(n);
      }

      // type-check the result we got
      Assert(resultNode.isNull() || resultNode.getType() == boolType);

      // ensure it's a constant
      Assert(resultNode.isConst());

      Assert(as.isVar());
      res.emplace_back(as.toExpr(), resultNode.toExpr());
    }
  }
  return res;
}

// TODO(#1108): Simplify the error reporting of this method.
Model* SmtEngine::getModel() {
  Trace("smt") << "SMT getModel()" << endl;
  SmtScope smts(this);

  finalOptionsAreSet();

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetModelCommand();
  }

  TheoryModel* m = getAvailableModel("get model");

  // Since model m is being returned to the user, we must ensure that this
  // model object remains valid with future check-sat calls. Hence, we set
  // the theory engine into "eager model building" mode. TODO #2648: revisit.
  d_theoryEngine->setEagerModelBuilding();

  if (options::modelCoresMode() != options::ModelCoresMode::NONE)
  {
    // If we enabled model cores, we compute a model core for m based on our
    // (expanded) assertions using the model core builder utility
    std::vector<Expr> eassertsProc = getExpandedAssertions();
    ModelCoreBuilder::setModelCore(eassertsProc, m, options::modelCoresMode());
  }
  m->d_inputName = d_filename;
  m->d_isKnownSat = (d_smtMode == SMT_MODE_SAT);
  return m;
}

Result SmtEngine::blockModel()
{
  Trace("smt") << "SMT blockModel()" << endl;
  SmtScope smts(this);

  finalOptionsAreSet();

  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << BlockModelCommand();
  }

  TheoryModel* m = getAvailableModel("block model");

  if (options::blockModelsMode() == options::BlockModelsMode::NONE)
  {
    std::stringstream ss;
    ss << "Cannot block model when block-models is set to none.";
    throw ModalException(ss.str().c_str());
  }

  // get expanded assertions
  std::vector<Expr> eassertsProc = getExpandedAssertions();
  Expr eblocker = ModelBlocker::getModelBlocker(
      eassertsProc, m, options::blockModelsMode());
  return assertFormula(Node::fromExpr(eblocker));
}

Result SmtEngine::blockModelValues(const std::vector<Expr>& exprs)
{
  Trace("smt") << "SMT blockModelValues()" << endl;
  SmtScope smts(this);

  finalOptionsAreSet();

  PrettyCheckArgument(
      !exprs.empty(),
      "block model values must be called on non-empty set of terms");
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << BlockModelValuesCommand(exprs);
  }

  TheoryModel* m = getAvailableModel("block model values");

  // get expanded assertions
  std::vector<Expr> eassertsProc = getExpandedAssertions();
  // we always do block model values mode here
  Expr eblocker = ModelBlocker::getModelBlocker(
      eassertsProc, m, options::BlockModelsMode::VALUES, exprs);
  return assertFormula(Node::fromExpr(eblocker));
}

std::pair<Expr, Expr> SmtEngine::getSepHeapAndNilExpr(void)
{
  if (!d_logic.isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot obtain separation logic expressions if not using the "
        "separation logic theory.";
    throw RecoverableModalException(msg);
  }
  NodeManagerScope nms(d_nodeManager);
  Expr heap;
  Expr nil;
  Model* m = getAvailableModel("get separation logic heap and nil");
  if (!m->getHeapModel(heap, nil))
  {
    InternalError()
        << "SmtEngine::getSepHeapAndNilExpr(): failed to obtain heap/nil "
           "expressions from theory model.";
  }
  return std::make_pair(heap, nil);
}

std::vector<Expr> SmtEngine::getExpandedAssertions()
{
  std::vector<Expr> easserts = getAssertions();
  // must expand definitions
  std::vector<Expr> eassertsProc;
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (const Expr& e : easserts)
  {
    Node ea = Node::fromExpr(e);
    Node eae = d_private->getProcessAssertions()->expandDefinitions(ea, cache);
    eassertsProc.push_back(eae.toExpr());
  }
  return eassertsProc;
}

Expr SmtEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Expr SmtEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

void SmtEngine::checkProof()
{
#if (IS_LFSC_BUILD && IS_PROOFS_BUILD)

  Chat() << "generating proof..." << endl;

  const Proof& pf = getProof();

  Chat() << "checking proof..." << endl;

  std::string logicString = d_logic.getLogicString();

  std::stringstream pfStream;

  pfStream << proof::plf_signatures << endl;
  int64_t sizeBeforeProof = static_cast<int64_t>(pfStream.tellp());

  pf.toStream(pfStream);
  d_stats->d_proofsSize +=
      static_cast<int64_t>(pfStream.tellp()) - sizeBeforeProof;

  {
    TimerStat::CodeTimer checkProofTimer(d_stats->d_lfscCheckProofTime);
    lfscc_init();
    lfscc_check_file(pfStream, false, false, false, false, false, false, false);
  }
  // FIXME: we should actually call lfscc_cleanup here, but lfscc_cleanup
  // segfaults on regress0/bv/core/bitvec7.smt
  // lfscc_cleanup();

#else  /* (IS_LFSC_BUILD && IS_PROOFS_BUILD) */
  Unreachable()
      << "This version of CVC4 was built without proof support; cannot check "
         "proofs.";
#endif /* (IS_LFSC_BUILD && IS_PROOFS_BUILD) */
}

UnsatCore SmtEngine::getUnsatCoreInternal()
{
#if IS_PROOFS_BUILD
  if (!options::unsatCores())
  {
    throw ModalException(
        "Cannot get an unsat core when produce-unsat-cores option is off.");
  }
  if (d_smtMode != SMT_MODE_UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by "
        "UNSAT/ENTAILED response.");
  }

  d_proofManager->traceUnsatCore();  // just to trigger core creation
  return UnsatCore(this, d_proofManager->extractUnsatCore());
#else  /* IS_PROOFS_BUILD */
  throw ModalException(
      "This build of CVC4 doesn't have proof support (required for unsat "
      "cores).");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::checkUnsatCore() {
  Assert(options::unsatCores())
      << "cannot check unsat core if unsat cores are turned off";

  Notice() << "SmtEngine::checkUnsatCore(): generating unsat core" << endl;
  UnsatCore core = getUnsatCore();

  SmtEngine coreChecker(d_exprManager, &d_options);
  coreChecker.setIsInternalSubsolver();
  coreChecker.setLogic(getLogicInfo());
  coreChecker.getOptions().set(options::checkUnsatCores, false);
  coreChecker.getOptions().set(options::checkProofs, false);

  PROOF(
  std::vector<Command*>::const_iterator itg = d_defineCommands.begin();
  for (; itg != d_defineCommands.end();  ++itg) {
    (*itg)->invoke(&coreChecker);
  }
  );

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions (size == " << core.size() << ")" << endl;
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Notice() << "SmtEngine::checkUnsatCore(): pushing core member " << *i << endl;
    coreChecker.assertFormula(Node::fromExpr(*i));
  }
  Result r;
  try {
    r = coreChecker.checkSat();
  } catch(...) {
    throw;
  }
  Notice() << "SmtEngine::checkUnsatCore(): result is " << r << endl;
  if(r.asSatisfiabilityResult().isUnknown()) {
    Warning()
        << "SmtEngine::checkUnsatCore(): could not check core result unknown."
        << std::endl;
  }
  else if (r.asSatisfiabilityResult().isSat())
  {
    InternalError()
        << "SmtEngine::checkUnsatCore(): produced core was satisfiable.";
  }
}

void SmtEngine::checkModel(bool hardFailure) {
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(d_assertionList != NULL)
      << "don't have an assertion list to check in SmtEngine::checkModel()";

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  Notice() << "SmtEngine::checkModel(): generating model" << endl;
  TheoryModel* m = getAvailableModel("check model");

  // check-model is not guaranteed to succeed if approximate values were used.
  // Thus, we intentionally abort here.
  if (m->hasApproximations())
  {
    throw RecoverableModalException(
        "Cannot run check-model on a model with approximate values.");
  }

  // Check individual theory assertions
  if (options::debugCheckModels())
  {
    d_theoryEngine->checkTheoryAssertionsWithModel(hardFailure);
  }
  
  // Output the model
  Notice() << *m;

  // We have a "fake context" for the substitution map (we don't need it
  // to be context-dependent)
  context::Context fakeContext;
  SubstitutionMap substitutions(&fakeContext, /* substituteUnderQuantifiers = */ false);

  for(size_t k = 0; k < m->getNumCommands(); ++k) {
    const DeclareFunctionCommand* c = dynamic_cast<const DeclareFunctionCommand*>(m->getCommand(k));
    Notice() << "SmtEngine::checkModel(): model command " << k << " : " << m->getCommand(k) << endl;
    if(c == NULL) {
      // we don't care about DECLARE-DATATYPES, DECLARE-SORT, ...
      Notice() << "SmtEngine::checkModel(): skipping..." << endl;
    } else {
      // We have a DECLARE-FUN:
      //
      // We'll first do some checks, then add to our substitution map
      // the mapping: function symbol |-> value

      Expr func = c->getFunction();
      Node val = m->getValue(func);

      Notice() << "SmtEngine::checkModel(): adding substitution: " << func << " |-> " << val << endl;

      // (1) if the value is a lambda, ensure the lambda doesn't contain the
      // function symbol (since then the definition is recursive)
      if (val.getKind() == kind::LAMBDA) {
        // first apply the model substitutions we have so far
        Debug("boolean-terms") << "applying subses to " << val[1] << endl;
        Node n = substitutions.apply(val[1]);
        Debug("boolean-terms") << "++ got " << n << endl;
        // now check if n contains func by doing a substitution
        // [func->func2] and checking equality of the Nodes.
        // (this just a way to check if func is in n.)
        SubstitutionMap subs(&fakeContext);
        Node func2 = NodeManager::currentNM()->mkSkolem("", TypeNode::fromType(func.getType()), "", NodeManager::SKOLEM_NO_NOTIFY);
        subs.addSubstitution(func, func2);
        if(subs.apply(n) != n) {
          Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE DEFINED IN TERMS OF ITSELF ***" << endl;
          stringstream ss;
          ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
             << "considering model value for " << func << endl
             << "body of lambda is:   " << val << endl;
          if(n != val[1]) {
            ss << "body substitutes to: " << n << endl;
          }
          ss << "so " << func << " is defined in terms of itself." << endl
             << "Run with `--check-models -v' for additional diagnostics.";
          InternalError() << ss.str();
        }
      }

      // (2) check that the value is actually a value
      else if (!val.isConst())
      {
        // This is only a warning since it could have been assigned an
        // unevaluable term (e.g. an application of a transcendental function).
        // This parallels the behavior (warnings for non-constant expressions)
        // when checking whether assertions are satisfied below.
        Warning() << "Warning : SmtEngine::checkModel(): "
                  << "model value for " << func << endl
                  << "             is " << val << endl
                  << "and that is not a constant (.isConst() == false)."
                  << std::endl
                  << "Run with `--check-models -v' for additional diagnostics."
                  << std::endl;
      }

      // (3) check that it's the correct (sub)type
      // This was intended to be a more general check, but for now we can't do that because
      // e.g. "1" is an INT, which isn't a subrange type [1..10] (etc.).
      else if(func.getType().isInteger() && !val.getType().isInteger()) {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT CORRECT TYPE ***" << endl;
        InternalError()
            << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH "
               "MODEL:"
            << endl
            << "model value for " << func << endl
            << "             is " << val << endl
            << "value type is     " << val.getType() << endl
            << "should be of type " << func.getType() << endl
            << "Run with `--check-models -v' for additional diagnostics.";
      }

      // (4) checks complete, add the substitution
      Debug("boolean-terms") << "cm: adding subs " << func << " :=> " << val << endl;
      substitutions.addSubstitution(func, val);
    }
  }

  // Now go through all our user assertions checking if they're satisfied.
  for (const Node& assertion : *d_assertionList)
  {
    Notice() << "SmtEngine::checkModel(): checking assertion " << assertion
             << endl;
    Node n = assertion;
    Node nr = Rewriter::rewrite(substitutions.apply(n));
    Trace("boolean-terms") << "n: " << n << endl;
    Trace("boolean-terms") << "nr: " << nr << endl;
    if (nr.isConst() && nr.getConst<bool>())
    {
      continue;
    }
    // Apply any define-funs from the problem.
    {
      unordered_map<Node, Node, NodeHashFunction> cache;
      n = d_private->getProcessAssertions()->expandDefinitions(n, cache);
    }
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << endl;

    // Apply our model value substitutions.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << endl;

    // We look up the value before simplifying. If n contains quantifiers,
    // this may increases the chance of finding its value before the node is
    // altered by simplification below.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;

    // Simplify the result.
    n = d_private->simplify(n);
    Notice() << "SmtEngine::checkModel(): -- simplifies to  " << n << endl;

    // Replace the already-known ITEs (this is important for ground ITEs under quantifiers).
    n = d_private->d_iteRemover.replace(n);
    Notice() << "SmtEngine::checkModel(): -- ite replacement gives " << n << endl;

    // Apply our model value substitutions (again), as things may have been simplified.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- re-substitutes to " << n << endl;

    // As a last-ditch effort, ask model to simplify it.
    // Presently, this is only an issue for quantifiers, which can have a value
    // but don't show up in our substitution map above.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- model-substitutes to " << n << endl;

    if (n.isConst())
    {
      if (n.getConst<bool>())
      {
        // assertion is true, everything is fine
        continue;
      }
    }

    // Otherwise, we did not succeed in showing the current assertion to be
    // true. This may either indicate that our model is wrong, or that we cannot
    // check it. The latter may be the case for several reasons.
    // For example, quantified formulas are not checkable, although we assign
    // them to true/false based on the satisfying assignment. However,
    // quantified formulas can be modified during preprocess, so they may not
    // correspond to those in the satisfying assignment. Hence we throw
    // warnings for assertions that do not simplify to either true or false.
    // Other theories such as non-linear arithmetic (in particular,
    // transcendental functions) also have the property of not being able to
    // be checked precisely here.
    // Note that warnings like these can be avoided for quantified formulas
    // by making preprocessing passes explicitly record how they
    // rewrite quantified formulas (see cvc4-wishues#43).
    if (!n.isConst())
    {
      // Not constant, print a less severe warning message here.
      Warning() << "Warning : SmtEngine::checkModel(): cannot check simplified "
                   "assertion : "
                << n << endl;
      continue;
    }
    // Assertions that simplify to false result in an InternalError or
    // Warning being thrown below (when hardFailure is false).
    Notice() << "SmtEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
             << endl;
    stringstream ss;
    ss << "SmtEngine::checkModel(): "
       << "ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
       << "assertion:     " << assertion << endl
       << "simplifies to: " << n << endl
       << "expected `true'." << endl
       << "Run with `--check-models -v' for additional diagnostics.";
    if (hardFailure)
    {
      // internal error if hardFailure is true
      InternalError() << ss.str();
    }
    else
    {
      Warning() << ss.str() << endl;
    }
  }
  Notice() << "SmtEngine::checkModel(): all assertions checked out OK !" << endl;
}

void SmtEngine::checkSynthSolution()
{
  NodeManager* nm = NodeManager::currentNM();
  Notice() << "SmtEngine::checkSynthSolution(): checking synthesis solution" << endl;
  std::map<Node, std::map<Node, Node>> sol_map;
  /* Get solutions and build auxiliary vectors for substituting */
  if (!d_theoryEngine->getSynthSolutions(sol_map))
  {
    InternalError() << "SmtEngine::checkSynthSolution(): No solution to check!";
    return;
  }
  if (sol_map.empty())
  {
    InternalError() << "SmtEngine::checkSynthSolution(): Got empty solution!";
    return;
  }
  Trace("check-synth-sol") << "Got solution map:\n";
  // the set of synthesis conjectures in our assertions
  std::unordered_set<Node, NodeHashFunction> conjs;
  // For each of the above conjectures, the functions-to-synthesis and their
  // solutions. This is used as a substitution below.
  std::map<Node, std::vector<Node>> fvarMap;
  std::map<Node, std::vector<Node>> fsolMap;
  for (const std::pair<const Node, std::map<Node, Node>>& cmap : sol_map)
  {
    Trace("check-synth-sol") << "For conjecture " << cmap.first << ":\n";
    conjs.insert(cmap.first);
    std::vector<Node>& fvars = fvarMap[cmap.first];
    std::vector<Node>& fsols = fsolMap[cmap.first];
    for (const std::pair<const Node, Node>& pair : cmap.second)
    {
      Trace("check-synth-sol")
          << "  " << pair.first << " --> " << pair.second << "\n";
      fvars.push_back(pair.first);
      fsols.push_back(pair.second);
    }
  }
  Trace("check-synth-sol") << "Starting new SMT Engine\n";
  /* Start new SMT engine to check solutions */
  SmtEngine solChecker(d_exprManager, &d_options);
  solChecker.setIsInternalSubsolver();
  solChecker.setLogic(getLogicInfo());
  solChecker.getOptions().set(options::checkSynthSol, false);
  solChecker.getOptions().set(options::sygusRecFun, false);

  Trace("check-synth-sol") << "Retrieving assertions\n";
  // Build conjecture from original assertions
  if (d_assertionList == NULL)
  {
    Trace("check-synth-sol") << "No assertions to check\n";
    return;
  }
  // auxiliary assertions
  std::vector<Node> auxAssertions;
  // expand definitions cache
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (const Node& assertion : *d_assertionList)
  {
    Notice() << "SmtEngine::checkSynthSolution(): checking assertion "
             << assertion << endl;
    Trace("check-synth-sol") << "Retrieving assertion " << assertion << "\n";
    // Apply any define-funs from the problem.
    Node n =
        d_private->getProcessAssertions()->expandDefinitions(assertion, cache);
    Notice() << "SmtEngine::checkSynthSolution(): -- expands to " << n << endl;
    Trace("check-synth-sol") << "Expanded assertion " << n << "\n";
    if (conjs.find(n) == conjs.end())
    {
      Trace("check-synth-sol") << "It is an auxiliary assertion\n";
      auxAssertions.push_back(n);
    }
    else
    {
      Trace("check-synth-sol") << "It is a synthesis conjecture\n";
    }
  }
  // check all conjectures
  for (const Node& conj : conjs)
  {
    // get the solution for this conjecture
    std::vector<Node>& fvars = fvarMap[conj];
    std::vector<Node>& fsols = fsolMap[conj];
    // Apply solution map to conjecture body
    Node conjBody;
    /* Whether property is quantifier free */
    if (conj[1].getKind() != kind::EXISTS)
    {
      conjBody = conj[1].substitute(
          fvars.begin(), fvars.end(), fsols.begin(), fsols.end());
    }
    else
    {
      conjBody = conj[1][1].substitute(
          fvars.begin(), fvars.end(), fsols.begin(), fsols.end());

      /* Skolemize property */
      std::vector<Node> vars, skos;
      for (unsigned j = 0, size = conj[1][0].getNumChildren(); j < size; ++j)
      {
        vars.push_back(conj[1][0][j]);
        std::stringstream ss;
        ss << "sk_" << j;
        skos.push_back(nm->mkSkolem(ss.str(), conj[1][0][j].getType()));
        Trace("check-synth-sol") << "\tSkolemizing " << conj[1][0][j] << " to "
                                 << skos.back() << "\n";
      }
      conjBody = conjBody.substitute(
          vars.begin(), vars.end(), skos.begin(), skos.end());
    }
    Notice() << "SmtEngine::checkSynthSolution(): -- body substitutes to "
             << conjBody << endl;
    Trace("check-synth-sol") << "Substituted body of assertion to " << conjBody
                             << "\n";
    solChecker.assertFormula(conjBody);
    // Assert all auxiliary assertions. This may include recursive function
    // definitions that were added as assertions to the sygus problem.
    for (const Node& a : auxAssertions)
    {
      solChecker.assertFormula(a);
    }
    Result r = solChecker.checkSat();
    Notice() << "SmtEngine::checkSynthSolution(): result is " << r << endl;
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.asSatisfiabilityResult().isUnknown())
    {
      InternalError() << "SmtEngine::checkSynthSolution(): could not check "
                         "solution, result "
                         "unknown.";
    }
    else if (r.asSatisfiabilityResult().isSat())
    {
      InternalError()
          << "SmtEngine::checkSynthSolution(): produced solution leads to "
             "satisfiable negated conjecture.";
    }
    solChecker.resetAssertions();
  }
}

void SmtEngine::checkInterpol(Expr interpol,
                              const std::vector<Expr>& easserts,
                              const Node& conj)
{
}

void SmtEngine::checkAbduct(Node a)
{
  Assert(a.getType().isBoolean());
  // check it with the abduction solver
  return d_abductSolver->checkAbduct(a);
}

// TODO(#1108): Simplify the error reporting of this method.
UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetUnsatCoreCommand();
  }
  return getUnsatCoreInternal();
}

// TODO(#1108): Simplify the error reporting of this method.
const Proof& SmtEngine::getProof()
{
  Trace("smt") << "SMT getProof()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetProofCommand();
  }
#if IS_PROOFS_BUILD
  if(!options::proof()) {
    throw ModalException("Cannot get a proof when produce-proofs option is off.");
  }
  if (d_smtMode != SMT_MODE_UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get a proof unless immediately preceded by UNSAT/ENTAILED "
        "response.");
  }

  return ProofManager::getProof(this);
#else /* IS_PROOFS_BUILD */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::printInstantiations( std::ostream& out ) {
  SmtScope smts(this);
  finalOptionsAreSet();
  if (options::instFormatMode() == options::InstFormatMode::SZS)
  {
    out << "% SZS output start Proof for " << d_filename.c_str() << std::endl;
  }
  if( d_theoryEngine ){
    d_theoryEngine->printInstantiations( out );
  }else{
    Assert(false);
  }
  if (options::instFormatMode() == options::InstFormatMode::SZS)
  {
    out << "% SZS output end Proof for " << d_filename.c_str() << std::endl;
  }
}

void SmtEngine::printSynthSolution( std::ostream& out ) {
  SmtScope smts(this);
  finalOptionsAreSet();
  if( d_theoryEngine ){
    d_theoryEngine->printSynthSolution( out );
  }else{
    Assert(false);
  }
}

bool SmtEngine::getSynthSolutions(std::map<Expr, Expr>& sol_map)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  std::map<Node, std::map<Node, Node>> sol_mapn;
  Assert(d_theoryEngine != nullptr);
  // fail if the theory engine does not have synthesis solutions
  if (!d_theoryEngine->getSynthSolutions(sol_mapn))
  {
    return false;
  }
  for (std::pair<const Node, std::map<Node, Node>>& cs : sol_mapn)
  {
    for (std::pair<const Node, Node>& s : cs.second)
    {
      sol_map[s.first.toExpr()] = s.second.toExpr();
    }
  }
  return true;
}

Expr SmtEngine::doQuantifierElimination(const Expr& e, bool doFull, bool strict)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  if(!d_logic.isPure(THEORY_ARITH) && strict){
    Warning() << "Unexpected logic for quantifier elimination " << d_logic << endl;
  }
  Trace("smt-qe") << "Do quantifier elimination " << e << std::endl;
  Node n_e = Node::fromExpr( e );
  if (n_e.getKind() != kind::EXISTS && n_e.getKind() != kind::FORALL)
  {
    throw ModalException(
        "Expecting a quantified formula as argument to get-qe.");
  }
  //tag the quantified formula with the quant-elim attribute
  TypeNode t = NodeManager::currentNM()->booleanType();
  Node n_attr = NodeManager::currentNM()->mkSkolem("qe", t, "Auxiliary variable for qe attr.");
  std::vector< Node > node_values;
  d_theoryEngine->setUserAttribute( doFull ? "quant-elim" : "quant-elim-partial", n_attr, node_values, "");
  n_attr = NodeManager::currentNM()->mkNode(kind::INST_ATTRIBUTE, n_attr);
  n_attr = NodeManager::currentNM()->mkNode(kind::INST_PATTERN_LIST, n_attr);
  std::vector< Node > e_children;
  e_children.push_back( n_e[0] );
  e_children.push_back(n_e.getKind() == kind::EXISTS ? n_e[1]
                                                     : n_e[1].negate());
  e_children.push_back( n_attr );
  Node nn_e = NodeManager::currentNM()->mkNode( kind::EXISTS, e_children );
  Trace("smt-qe-debug") << "Query for quantifier elimination : " << nn_e << std::endl;
  Assert(nn_e.getNumChildren() == 3);
  Result r = checkSatisfiability(nn_e.toExpr(), true, true);
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if(r.asSatisfiabilityResult().isSat() != Result::UNSAT ) {
    if( r.asSatisfiabilityResult().isSat() != Result::SAT && doFull ){
      Notice()
          << "While performing quantifier elimination, unexpected result : "
          << r << " for query.";
      // failed, return original
      return e;
    }
    std::vector< Node > inst_qs;
    d_theoryEngine->getInstantiatedQuantifiedFormulas( inst_qs );
    Assert(inst_qs.size() <= 1);
    Node ret_n;
    if( inst_qs.size()==1 ){
      Node top_q = inst_qs[0];
      //Node top_q = Rewriter::rewrite( nn_e ).negate();
      Assert(top_q.getKind() == kind::FORALL);
      Trace("smt-qe") << "Get qe for " << top_q << std::endl;
      ret_n = d_theoryEngine->getInstantiatedConjunction( top_q );
      Trace("smt-qe") << "Returned : " << ret_n << std::endl;
      if (n_e.getKind() == kind::EXISTS)
      {
        ret_n = Rewriter::rewrite(ret_n.negate());
      }
    }else{
      ret_n = NodeManager::currentNM()->mkConst(n_e.getKind() != kind::EXISTS);
    }
    // do extended rewrite to minimize the size of the formula aggressively
    theory::quantifiers::ExtendedRewriter extr(true);
    ret_n = extr.extendedRewrite(ret_n);
    return ret_n.toExpr();
  }else {
    return NodeManager::currentNM()
        ->mkConst(n_e.getKind() == kind::EXISTS)
        .toExpr();
  }
}

bool SmtEngine::getInterpol(const Expr& conj,
                            const Type& grammarType,
                            Expr& interpol)
{
  return false;
}

bool SmtEngine::getInterpol(const Expr& conj, Expr& interpol)
{
  Type grammarType;
  return getInterpol(conj, grammarType, interpol);
}

bool SmtEngine::getAbduct(const Node& conj,
                          const TypeNode& grammarType,
                          Node& abd)
{
  if (d_abductSolver->getAbduct(conj, grammarType, abd))
  {
    // successfully generated an abduct, update to abduct state
    d_smtMode = SMT_MODE_ABDUCT;
    return true;
  }
  // failed, we revert to the assert state
  d_smtMode = SMT_MODE_ASSERT;
  return false;
}

bool SmtEngine::getAbduct(const Node& conj, Node& abd)
{
  TypeNode grammarType;
  return getAbduct(conj, grammarType, abd);
}

void SmtEngine::getInstantiatedQuantifiedFormulas( std::vector< Expr >& qs ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    std::vector< Node > qs_n;
    d_theoryEngine->getInstantiatedQuantifiedFormulas( qs_n );
    for( unsigned i=0; i<qs_n.size(); i++ ){
      qs.push_back( qs_n[i].toExpr() );
    }
  }else{
    Assert(false);
  }
}

void SmtEngine::getInstantiations( Expr q, std::vector< Expr >& insts ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    std::vector< Node > insts_n;
    d_theoryEngine->getInstantiations( Node::fromExpr( q ), insts_n );
    for( unsigned i=0; i<insts_n.size(); i++ ){
      insts.push_back( insts_n[i].toExpr() );
    }
  }else{
    Assert(false);
  }
}

void SmtEngine::getInstantiationTermVectors( Expr q, std::vector< std::vector< Expr > >& tvecs ) {
  SmtScope smts(this);
  Assert(options::trackInstLemmas());
  if( d_theoryEngine ){
    std::vector< std::vector< Node > > tvecs_n;
    d_theoryEngine->getInstantiationTermVectors( Node::fromExpr( q ), tvecs_n );
    for( unsigned i=0; i<tvecs_n.size(); i++ ){
      std::vector< Expr > tvec;
      for( unsigned j=0; j<tvecs_n[i].size(); j++ ){
        tvec.push_back( tvecs_n[i][j].toExpr() );
      }
      tvecs.push_back( tvec );
    }
  }else{
    Assert(false);
  }
}

vector<Expr> SmtEngine::getAssertions() {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssertionsCommand();
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!options::produceAssertions()) {
    const char* msg =
      "Cannot query the current assertion list when not in produce-assertions mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  std::vector<Expr> res;
  for (const Node& n : *d_assertionList)
  {
    res.emplace_back(n.toExpr());
  }
  // copy the result out
  return res;
}

void SmtEngine::push()
{
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT push()" << endl;
  d_private->notifyPush();
  d_private->processAssertions();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PushCommand();
  }
  if(!options::incrementalSolving()) {
    throw ModalException("Cannot push when not solving incrementally (use --incremental)");
  }


  // The problem isn't really "extended" yet, but this disallows
  // get-model after a push, simplifying our lives somewhat and
  // staying symmetric with pop.
  setProblemExtended();

  d_userLevels.push_back(d_userContext->getLevel());
  internalPush();
  Trace("userpushpop") << "SmtEngine: pushed to level "
                       << d_userContext->getLevel() << endl;
}

void SmtEngine::pop() {
  SmtScope smts(this);
  finalOptionsAreSet();
  Trace("smt") << "SMT pop()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PopCommand();
  }
  if(!options::incrementalSolving()) {
    throw ModalException("Cannot pop when not solving incrementally (use --incremental)");
  }
  if(d_userLevels.size() == 0) {
    throw ModalException("Cannot pop beyond the first user frame");
  }

  // The problem isn't really "extended" yet, but this disallows
  // get-model after a pop, simplifying our lives somewhat.  It might
  // not be strictly necessary to do so, since the pops occur lazily,
  // but also it would be weird to have a legally-executed (get-model)
  // that only returns a subset of the assignment (because the rest
  // is no longer in scope!).
  setProblemExtended();

  AlwaysAssert(d_userContext->getLevel() > 0);
  AlwaysAssert(d_userLevels.back() < d_userContext->getLevel());
  while (d_userLevels.back() < d_userContext->getLevel()) {
    internalPop(true);
  }
  d_userLevels.pop_back();

  // Clear out assertion queues etc., in case anything is still in there
  d_private->notifyPop();

  Trace("userpushpop") << "SmtEngine: popped to level "
                       << d_userContext->getLevel() << endl;
  // FIXME: should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SmtEngine::internalPush() {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPush()" << endl;
  doPendingPops();
  if(options::incrementalSolving()) {
    d_private->processAssertions();
    TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
    d_userContext->push();
    // the d_context push is done inside of the SAT solver
    d_propEngine->push();
  }
}

void SmtEngine::internalPop(bool immediate) {
  Assert(d_fullyInited);
  Trace("smt") << "SmtEngine::internalPop()" << endl;
  if(options::incrementalSolving()) {
    ++d_pendingPops;
  }
  if(immediate) {
    doPendingPops();
  }
}

void SmtEngine::doPendingPops() {
  Trace("smt") << "SmtEngine::doPendingPops()" << endl;
  Assert(d_pendingPops == 0 || options::incrementalSolving());
  // check to see if a postsolve() is pending
  if (d_needPostsolve)
  {
    d_propEngine->resetTrail();
  }
  while(d_pendingPops > 0) {
    TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
    d_propEngine->pop();
    // the d_context pop is done inside of the SAT solver
    d_userContext->pop();
    --d_pendingPops;
  }
  if (d_needPostsolve)
  {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }
}

void SmtEngine::reset()
{
  SmtScope smts(this);
  ExprManager *em = d_exprManager;
  Trace("smt") << "SMT reset()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ResetCommand();
  }
  Options opts;
  opts.copyValues(d_originalOptions);
  this->~SmtEngine();
  new (this) SmtEngine(em, &opts);
}

void SmtEngine::resetAssertions()
{
  SmtScope smts(this);

  if (!d_fullyInited)
  {
    // We're still in Start Mode, nothing asserted yet, do nothing.
    // (see solver execution modes in the SMT-LIB standard)
    Assert(d_context->getLevel() == 0);
    Assert(d_userContext->getLevel() == 0);
    d_dumpm->resetAssertions();
    return;
  }

  doPendingPops();

  Trace("smt") << "SMT resetAssertions()" << endl;
  if (Dump.isOn("benchmark"))
  {
    Dump("benchmark") << ResetAssertionsCommand();
  }

  while (!d_userLevels.empty())
  {
    pop();
  }

  // Remember the global push/pop around everything when beyond Start mode
  // (see solver execution modes in the SMT-LIB standard)
  Assert(d_userLevels.size() == 0 && d_userContext->getLevel() == 1);
  d_context->popto(0);
  d_userContext->popto(0);
  d_dumpm->resetAssertions();
  d_userContext->push();
  d_context->push();

  /* Create new PropEngine.
   * First force destruction of referenced PropEngine to enforce that
   * statistics are unregistered by the obsolete PropEngine object before
   * registered again by the new PropEngine object */
  d_propEngine.reset(nullptr);
  d_propEngine.reset(new PropEngine(
      getTheoryEngine(), getContext(), getUserContext(), getResourceManager()));
  d_theoryEngine->setPropEngine(getPropEngine());
}

void SmtEngine::interrupt()
{
  if(!d_fullyInited) {
    return;
  }
  d_propEngine->interrupt();
  d_theoryEngine->interrupt();
}

void SmtEngine::setResourceLimit(unsigned long units, bool cumulative) {
  d_resourceManager->setResourceLimit(units, cumulative);
}
void SmtEngine::setTimeLimit(unsigned long milis)
{
  d_resourceManager->setTimeLimit(milis);
}

unsigned long SmtEngine::getResourceUsage() const {
  return d_resourceManager->getResourceUsage();
}

unsigned long SmtEngine::getTimeUsage() const {
  return d_resourceManager->getTimeUsage();
}

unsigned long SmtEngine::getResourceRemaining() const
{
  return d_resourceManager->getResourceRemaining();
}

NodeManager* SmtEngine::getNodeManager() const
{
  return d_exprManager->getNodeManager();
}

Statistics SmtEngine::getStatistics() const
{
  return Statistics(*d_statisticsRegistry);
}

SExpr SmtEngine::getStatistic(std::string name) const
{
  return d_statisticsRegistry->getStatistic(name);
}

void SmtEngine::safeFlushStatistics(int fd) const {
  d_statisticsRegistry->safeFlushInformation(fd);
}

void SmtEngine::setUserAttribute(const std::string& attr,
                                 Expr expr,
                                 const std::vector<Expr>& expr_values,
                                 const std::string& str_value)
{
  SmtScope smts(this);
  finalOptionsAreSet();
  std::vector<Node> node_values;
  for( unsigned i=0; i<expr_values.size(); i++ ){
    node_values.push_back( expr_values[i].getNode() );
  }
  d_theoryEngine->setUserAttribute(attr, expr.getNode(), node_values, str_value);
}

void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
{
  // Always check whether the SmtEngine has been initialized (which is done
  // upon entering Assert mode the first time). No option can  be set after
  // initialized.
  if(d_fullyInited) {
    throw ModalException("SmtEngine::setOption called after initialization.");
  }
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << SetOptionCommand(key, value);
  }

  if(key == "command-verbosity") {
    if(!value.isAtom()) {
      const vector<SExpr>& cs = value.getChildren();
      if(cs.size() == 2 &&
         (cs[0].isKeyword() || cs[0].isString()) &&
         cs[1].isInteger()) {
        string c = cs[0].getValue();
        const Integer& v = cs[1].getIntegerValue();
        if(v < 0 || v > 2) {
          throw OptionException("command-verbosity must be 0, 1, or 2");
        }
        d_commandVerbosity[c] = v;
        return;
      }
    }
    throw OptionException("command-verbosity value must be a tuple (command-name, integer)");
  }

  if(!value.isAtom()) {
    throw OptionException("bad value for :" + key);
  }

  string optionarg = value.getValue();
  d_options.setOption(key, optionarg);
}

void SmtEngine::setIsInternalSubsolver() { d_isInternalSubsolver = true; }

bool SmtEngine::isInternalSubsolver() const { return d_isInternalSubsolver; }

CVC4::SExpr SmtEngine::getOption(const std::string& key) const
{
  NodeManagerScope nms(d_nodeManager);

  Trace("smt") << "SMT getOption(" << key << ")" << endl;

  if(key.length() >= 18 &&
     key.compare(0, 18, "command-verbosity:") == 0) {
    map<string, Integer>::const_iterator i = d_commandVerbosity.find(key.c_str() + 18);
    if(i != d_commandVerbosity.end()) {
      return SExpr((*i).second);
    }
    i = d_commandVerbosity.find("*");
    if(i != d_commandVerbosity.end()) {
      return SExpr((*i).second);
    }
    return SExpr(Integer(2));
  }

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetOptionCommand(key);
  }

  if(key == "command-verbosity") {
    vector<SExpr> result;
    SExpr defaultVerbosity;
    for(map<string, Integer>::const_iterator i = d_commandVerbosity.begin();
        i != d_commandVerbosity.end();
        ++i) {
      vector<SExpr> v;
      v.push_back(SExpr((*i).first));
      v.push_back(SExpr((*i).second));
      if((*i).first == "*") {
        // put the default at the end of the SExpr
        defaultVerbosity = SExpr(v);
      } else {
        result.push_back(SExpr(v));
      }
    }
    // put the default at the end of the SExpr
    if(!defaultVerbosity.isAtom()) {
      result.push_back(defaultVerbosity);
    } else {
      // ensure the default is always listed
      vector<SExpr> v;
      v.push_back(SExpr("*"));
      v.push_back(SExpr(Integer(2)));
      result.push_back(SExpr(v));
    }
    return SExpr(result);
  }

  return SExpr::parseAtom(d_options.getOption(key));
}

bool SmtEngine::getExpressionName(const Node& e, std::string& name) const {
  return d_exprNames->getExpressionName(e, name);
}

void SmtEngine::setExpressionName(const Node& e, const std::string& name) {
  Trace("smt-debug") << "Set expression name " << e << " to " << name << std::endl;
  d_exprNames->setExpressionName(e,name);
}

Options& SmtEngine::getOptions() { return d_options; }

const Options& SmtEngine::getOptions() const { return d_options; }

ResourceManager* SmtEngine::getResourceManager()
{
  return d_resourceManager.get();
}

DumpManager* SmtEngine::getDumpManager() { return d_dumpm.get(); }

void SmtEngine::setSygusConjectureStale()
{
  if (d_private->d_sygusConjectureStale)
  {
    // already stale
    return;
  }
  d_private->d_sygusConjectureStale = true;
  if (options::incrementalSolving())
  {
    internalPop();
  }
}

}/* CVC4 namespace */
