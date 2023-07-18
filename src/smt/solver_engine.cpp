/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The main entry point into the cvc5 library's SMT interface.
 */

#include "smt/solver_engine.h"

#include "base/check.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "decision/decision_engine.h"
#include "expr/bound_var_manager.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subtype_elim_node_converter.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/options_public.h"
#include "options/parser_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "preprocessing/passes/synth_rew_rules.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/abduction_solver.h"
#include "smt/assertions.h"
#include "smt/check_models.h"
#include "smt/context_manager.h"
#include "smt/env.h"
#include "smt/expand_definitions.h"
#include "smt/find_synth_solver.h"
#include "smt/interpolation_solver.h"
#include "smt/listeners.h"
#include "smt/logic_exception.h"
#include "smt/model.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/preprocessor.h"
#include "smt/proof_manager.h"
#include "smt/quant_elim_solver.h"
#include "smt/set_defaults.h"
#include "smt/smt_driver.h"
#include "smt/smt_driver_deep_restarts.h"
#include "smt/smt_solver.h"
#include "smt/solver_engine_state.h"
#include "smt/solver_engine_stats.h"
#include "smt/sygus_solver.h"
#include "smt/timeout_core_manager.h"
#include "smt/unsat_core_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/instantiation_list.h"
#include "theory/quantifiers/oracle_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/rewrite_verifier.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "util/random.h"
#include "util/rational.h"
#include "util/resource_manager.h"
#include "util/sexpr.h"
#include "util/statistics_registry.h"

// required for hacks related to old proofs for unsat cores
#include "base/configuration.h"
#include "base/configuration_private.h"

using namespace std;
using namespace cvc5::internal::smt;
using namespace cvc5::internal::preprocessing;
using namespace cvc5::internal::prop;
using namespace cvc5::context;
using namespace cvc5::internal::theory;

namespace cvc5::internal {

SolverEngine::SolverEngine(const Options* optr)
    : d_env(new Env(optr)),
      d_state(new SolverEngineState(*d_env.get())),
      d_ctxManager(nullptr),
      d_routListener(new ResourceOutListener(*this)),
      d_smtSolver(nullptr),
      d_smtDriver(nullptr),
      d_checkModels(nullptr),
      d_pfManager(nullptr),
      d_ucManager(nullptr),
      d_sygusSolver(nullptr),
      d_abductSolver(nullptr),
      d_interpolSolver(nullptr),
      d_quantElimSolver(nullptr),
      d_isInternalSubsolver(false),
      d_stats(nullptr)
{
  // listen to resource out
  getResourceManager()->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SolverEngineStatistics(d_env->getStatisticsRegistry()));
  // make the SMT solver
  d_smtSolver.reset(new SmtSolver(*d_env, *d_stats));
  // make the context manager
  d_ctxManager.reset(new ContextManager(*d_env.get(), *d_state));
  // make the SyGuS solver
  d_sygusSolver.reset(new SygusSolver(*d_env.get(), *d_smtSolver));
  // make the quantifier elimination solver
  d_quantElimSolver.reset(
      new QuantElimSolver(*d_env.get(), *d_smtSolver, d_ctxManager.get()));
}

bool SolverEngine::isFullyInited() const { return d_state->isFullyInited(); }
bool SolverEngine::isQueryMade() const { return d_state->isQueryMade(); }
size_t SolverEngine::getNumUserLevels() const
{
  return d_ctxManager->getNumUserLevels();
}
SmtMode SolverEngine::getSmtMode() const { return d_state->getMode(); }
bool SolverEngine::isSmtModeSat() const
{
  SmtMode mode = getSmtMode();
  return mode == SmtMode::SAT || mode == SmtMode::SAT_UNKNOWN;
}
Result SolverEngine::getStatusOfLastCommand() const
{
  return d_state->getStatus();
}

void SolverEngine::finishInit()
{
  if (d_state->isFullyInited())
  {
    // already initialized, return
    return;
  }

  // Notice that finishInit is called when options are finalized. If we are
  // parsing smt2, this occurs at the moment we enter "Assert mode", page 52 of
  // SMT-LIB 2.6 standard.

  // set the logic
  const LogicInfo& logic = getLogicInfo();
  if (!logic.isLocked())
  {
    setLogicInternal();
  }

  // set the random seed
  Random::getRandom().setSeed(d_env->getOptions().driver.seed);

  // Call finish init on the set defaults module. This inializes the logic
  // and the best default options based on our heuristics.
  SetDefaults sdefaults(*d_env, d_isInternalSubsolver);
  sdefaults.setDefaults(d_env->d_logic, getOptions());

  ProofNodeManager* pnm = nullptr;
  if (d_env->getOptions().smt.produceProofs)
  {
    // ensure bound variable uses canonical bound variables
    NodeManager::currentNM()->getBoundVarManager()->enableKeepCacheValues();
    // make the proof manager
    d_pfManager.reset(new PfManager(*d_env.get()));
    // start the unsat core manager
    d_ucManager.reset(new UnsatCoreManager(*d_env.get()));
    pnm = d_pfManager->getProofNodeManager();
  }
  // enable proof support in the environment/rewriter
  d_env->finishInit(pnm);

  Trace("smt-debug") << "SolverEngine::finishInit" << std::endl;
  d_smtSolver->finishInit();

  // make SMT solver driver based on options
  if (options().smt.deepRestartMode != options::DeepRestartMode::NONE)
  {
    d_smtDriver.reset(new SmtDriverDeepRestarts(
        *d_env.get(), *d_smtSolver.get(), d_ctxManager.get()));
  }
  else
  {
    ContextManager* ctx = d_ctxManager.get();
    // deep restarts not enabled
    d_smtDriver.reset(
        new SmtDriverSingleCall(*d_env.get(), *d_smtSolver.get(), ctx));
  }

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_ctxManager->setup(d_smtDriver.get());

  // subsolvers
  if (d_env->getOptions().smt.produceAbducts)
  {
    d_abductSolver.reset(new AbductionSolver(*d_env.get()));
  }
  if (d_env->getOptions().smt.produceInterpolants)
  {
    d_interpolSolver.reset(new InterpolationSolver(*d_env));
  }
  // check models utility
  if (d_env->getOptions().smt.checkModels)
  {
    d_checkModels.reset(new CheckModels(*d_env.get()));
  }

  AlwaysAssert(d_smtSolver->getPropEngine()->getAssertionLevel() == 0)
      << "The PropEngine has pushed but the SolverEngine "
         "hasn't finished initializing!";

  Assert(getLogicInfo().isLocked());

  // store that we are finished initializing
  d_state->markFinishInit();
  Trace("smt-debug") << "SolverEngine::finishInit done" << std::endl;
}

void SolverEngine::shutdown()
{
  d_ctxManager->shutdown();
  d_env->shutdown();
}

SolverEngine::~SolverEngine()
{

  try
  {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_ctxManager->cleanup();

    // destroy all passes before destroying things that they refer to
    d_smtSolver->getPreprocessor()->cleanup();

    d_pfManager.reset(nullptr);
    d_ucManager.reset(nullptr);

    d_abductSolver.reset(nullptr);
    d_interpolSolver.reset(nullptr);
    d_quantElimSolver.reset(nullptr);
    d_sygusSolver.reset(nullptr);
    d_smtDriver.reset(nullptr);
    d_smtSolver.reset(nullptr);

    d_stats.reset(nullptr);
    d_routListener.reset(nullptr);
    // destroy the state
    d_state.reset(nullptr);
    // destroy the environment
    d_env.reset(nullptr);
  }
  catch (Exception& e)
  {
    d_env->warning() << "cvc5 threw an exception during cleanup." << std::endl << e << std::endl;
  }
}

void SolverEngine::setLogic(const LogicInfo& logic)
{
  if (d_state->isFullyInited())
  {
    throw ModalException(
        "Cannot set logic in SolverEngine after the engine has "
        "finished initializing.");
  }
  d_env->d_logic = logic;
  d_userLogic = logic;
  setLogicInternal();
}

void SolverEngine::setLogic(const std::string& s)
{
  try
  {
    setLogic(LogicInfo(s));
  }
  catch (IllegalArgumentException& e)
  {
    throw LogicException(e.what());
  }
}

void SolverEngine::setLogic(const char* logic) { setLogic(string(logic)); }

const LogicInfo& SolverEngine::getLogicInfo() const
{
  return d_env->getLogicInfo();
}

LogicInfo SolverEngine::getUserLogicInfo() const
{
  // Lock the logic to make sure that this logic can be queried. We create a
  // copy of the user logic here to keep this method const.
  LogicInfo res = d_userLogic;
  res.lock();
  return res;
}

void SolverEngine::setLogicInternal()
{
  Assert(!d_state->isFullyInited())
      << "setting logic in SolverEngine but the engine has already"
         " finished initializing for this run";
  d_env->d_logic.lock();
  d_userLogic.lock();
}

void SolverEngine::setInfo(const std::string& key, const std::string& value)
{
  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if (key == "filename")
  {
    d_env->d_options.writeDriver().filename = value;
    d_env->getStatisticsRegistry().registerValue<std::string>(
        "driver::filename", value);
  }
  else if (key == "smt-lib-version"
           && !getOptions().base.inputLanguageWasSetByUser)
  {
    if (value != "2" && value != "2.6")
    {
      d_env->warning() << "SMT-LIB version " << value
                << " unsupported, defaulting to language (and semantics of) "
                   "SMT-LIB 2.6\n";
    }
    getOptions().writeBase().inputLanguage = Language::LANG_SMTLIB_V2_6;
    // also update the output language
    if (!getOptions().printer.outputLanguageWasSetByUser)
    {
      setOption("output-language", "smtlib2.6");
      getOptions().writePrinter().outputLanguageWasSetByUser = false;
    }
  }
  else if (key == "status")
  {
    d_state->notifyExpectedStatus(value);
  }
}

bool SolverEngine::isValidGetInfoFlag(const std::string& key) const
{
  if (key == "all-statistics" || key == "error-behavior" || key == "filename"
      || key == "name" || key == "version" || key == "authors"
      || key == "status" || key == "time" || key == "reason-unknown"
      || key == "assertion-stack-levels" || key == "all-options")
  {
    return true;
  }
  return false;
}

std::string SolverEngine::getInfo(const std::string& key) const
{
  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if (key == "all-statistics")
  {
    return toSExpr(d_env->getStatisticsRegistry().begin(),
                   d_env->getStatisticsRegistry().end());
  }
  if (key == "error-behavior")
  {
    return "immediate-exit";
  }
  if (key == "filename")
  {
    return d_env->getOptions().driver.filename;
  }
  if (key == "name")
  {
    return toSExpr(Configuration::getName());
  }
  if (key == "version")
  {
    return toSExpr(Configuration::getVersionString());
  }
  if (key == "authors")
  {
    return toSExpr("the " + Configuration::getName() + " authors");
  }
  if (key == "status")
  {
    // sat | unsat | unknown
    Result status = d_state->getStatus();
    switch (status.getStatus())
    {
      case Result::SAT: return "sat";
      case Result::UNSAT: return "unsat";
      default: return "unknown";
    }
  }
  if (key == "time")
  {
    return toSExpr(std::clock());
  }
  if (key == "reason-unknown")
  {
    Result status = d_state->getStatus();
    if (!status.isNull() && status.isUnknown())
    {
      std::stringstream ss;
      ss << status.getUnknownExplanation();
      std::string s = ss.str();
      transform(s.begin(), s.end(), s.begin(), ::tolower);
      return s;
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
    size_t ulevel = d_ctxManager->getNumUserLevels();
    AlwaysAssert(ulevel <= std::numeric_limits<unsigned long int>::max());
    return toSExpr(ulevel);
  }
  Assert(key == "all-options");
  // get the options, like all-statistics
  std::vector<std::vector<std::string>> res;
  for (const auto& opt : options::getNames())
  {
    res.emplace_back(
        std::vector<std::string>{opt, options::get(getOptions(), opt)});
  }
  return toSExpr(res);
}

void SolverEngine::debugCheckFormals(const std::vector<Node>& formals,
                                     Node func)
{
  for (std::vector<Node>::const_iterator i = formals.begin();
       i != formals.end();
       ++i)
  {
    if ((*i).getKind() != kind::BOUND_VARIABLE)
    {
      stringstream ss;
      ss << "All formal arguments to defined functions must be "
            "BOUND_VARIABLEs, but in the\n"
         << "definition of function " << func << ", formal\n"
         << "  " << *i << "\n"
         << "has kind " << (*i).getKind();
      throw TypeCheckingExceptionPrivate(func, ss.str());
    }
  }
}

void SolverEngine::debugCheckFunctionBody(Node formula,
                                          const std::vector<Node>& formals,
                                          Node func)
{
  TypeNode formulaType = formula.getType(d_env->getOptions().expr.typeChecking);
  TypeNode funcType = func.getType();
  // We distinguish here between definitions of constants and functions,
  // because the type checking for them is subtly different.  Perhaps we
  // should instead have SolverEngine::defineFunction() and
  // SolverEngine::defineConstant() for better clarity, although then that
  // doesn't match the SMT-LIBv2 standard...
  if (formals.size() > 0)
  {
    TypeNode rangeType = funcType.getRangeType();
    if (formulaType != rangeType)
    {
      stringstream ss;
      ss << "Type of defined function does not match its declaration\n"
         << "The function  : " << func << "\n"
         << "Declared type : " << rangeType << "\n"
         << "The body      : " << formula << "\n"
         << "Body type     : " << formulaType;
      throw TypeCheckingExceptionPrivate(func, ss.str());
    }
  }
  else
  {
    if (formulaType != funcType)
    {
      stringstream ss;
      ss << "Declared type of defined constant does not match its definition\n"
         << "The constant   : " << func << "\n"
         << "Declared type  : " << funcType << "\n"
         << "The definition : " << formula << "\n"
         << "Definition type: " << formulaType;
      throw TypeCheckingExceptionPrivate(func, ss.str());
    }
  }
}

void SolverEngine::defineFunction(Node func,
                                  const std::vector<Node>& formals,
                                  Node formula,
                                  bool global)
{
  beginCall();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  Node def = formula;
  if (!formals.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    def = nm->mkNode(
        kind::LAMBDA, nm->mkNode(kind::BOUND_VAR_LIST, formals), def);
  }
  Node feq = func.eqNode(def);
  d_smtSolver->getAssertions().addDefineFunDefinition(feq, global);
}

void SolverEngine::defineFunction(Node func, Node lambda, bool global)
{
  beginCall();
  // A define-fun is treated as a (higher-order) assertion. It is provided
  // to the assertions object. It will be added as a top-level substitution
  // within this class, possibly multiple times if global is true.
  Node feq = func.eqNode(lambda);
  d_smtSolver->getAssertions().addDefineFunDefinition(feq, global);
}

void SolverEngine::defineFunctionsRec(
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas,
    bool global)
{
  beginCall();
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

  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = funcs.size(); i < size; i++)
  {
    // we assert a quantified formula
    Node func_app;
    // make the function application
    if (formals[i].empty())
    {
      // it has no arguments
      func_app = funcs[i];
    }
    else
    {
      std::vector<Node> children;
      children.push_back(funcs[i]);
      children.insert(children.end(), formals[i].begin(), formals[i].end());
      func_app = nm->mkNode(kind::APPLY_UF, children);
    }
    Node lem = nm->mkNode(kind::EQUAL, func_app, formulas[i]);
    if (!formals[i].empty())
    {
      // set the attribute to denote this is a function definition
      Node aexpr = nm->mkNode(kind::INST_ATTRIBUTE, func_app);
      aexpr = nm->mkNode(kind::INST_PATTERN_LIST, aexpr);
      FunDefAttribute fda;
      func_app.setAttribute(fda, true);
      // make the quantified formula
      Node boundVars = nm->mkNode(kind::BOUND_VAR_LIST, formals[i]);
      lem = nm->mkNode(kind::FORALL, boundVars, lem, aexpr);
    }
    // Assert the quantified formula. Notice we don't call assertFormula
    // directly, since we should call a private member method since we have
    // already ensuring this SolverEngine is initialized above.
    // add define recursive definition to the assertions
    d_smtSolver->getAssertions().addDefineFunDefinition(lem, global);
  }
}

void SolverEngine::defineFunctionRec(Node func,
                                     const std::vector<Node>& formals,
                                     Node formula,
                                     bool global)
{
  std::vector<Node> funcs;
  funcs.push_back(func);
  std::vector<std::vector<Node>> formals_multi;
  formals_multi.push_back(formals);
  std::vector<Node> formulas;
  formulas.push_back(formula);
  defineFunctionsRec(funcs, formals_multi, formulas, global);
}

TheoryModel* SolverEngine::getAvailableModel(const char* c) const
{
  if (!d_env->getOptions().theory.assignFunctionValues)
  {
    std::stringstream ss;
    ss << "Cannot " << c << " when --assign-function-values is false.";
    throw RecoverableModalException(ss.str().c_str());
  }

  if (d_state->getMode() != SmtMode::SAT
      && d_state->getMode() != SmtMode::SAT_UNKNOWN)
  {
    std::stringstream ss;
    ss << "Cannot " << c
       << " unless immediately preceded by SAT or UNKNOWN response.";
    throw RecoverableModalException(ss.str().c_str());
  }

  if (!d_env->getOptions().smt.produceModels)
  {
    std::stringstream ss;
    ss << "Cannot " << c << " when produce-models options is off.";
    throw ModalException(ss.str().c_str());
  }

  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  Assert(te != nullptr);
  // If the solver is in UNKNOWN mode, we use the latest available model (e.g.,
  // one that was generated for a last call check). Note that the model is SAT
  // context-independent internally, so this works even if the SAT solver has
  // backtracked since the model was generated. We disable the resource manager
  // while building or getting the model. In general, we should not be spending
  // resources while building a model, but this ensures that we return a model
  // if a problem was solved within the allocated resources.
  getResourceManager()->setEnabled(false);
  TheoryModel* m = d_state->getMode() == SmtMode::SAT_UNKNOWN
                       ? te->getModel()
                       : te->getBuiltModel();
  getResourceManager()->setEnabled(true);

  if (m == nullptr)
  {
    std::stringstream ss;
    ss << "Cannot " << c
       << " since model is not available. Perhaps the most recent call to "
          "check-sat was interrupted?";
    throw RecoverableModalException(ss.str().c_str());
  }
  // compute the model core if necessary and not done so already
  const Options& opts = d_env->getOptions();
  if (opts.smt.modelCoresMode != options::ModelCoresMode::NONE
      && !m->isUsingModelCore())
  {
    // If we enabled model cores, we compute a model core for m based on our
    // (expanded) assertions using the model core builder utility. Notice that
    // we get the assertions using the getAssertionsInternal, which does not
    // impact whether we are in "sat" mode
    std::vector<Node> asserts = getAssertionsInternal();
    d_smtSolver->getPreprocessor()->applySubstitutions(asserts);
    ModelCoreBuilder mcb(*d_env.get());
    mcb.setModelCore(asserts, m, opts.smt.modelCoresMode);
  }

  return m;
}

QuantifiersEngine* SolverEngine::getAvailableQuantifiersEngine(
    const char* c) const
{
  QuantifiersEngine* qe = d_smtSolver->getQuantifiersEngine();
  if (qe == nullptr)
  {
    std::stringstream ss;
    ss << "Cannot " << c << " when quantifiers are not present.";
    throw ModalException(ss.str().c_str());
  }
  return qe;
}

Result SolverEngine::checkSat()
{
  beginCall(true);
  Result res = checkSatInternal({});
  endCall();
  return res;
}

Result SolverEngine::checkSat(const Node& assumption)
{
  beginCall(true);
  std::vector<Node> assump;
  if (!assumption.isNull())
  {
    assump.push_back(assumption);
  }
  Result res = checkSatInternal(assump);
  endCall();
  return res;
}

Result SolverEngine::checkSat(const std::vector<Node>& assumptions)
{
  beginCall(true);
  Result res = checkSatInternal(assumptions);
  endCall();
  return res;
}

Result SolverEngine::checkSatInternal(const std::vector<Node>& assumptions)
{
  ensureWellFormedTerms(assumptions, "checkSat");

  Trace("smt") << "SolverEngine::checkSat(" << assumptions << ")" << endl;
  // update the state to indicate we are about to run a check-sat
  d_state->notifyCheckSat();

  // Call the SMT solver driver to check for satisfiability. Note that in the
  // case of options like e.g. deep restarts, this may invokve multiple calls
  // to check satisfiability in the underlying SMT solver
  Result r = d_smtDriver->checkSat(assumptions);

  Trace("smt") << "SolverEngine::checkSat(" << assumptions << ") => " << r
               << endl;
  // notify our state of the check-sat result
  d_state->notifyCheckSatResult(r);

  // Check that SAT results generate a model correctly.
  if (d_env->getOptions().smt.checkModels)
  {
    if (r.getStatus() == Result::SAT)
    {
      checkModel();
    }
  }
  // Check that UNSAT results generate a proof correctly.
  if (d_env->getOptions().smt.checkProofs)
  {
    if (r.getStatus() == Result::UNSAT)
    {
      checkProof();
    }
  }
  // Check that UNSAT results generate an unsat core correctly.
  if (d_env->getOptions().smt.checkUnsatCores)
  {
    if (r.getStatus() == Result::UNSAT)
    {
      TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
      checkUnsatCore();
    }
  }

  if (d_env->getOptions().base.statisticsEveryQuery)
  {
    printStatisticsDiff();
  }

  // set the filename on the result
  const std::string& filename = d_env->getOptions().driver.filename;
  return Result(r, filename);
}

std::pair<Result, std::vector<Node>> SolverEngine::getTimeoutCore()
{
  Trace("smt") << "SolverEngine::getTimeoutCore()" << std::endl;
  beginCall(true);
  // refresh the assertions, to ensure we have applied preprocessing to
  // all current assertions
  d_smtDriver->refreshAssertions();
  TimeoutCoreManager tcm(*d_env.get());
  // get the preprocessed assertions
  const context::CDList<Node>& assertions =
      d_smtSolver->getPreprocessedAssertions();
  std::vector<Node> passerts;
  for (const Node& a : assertions)
  {
    passerts.push_back(a);
  }
  const context::CDHashMap<size_t, Node>& ppsm =
      d_smtSolver->getPreprocessedSkolemMap();
  std::map<size_t, Node> ppSkolemMap;
  for (auto& pk : ppsm)
  {
    ppSkolemMap[pk.first] = pk.second;
  }
  std::pair<Result, std::vector<Node>> ret =
      tcm.getTimeoutCore(passerts, ppSkolemMap);
  // convert the preprocessed assertions to input assertions
  std::vector<Node> core = convertPreprocessedToInput(ret.second, true);
  endCall();
  return std::pair<Result, std::vector<Node>>(ret.first, core);
}

std::vector<Node> SolverEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  if (!d_env->getOptions().smt.unsatAssumptions)
  {
    throw ModalException(
        "Cannot get unsat assumptions when produce-unsat-assumptions option "
        "is off.");
  }
  if (d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get unsat assumptions unless immediately preceded by "
        "UNSAT.");
  }
  UnsatCore core = getUnsatCoreInternal();
  std::vector<Node> res;
  std::vector<Node>& assumps = d_smtSolver->getAssertions().getAssumptions();
  for (const Node& e : assumps)
  {
    if (std::find(core.begin(), core.end(), e) != core.end())
    {
      res.push_back(e);
    }
  }
  return res;
}

void SolverEngine::assertFormula(const Node& formula)
{
  beginCall();
  ensureWellFormedTerm(formula, "assertFormula");
  assertFormulaInternal(formula);
}

void SolverEngine::assertFormulaInternal(const Node& formula)
{
  // as an optimization we do not check whether formula is well-formed here, and
  // defer this check for certain cases within the assertions module.
  Trace("smt") << "SolverEngine::assertFormula(" << formula << ")" << endl;
  d_smtSolver->getAssertions().assertFormula(formula);
}

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SolverEngine::declareSygusVar(Node var)
{
  beginCall();
  d_sygusSolver->declareSygusVar(var);
}

void SolverEngine::declareSynthFun(Node func,
                                   TypeNode sygusType,
                                   bool isInv,
                                   const std::vector<Node>& vars)
{
  beginCall();
  d_sygusSolver->declareSynthFun(func, sygusType, isInv, vars);
}
void SolverEngine::declareSynthFun(Node func,
                                   bool isInv,
                                   const std::vector<Node>& vars)
{
  beginCall();
  // use a null sygus type
  TypeNode sygusType;
  d_sygusSolver->declareSynthFun(func, sygusType, isInv, vars);
}

void SolverEngine::assertSygusConstraint(Node n, bool isAssume)
{
  beginCall();
  d_sygusSolver->assertSygusConstraint(n, isAssume);
}

std::vector<Node> SolverEngine::getSygusConstraints()
{
  beginCall();
  return d_sygusSolver->getSygusConstraints();
}

std::vector<Node> SolverEngine::getSygusAssumptions()
{
  beginCall();
  return d_sygusSolver->getSygusAssumptions();
}

void SolverEngine::assertSygusInvConstraint(Node inv,
                                            Node pre,
                                            Node trans,
                                            Node post)
{
  beginCall();
  d_sygusSolver->assertSygusInvConstraint(inv, pre, trans, post);
}

SynthResult SolverEngine::checkSynth(bool isNext)
{
  beginCall();
  if (isNext && d_state->getMode() != SmtMode::SYNTH)
  {
    throw RecoverableModalException(
        "Cannot check-synth-next unless immediately preceded by a successful "
        "call to check-synth(-next).");
  }
  SynthResult r = d_sygusSolver->checkSynth(isNext);
  d_state->notifyCheckSynthResult(r);
  return r;
}

Node SolverEngine::findSynth(modes::FindSynthTarget fst, const TypeNode& gtn)
{
  beginCall();
  Trace("smt") << "SolverEngine::findSynth " << fst << std::endl;
  // The grammar(s) we will use. This may be more than one if doing rewrite
  // rule synthesis from input or if no grammar is specified, indicating we
  // wish to use grammars for each function-to-synthesize.
  std::vector<TypeNode> gtnu;
  if (!gtn.isNull())
  {
    // Must generalize the free symbols in the grammar to variables. Otherwise,
    // certain algorithms (e.g. sampling) will fail to treat the free symbols
    // of the grammar as inputs to the term to find.
    TypeNode ggtn = theory::datatypes::utils::generalizeSygusType(gtn);
    gtnu.push_back(ggtn);
  }
  // if synthesizing rewrite rules from input, we infer the grammar here
  if (fst == modes::FindSynthTarget::FIND_SYNTH_TARGET_REWRITE_INPUT)
  {
    if (!gtn.isNull())
    {
      Warning() << "Ignoring grammar provided to find-synth :rewrite_input"
                << std::endl;
    }
    uint64_t nvars = options().quantifiers.sygusRewSynthInputNVars;
    std::vector<Node> asserts = getAssertionsInternal();
    gtnu = preprocessing::passes::SynthRewRulesPass::getGrammarsFrom(asserts,
                                                                     nvars);
    if (gtnu.empty())
    {
      Warning() << "Could not find grammar in find-synth :rewrite_input"
                << std::endl;
      return Node::null();
    }
  }
  if (d_sygusSolver != nullptr && gtnu.empty())
  {
    // if no type provided, and the sygus solver exists,
    std::vector<std::pair<Node, TypeNode>> funs =
        d_sygusSolver->getSynthFunctions();
    for (const std::pair<Node, TypeNode>& f : funs)
    {
      if (!f.second.isNull())
      {
        gtnu.push_back(f.second);
      }
    }
  }
  if (gtnu.empty())
  {
    throw RecoverableModalException(
        "No grammar available in call to find-synth. Either provide one or "
        "ensure synth-fun has been called.");
  }
  // initialize find synthesis solver if not done so already
  if (d_findSynthSolver == nullptr)
  {
    d_findSynthSolver.reset(new FindSynthSolver(*d_env.get()));
  }
  Node ret = d_findSynthSolver->findSynth(fst, gtnu);
  return ret;
}

Node SolverEngine::findSynthNext()
{
  beginCall();
  if (d_state->getMode() != SmtMode::FIND_SYNTH)
  {
    throw RecoverableModalException(
        "Cannot find-synth-next unless immediately preceded by a successful "
        "call to find-synth(-next).");
  }
  return d_findSynthSolver->findSynthNext();
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SolverEngine::declarePool(const Node& p,
                               const std::vector<Node>& initValue)
{
  Assert(p.isVar() && p.getType().isSet());
  beginCall();
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("declareTermPool");
  qe->declarePool(p, initValue);
}

void SolverEngine::declareOracleFun(
    Node var, std::function<std::vector<Node>(const std::vector<Node>&)> fn)
{
  beginCall();
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("declareOracleFun");
  qe->declareOracleFun(var);
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> inputs;
  std::vector<Node> outputs;
  TypeNode tn = var.getType();
  Node app;
  if (tn.isFunction())
  {
    const std::vector<TypeNode>& argTypes = tn.getArgTypes();
    for (const TypeNode& t : argTypes)
    {
      inputs.push_back(nm->mkBoundVar(t));
    }
    outputs.push_back(nm->mkBoundVar(tn.getRangeType()));
    std::vector<Node> appc;
    appc.push_back(var);
    appc.insert(appc.end(), inputs.begin(), inputs.end());
    app = nm->mkNode(kind::APPLY_UF, appc);
  }
  else
  {
    outputs.push_back(nm->mkBoundVar(tn.getRangeType()));
    app = var;
  }
  // makes equality assumption
  Node assume = nm->mkNode(kind::EQUAL, app, outputs[0]);
  // no constraints
  Node constraint = nm->mkConst(true);
  // make the oracle constant which carries the method implementation
  Oracle oracle(fn);
  Node o = NodeManager::currentNM()->mkOracle(oracle);
  // set the attribute, which ensures we remember the method implementation for
  // the oracle function
  var.setAttribute(theory::OracleInterfaceAttribute(), o);
  // define the oracle interface
  Node q = quantifiers::OracleEngine::mkOracleInterface(
      inputs, outputs, assume, constraint, o);
  // assert it
  assertFormula(q);
}

Node SolverEngine::simplify(const Node& t)
{
  beginCall(true);
  // ensure we've processed assertions
  d_smtDriver->refreshAssertions();
  // apply substitutions
  Node tt = d_smtSolver->getPreprocessor()->applySubstitutions(t);
  // now rewrite
  Node ret = d_env->getRewriter()->rewrite(tt);
  // make so that the returned term does not involve arithmetic subtyping
  SubtypeElimNodeConverter senc;
  ret = senc.convert(ret);
  endCall();
  return ret;
}

Node SolverEngine::getValue(const Node& t) const
{
  ensureWellFormedTerm(t, "get value");
  Trace("smt") << "SMT getValue(" << t << ")" << endl;
  TypeNode expectedType = t.getType();

  // We must expand definitions here, which replaces certain subterms of t
  // by the form that is used internally. This is necessary for some corner
  // cases of get-value to be accurate, e.g., when getting the value of
  // a division-by-zero term, we require getting the appropriate skolem
  // function corresponding to division-by-zero which may have been used during
  // the previous satisfiability check.
  std::unordered_map<Node, Node> cache;
  ExpandDefs expDef(*d_env.get());
  // Must apply substitutions first to ensure we expand definitions in the
  // solved form of t as well.
  Node n = d_smtSolver->getPreprocessor()->applySubstitutions(t);
  n = expDef.expandDefinitions(n, cache);

  Trace("smt") << "--- getting value of " << n << endl;
  // There are two ways model values for terms are computed (for historical
  // reasons).  One way is that used in check-model; the other is that
  // used by the Model classes.  It's not clear to me exactly how these
  // two are different, but they need to be unified.  This ugly hack here
  // is to fix bug 554 until we can revamp boolean-terms and models [MGD]

  // AJR : necessary?
  if (!n.getType().isFunction())
  {
    n = d_env->getRewriter()->rewrite(n);
  }

  Trace("smt") << "--- getting value of " << n << endl;
  TheoryModel* m = getAvailableModel("get-value");
  Assert(m != nullptr);
  Node resultNode = m->getValue(n);
  Trace("smt") << "--- got value " << n << " = " << resultNode << endl;
  Trace("smt") << "--- type " << resultNode.getType() << endl;
  Trace("smt") << "--- expected type " << expectedType << endl;

  // type-check the result we got
  Assert(resultNode.isNull() || resultNode.getType() == expectedType)
      << "Run with -t smt for details.";

  // Ensure it's a value (constant or const-ish like real algebraic
  // numbers), or a lambda (for uninterpreted functions). This assertion only
  // holds for models that do not have approximate values.
  if (!m->isValue(resultNode))
  {
    d_env->warning() << "Could not evaluate " << resultNode
                     << " in getValue." << std::endl;
  }

  if (d_env->getOptions().smt.abstractValues)
  {
    TypeNode rtn = resultNode.getType();
    if (rtn.isArray())
    {
      // construct the skolem function
      SkolemManager* skm = NodeManager::currentNM()->getSkolemManager();
      Node a =
          skm->mkSkolemFunction(SkolemFunId::ABSTRACT_VALUE, rtn, resultNode);
      // add to top-level substitutions if applicable
      theory::TrustSubstitutionMap& tsm = d_env->getTopLevelSubstitutions();
      if (!tsm.get().hasSubstitution(resultNode))
      {
        tsm.addSubstitution(resultNode, a);
      }
      resultNode = a;
      Trace("smt") << "--- abstract value >> " << resultNode << endl;
    }
  }

  return resultNode;
}

std::vector<Node> SolverEngine::getValues(const std::vector<Node>& exprs) const
{
  std::vector<Node> result;
  for (const Node& e : exprs)
  {
    result.push_back(getValue(e));
  }
  return result;
}

std::vector<Node> SolverEngine::getModelDomainElements(TypeNode tn) const
{
  Assert(tn.isUninterpretedSort());
  TheoryModel* m = getAvailableModel("getModelDomainElements");
  return m->getDomainElements(tn);
}

bool SolverEngine::isModelCoreSymbol(Node n)
{
  Assert(n.isVar());
  const Options& opts = d_env->getOptions();
  if (opts.smt.modelCoresMode == options::ModelCoresMode::NONE)
  {
    // if the model core mode is none, we are always a model core symbol
    return true;
  }
  TheoryModel* tm = getAvailableModel("isModelCoreSymbol");
  return tm->isModelCoreSymbol(n);
}

std::string SolverEngine::getModel(const std::vector<TypeNode>& declaredSorts,
                                   const std::vector<Node>& declaredFuns)
{
  // !!! Note that all methods called here should have a version at the API
  // level. This is to ensure that the information associated with a model is
  // completely accessible by the user. This is currently not rigorously
  // enforced. An alternative design would be to have this method implemented
  // at the API level, but this makes exceptions in the text interface less
  // intuitive.
  TheoryModel* tm = getAvailableModel("get model");
  // use the smt::Model model utility for printing
  const Options& opts = d_env->getOptions();
  bool isKnownSat = (d_state->getMode() == SmtMode::SAT);
  Model m(isKnownSat, opts.driver.filename);
  // set the model declarations, which determines what is printed in the model
  for (const TypeNode& tn : declaredSorts)
  {
    m.addDeclarationSort(tn, getModelDomainElements(tn));
  }
  bool usingModelCores =
      (opts.smt.modelCoresMode != options::ModelCoresMode::NONE);
  for (const Node& n : declaredFuns)
  {
    if (usingModelCores && !tm->isModelCoreSymbol(n))
    {
      // skip if not in model core
      continue;
    }
    Node value = tm->getValue(n);
    m.addDeclarationTerm(n, value);
  }
  // for separation logic
  TypeNode locT, dataT;
  if (getSepHeapTypes(locT, dataT))
  {
    std::pair<Node, Node> sh = getSepHeapAndNilExpr();
    m.setHeapModel(sh.first, sh.second);
  }
  // print the model
  std::stringstream ssm;
  ssm << m;
  return ssm.str();
}

void SolverEngine::blockModel(modes::BlockModelsMode mode)
{
  Trace("smt") << "SMT blockModel()" << endl;
  TheoryModel* m = getAvailableModel("block model");

  // get expanded assertions
  std::vector<Node> eassertsProc = getSubstitutedAssertions();
  ModelBlocker mb(*d_env.get());
  Node eblocker = mb.getModelBlocker(eassertsProc, m, mode);
  Trace("smt") << "Block formula: " << eblocker << std::endl;

  // Must begin call now to ensure pops are processed. We cannot call this
  // above since we are accessing the model.
  beginCall();
  assertFormulaInternal(eblocker);
}

void SolverEngine::blockModelValues(const std::vector<Node>& exprs)
{
  Trace("smt") << "SMT blockModelValues()" << endl;
  for (const Node& e : exprs)
  {
    ensureWellFormedTerm(e, "block model values");
  }

  TheoryModel* m = getAvailableModel("block model values");

  // get expanded assertions
  std::vector<Node> eassertsProc = getSubstitutedAssertions();
  // we always do block model values mode here
  ModelBlocker mb(*d_env.get());
  Node eblocker = mb.getModelBlocker(
      eassertsProc, m, modes::BlockModelsMode::VALUES, exprs);

  // Call begin call here, for same reasons as above.
  beginCall();
  assertFormulaInternal(eblocker);
}

std::pair<Node, Node> SolverEngine::getSepHeapAndNilExpr(void)
{
  if (!getLogicInfo().isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot obtain separation logic expressions if not using the "
        "separation logic theory.";
    throw RecoverableModalException(msg);
  }
  Node heap;
  Node nil;
  TheoryModel* tm = getAvailableModel("get separation logic heap and nil");
  if (!tm->getHeapModel(heap, nil))
  {
    const char* msg =
        "Failed to obtain heap/nil "
        "expressions from theory model.";
    throw RecoverableModalException(msg);
  }
  return std::make_pair(heap, nil);
}

std::vector<Node> SolverEngine::getAssertionsInternal() const
{
  Assert(d_state->isFullyInited());
  // ensure that global declarations are processed
  d_smtSolver->getAssertions().refresh();
  const CDList<Node>& al = d_smtSolver->getAssertions().getAssertionList();
  std::vector<Node> res;
  for (const Node& n : al)
  {
    res.emplace_back(n);
  }
  return res;
}

const Options& SolverEngine::options() const { return d_env->getOptions(); }

void SolverEngine::ensureWellFormedTerm(const Node& n,
                                        const std::string& src) const
{
  if (Configuration::isAssertionBuild())
  {
    bool wasShadow = false;
    if (expr::hasFreeOrShadowedVar(n, wasShadow))
    {
      std::stringstream se;
      se << "Cannot process term " << n << " with ";
      if (wasShadow)
      {
        se << "shadowed variables " << std::endl;
      }
      else
      {
        std::unordered_set<internal::Node> fvs;
        expr::getFreeVariables(n, fvs);
        se << "free variables: " << fvs << std::endl;
      }
      throw ModalException(se.str().c_str());
    }
  }
}

void SolverEngine::ensureWellFormedTerms(const std::vector<Node>& ns,
                                         const std::string& src) const
{
  if (Configuration::isAssertionBuild())
  {
    for (const Node& n : ns)
    {
      ensureWellFormedTerm(n, src);
    }
  }
}

std::vector<Node> SolverEngine::convertPreprocessedToInput(
    const std::vector<Node>& ppa, bool isInternal)
{
  std::vector<Node> core;
  CDProof cdp(*d_env);
  Node fnode = NodeManager::currentNM()->mkConst(false);
  cdp.addStep(fnode, PfRule::SAT_REFUTATION, ppa, {});
  std::shared_ptr<ProofNode> pepf = cdp.getProofFor(fnode);
  Assert(pepf != nullptr);
  std::shared_ptr<ProofNode> pfn =
      d_pfManager->connectProofToAssertions(pepf, *d_smtSolver.get());
  d_ucManager->getUnsatCore(
      pfn, d_smtSolver->getAssertions(), core, isInternal);
  return core;
}

std::vector<Node> SolverEngine::getSubstitutedAssertions()
{
  std::vector<Node> easserts = getAssertions();
  // must expand definitions
  d_smtSolver->getPreprocessor()->applySubstitutions(easserts);
  return easserts;
}

Env& SolverEngine::getEnv() { return *d_env.get(); }

void SolverEngine::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  if (d_state->isFullyInited())
  {
    throw ModalException(
        "Cannot set logic in SolverEngine after the engine has "
        "finished initializing.");
  }
  if (!getLogicInfo().isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot declare heap if not using the separation logic theory.";
    throw RecoverableModalException(msg);
  }
  TypeNode locT2, dataT2;
  if (getSepHeapTypes(locT2, dataT2))
  {
    std::stringstream ss;
    ss << "ERROR: cannot declare heap types for separation logic more than "
          "once.  We are declaring heap of type ";
    ss << locT << " -> " << dataT << ", but we already have ";
    ss << locT2 << " -> " << dataT2;
    throw LogicException(ss.str());
  }
  d_env->declareSepHeap(locT, dataT);
}

bool SolverEngine::getSepHeapTypes(TypeNode& locT, TypeNode& dataT)
{
  if (!d_env->hasSepHeap())
  {
    return false;
  }
  locT = d_env->getSepLocType();
  dataT = d_env->getSepDataType();
  return true;
}

Node SolverEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Node SolverEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

std::vector<Node> SolverEngine::getLearnedLiterals(modes::LearnedLitType t)
{
  Trace("smt") << "SMT getLearnedLiterals()" << std::endl;
  // note that the default mode for learned literals is via the prop engine,
  // although other modes could use the preprocessor
  PropEngine* pe = d_smtSolver->getPropEngine();
  Assert(pe != nullptr);
  return pe->getLearnedZeroLevelLiterals(t);
}

void SolverEngine::checkProof()
{
  Assert(d_env->getOptions().smt.produceProofs);
  // internal check the proof
  PropEngine* pe = d_smtSolver->getPropEngine();
  Assert(pe != nullptr);
  if (d_env->getOptions().proof.proofCheck == options::ProofCheckMode::EAGER)
  {
    pe->checkProof(d_smtSolver->getAssertions().getAssertionList());
  }
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pePfn = pe->getProof();
  if (d_env->getOptions().smt.checkProofs)
  {
    // connect proof to assertions, which will fail if the proof is malformed
    d_pfManager->connectProofToAssertions(pePfn, *d_smtSolver.get());
  }
}

void SolverEngine::beginCall(bool needsRLlimit)
{
  // ensure this solver engine has been initialized
  finishInit();
  // ensure the context is current
  d_ctxManager->doPendingPops();
  // optionally, ensure the resource manager's state is current
  if (needsRLlimit)
  {
    ResourceManager* rm = getResourceManager();
    rm->beginCall();
    Trace("limit") << "SolverEngine::beginCall(): cumulative millis "
                   << rm->getTimeUsage() << ", resources "
                   << rm->getResourceUsage() << std::endl;
  }
}

void SolverEngine::endCall()
{
  // refresh the resource manager (for stats)
  ResourceManager* rm = getResourceManager();
  rm->refresh();
  Trace("limit") << "SolverEngine::endCall(): cumulative millis "
                 << rm->getTimeUsage() << ", resources "
                 << rm->getResourceUsage() << std::endl;
}

StatisticsRegistry& SolverEngine::getStatisticsRegistry()
{
  return d_env->getStatisticsRegistry();
}

UnsatCore SolverEngine::getUnsatCoreInternal(bool isInternal)
{
  if (!d_env->getOptions().smt.produceUnsatCores)
  {
    throw ModalException(
        "Cannot get an unsat core when produce-unsat-cores or produce-proofs "
        "option is off.");
  }
  if (d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by "
        "UNSAT response.");
  }
  // generate with new proofs
  PropEngine* pe = d_smtSolver->getPropEngine();
  Assert(pe != nullptr);

  // make the proof corresponding to a dummy step (SAT_REFUTATION) of the
  // unsat core computed by the prop engine
  std::vector<Node> pcore;
  pe->getUnsatCore(pcore);
  std::vector<Node> core = convertPreprocessedToInput(pcore, isInternal);
  return UnsatCore(core);
}

void SolverEngine::checkUnsatCore()
{
  Assert(d_env->getOptions().smt.produceUnsatCores)
      << "cannot check unsat core if unsat cores are turned off";

  d_env->verbose(1) << "SolverEngine::checkUnsatCore(): generating unsat core"
                    << std::endl;
  UnsatCore core = getUnsatCoreInternal();

  // initialize the core checker
  std::unique_ptr<SolverEngine> coreChecker;
  initializeSubsolver(coreChecker, *d_env.get());
  // disable all proof options
  SetDefaults::disableChecking(coreChecker->getOptions());

  d_env->verbose(1) << "SolverEngine::checkUnsatCore(): pushing core assertions"
                    << std::endl;
  // set up the subsolver
  std::unordered_set<Node> adefs =
      d_smtSolver->getAssertions().getCurrentAssertionListDefitions();
  std::unordered_set<Node> removed;
  assertToSubsolver(*coreChecker.get(), core.getCore(), adefs, removed);
  Result r;
  try
  {
    r = coreChecker->checkSat();
  }
  catch (...)
  {
    throw;
  }
  d_env->verbose(1) << "SolverEngine::checkUnsatCore(): result is " << r
                    << std::endl;
  if (r.isUnknown())
  {
    d_env->warning() << "SolverEngine::checkUnsatCore(): could not check core result "
                 "unknown."
              << std::endl;
  }
  else if (r.getStatus() == Result::SAT)
  {
    InternalError()
        << "SolverEngine::checkUnsatCore(): produced core was satisfiable.";
  }
}

void SolverEngine::checkModel(bool hardFailure)
{
  const CDList<Node>& al = d_smtSolver->getAssertions().getAssertionList();
  // we always enable the assertion list, so it is able to be checked

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  d_env->verbose(1) << "SolverEngine::checkModel(): generating model"
                    << std::endl;
  TheoryModel* m = getAvailableModel("check model");
  Assert(m != nullptr);

  // check the model with the theory engine for debugging
  if (options().smt.debugCheckModels)
  {
    TheoryEngine* te = d_smtSolver->getTheoryEngine();
    Assert(te != nullptr);
    te->checkTheoryAssertionsWithModel(hardFailure);
  }

  // check the model with the check models utility
  Assert(d_checkModels != nullptr);
  d_checkModels->checkModel(m, al, hardFailure);
}

UnsatCore SolverEngine::getUnsatCore()
{
  Trace("smt") << "SMT getUnsatCore()" << std::endl;
  return getUnsatCoreInternal(false);
}

void SolverEngine::getRelevantQuantTermVectors(
    std::map<Node, InstantiationList>& insts,
    std::map<Node, std::vector<Node>>& sks,
    bool getDebugInfo)
{
  Assert(d_state->getMode() == SmtMode::UNSAT);
  // generate with new proofs
  PropEngine* pe = d_smtSolver->getPropEngine();
  Assert(pe != nullptr);
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pfn = pe->getProof();
  // note that we don't have to connect the SAT proof to the input assertions,
  // and preprocessing proofs don't impact what instantiations are used
  d_ucManager->getRelevantQuantTermVectors(pfn, insts, sks, getDebugInfo);
}

std::string SolverEngine::getProof(modes::ProofComponent c)
{
  Trace("smt") << "SMT getProof()\n";
  if (!d_env->getOptions().smt.produceProofs)
  {
    throw ModalException("Cannot get a proof when proof option is off.");
  }
  // The component modes::PROOF_COMPONENT_PREPROCESS returns the proof of
  // all preprocessed assertions. It does not require being in an unsat state.
  if (c != modes::PROOF_COMPONENT_RAW_PREPROCESS
      && d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get a proof unless immediately preceded by "
        "UNSAT response.");
  }
  // determine if we should get the full proof from the SAT solver
  PropEngine* pe = d_smtSolver->getPropEngine();
  Assert(pe != nullptr);
  std::vector<std::shared_ptr<ProofNode>> ps;
  bool connectToPreprocess = false;
  bool connectMkOuterScope = false;
  bool commentProves = true;
  options::ProofFormatMode mode = options::ProofFormatMode::NONE;
  if (c == modes::PROOF_COMPONENT_RAW_PREPROCESS)
  {
    // use all preprocessed assertions
    const context::CDList<Node>& assertions =
        d_smtSolver->getPreprocessedAssertions();
    connectToPreprocess = true;
    // We start with (ASSUME a) for each preprocessed assertion a. This
    // proof will be connected to the proof of preprocessing for a.
    ProofNodeManager* pnm = d_pfManager->getProofNodeManager();
    for (const Node& a : assertions)
    {
      ps.push_back(pnm->mkAssume(a));
    }
  }
  else if (c == modes::PROOF_COMPONENT_SAT)
  {
    ps.push_back(pe->getProof(false));
    // don't need to comment that it proves false
    commentProves = false;
  }
  else if (c == modes::PROOF_COMPONENT_THEORY_LEMMAS
           || c == modes::PROOF_COMPONENT_PREPROCESS)
  {
    ps = pe->getProofLeaves(c);
    // connect to preprocess proofs for preprocess mode
    connectToPreprocess = (c == modes::PROOF_COMPONENT_PREPROCESS);
  }
  else if (c == modes::PROOF_COMPONENT_FULL)
  {
    ps.push_back(pe->getProof(true));
    connectToPreprocess = true;
    connectMkOuterScope = true;
    // don't need to comment that it proves false
    commentProves = false;
    // we print in the format based on the proof mode
    mode = options().proof.proofFormatMode;
  }
  else
  {
    std::stringstream ss;
    ss << "Unknown proof component " << c << std::endl;
    throw RecoverableModalException(ss.str());
  }

  Assert(d_pfManager);
  std::ostringstream ss;
  // connect proofs to preprocessing, if specified
  if (connectToPreprocess)
  {
    ProofScopeMode scopeMode = connectMkOuterScope
                                   ? ProofScopeMode::DEFINITIONS_AND_ASSERTIONS
                                   : ProofScopeMode::NONE;
    for (std::shared_ptr<ProofNode>& p : ps)
    {
      Assert(p != nullptr);
      p = d_pfManager->connectProofToAssertions(
          p, *d_smtSolver.get(), scopeMode);
    }
  }
  // print all proofs
  // we currently only print outermost parentheses if the format is NONE
  if (mode == options::ProofFormatMode::NONE)
  {
    ss << "(" << std::endl;
  }
  for (std::shared_ptr<ProofNode>& p : ps)
  {
    if (commentProves)
    {
      ss << "(!" << std::endl;
    }
    d_pfManager->printProof(ss, p, mode);
    ss << std::endl;
    if (commentProves)
    {
      ss << ":proves " << p->getResult() << ")" << std::endl;
    }
  }
  if (mode == options::ProofFormatMode::NONE)
  {
    ss << ")" << std::endl;
  }
  return ss.str();
}

void SolverEngine::printInstantiations(std::ostream& out)
{
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("printInstantiations");

  // First, extract and print the skolemizations
  bool printed = false;
  bool reqNames = !d_env->getOptions().quantifiers.printInstFull;

  // Extract the skolemizations and instantiations
  std::map<Node, std::vector<Node>> sks;
  std::map<Node, InstantiationList> rinsts;
  if ((d_env->getOptions().smt.produceProofs
       && d_env->getOptions().smt.proofMode == options::ProofMode::FULL)
      && getSmtMode() == SmtMode::UNSAT)
  {
    // minimize skolemizations and instantiations based on proof manager
    getRelevantQuantTermVectors(
        rinsts, sks, options().driver.dumpInstantiationsDebug);
  }
  else
  {
    // get all skolem term vectors
    qe->getSkolemTermVectors(sks);
    // get all instantiations
    std::map<Node, std::vector<std::vector<Node>>> insts;
    qe->getInstantiationTermVectors(insts);
    for (const std::pair<const Node, std::vector<std::vector<Node>>>& i : insts)
    {
      // convert to instantiation list
      Node q = i.first;
      InstantiationList& ilq = rinsts[q];
      ilq.initialize(q);
      for (const std::vector<Node>& ii : i.second)
      {
        ilq.d_inst.push_back(InstantiationVec(ii));
      }
    }
  }
  // only print when in list mode
  if (d_env->getOptions().quantifiers.printInstMode
      == options::PrintInstMode::LIST)
  {
    for (const std::pair<const Node, std::vector<Node>>& s : sks)
    {
      Node name;
      if (!qe->getNameForQuant(s.first, name, reqNames))
      {
        // did not have a name and we are only printing formulas with names
        continue;
      }
      SkolemList slist(name, s.second);
      out << slist;
      printed = true;
    }
  }
  for (std::pair<const Node, InstantiationList>& i : rinsts)
  {
    if (i.second.d_inst.empty())
    {
      // no instantiations, skip
      continue;
    }
    Node name;
    if (!qe->getNameForQuant(i.first, name, reqNames))
    {
      // did not have a name and we are only printing formulas with names
      continue;
    }
    // must have a name
    if (d_env->getOptions().quantifiers.printInstMode
        == options::PrintInstMode::NUM)
    {
      out << "(num-instantiations " << name << " " << i.second.d_inst.size()
          << ")" << std::endl;
    }
    else
    {
      // take the name
      i.second.d_quant = name;
      Assert(d_env->getOptions().quantifiers.printInstMode
             == options::PrintInstMode::LIST);
      out << i.second;
    }
    printed = true;
  }
  // if we did not print anything, we indicate this
  if (!printed)
  {
    out << "none" << std::endl;
  }
}

void SolverEngine::getInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiationTermVectors");
  // get the list of all instantiations
  qe->getInstantiationTermVectors(insts);
}

bool SolverEngine::getSynthSolutions(std::map<Node, Node>& solMap)
{
  if (d_sygusSolver == nullptr)
  {
    throw RecoverableModalException(
        "Cannot get synth solutions in this context.");
  }
  bool ret = d_sygusSolver->getSynthSolutions(solMap);
  // we return false if solMap is empty, that is, when we ask for a solution
  // when none is available.
  return ret && !solMap.empty();
}

bool SolverEngine::getSubsolverSynthSolutions(std::map<Node, Node>& solMap)
{
  if (d_sygusSolver == nullptr)
  {
    throw RecoverableModalException(
        "Cannot get subsolver synth solutions in this context.");
  }
  bool ret = d_sygusSolver->getSubsolverSynthSolutions(solMap);
  // we return false if solMap is empty, that is, when we ask for a solution
  // when none is available.
  return ret && !solMap.empty();
}

Node SolverEngine::getQuantifierElimination(Node q, bool doFull)
{
  beginCall(true);
  Node result = d_quantElimSolver->getQuantifierElimination(
      q, doFull, d_isInternalSubsolver);
  endCall();
  return result;
}

Node SolverEngine::getInterpolant(const Node& conj, const TypeNode& grammarType)
{
  beginCall(true);
  std::vector<Node> axioms = getSubstitutedAssertions();
  // expand definitions in the conjecture as well
  Node conje = d_smtSolver->getPreprocessor()->applySubstitutions(conj);
  Node interpol;
  bool success =
      d_interpolSolver->getInterpolant(axioms, conje, grammarType, interpol);
  // notify the state of whether the get-interpolant call was successfuly, which
  // impacts the SMT mode.
  d_state->notifyGetInterpol(success);
  endCall();
  Assert(success == !interpol.isNull());
  return interpol;
}

Node SolverEngine::getInterpolantNext()
{
  beginCall(true);
  if (d_state->getMode() != SmtMode::INTERPOL)
  {
    throw RecoverableModalException(
        "Cannot get-interpolant-next unless immediately preceded by a "
        "successful "
        "call to get-interpolant(-next).");
  }
  Node interpol;
  bool success = d_interpolSolver->getInterpolantNext(interpol);
  // notify the state of whether the get-interpolantant-next call was successful
  d_state->notifyGetInterpol(success);
  endCall();
  Assert(success == !interpol.isNull());
  return interpol;
}

Node SolverEngine::getAbduct(const Node& conj, const TypeNode& grammarType)
{
  beginCall(true);
  std::vector<Node> axioms = getSubstitutedAssertions();
  // expand definitions in the conjecture as well
  Node conje = d_smtSolver->getPreprocessor()->applySubstitutions(conj);
  Node abd;
  bool success = d_abductSolver->getAbduct(axioms, conje, grammarType, abd);
  // notify the state of whether the get-abduct call was successful, which
  // impacts the SMT mode.
  d_state->notifyGetAbduct(success);
  endCall();
  Assert(success == !abd.isNull());
  return abd;
}

Node SolverEngine::getAbductNext()
{
  beginCall(true);
  if (d_state->getMode() != SmtMode::ABDUCT)
  {
    throw RecoverableModalException(
        "Cannot get-abduct-next unless immediately preceded by a successful "
        "call to get-abduct(-next).");
  }
  Node abd;
  bool success = d_abductSolver->getAbductNext(abd);
  // notify the state of whether the get-abduct-next call was successful
  d_state->notifyGetAbduct(success);
  Assert(success == !abd.isNull());
  return abd;
}

void SolverEngine::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiatedQuantifiedFormulas");
  qe->getInstantiatedQuantifiedFormulas(qs);
}

void SolverEngine::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node>>& tvecs)
{
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiationTermVectors");
  qe->getInstantiationTermVectors(q, tvecs);
}

std::vector<Node> SolverEngine::getAssertions()
{
  Trace("smt") << "SMT getAssertions()" << endl;
  beginCall();
  // note we always enable assertions, so it is available here
  return getAssertionsInternal();
}

void SolverEngine::getDifficultyMap(std::map<Node, Node>& dmap)
{
  Trace("smt") << "SMT getDifficultyMap()\n";
  beginCall();
  if (!d_env->getOptions().smt.produceDifficulty)
  {
    throw ModalException(
        "Cannot get difficulty when difficulty option is off.");
  }
  // the prop engine has the proof of false
  Assert(d_pfManager);
  // get difficulty map from theory engine first
  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  // do not include lemmas
  te->getDifficultyMap(dmap, false);
  // then ask proof manager to translate dmap in terms of the input
  d_pfManager->translateDifficultyMap(dmap, *d_smtSolver.get());
}

void SolverEngine::push()
{
  beginCall();
  Trace("smt") << "SMT push()" << endl;
  d_smtDriver->refreshAssertions();
  d_ctxManager->userPush();
}

void SolverEngine::pop()
{
  beginCall();
  Trace("smt") << "SMT pop()" << endl;
  d_ctxManager->userPop();

  // clear the learned literals from the preprocessor
  d_smtSolver->getPreprocessor()->clearLearnedLiterals();

  Trace("userpushpop") << "SolverEngine: popped to level "
                       << d_env->getUserContext()->getLevel() << endl;
  // should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SolverEngine::resetAssertions()
{
  if (!d_state->isFullyInited())
  {
    // We're still in Start Mode, nothing asserted yet, do nothing.
    // (see solver execution modes in the SMT-LIB standard)
    Assert(d_env->getContext()->getLevel() == 0);
    Assert(d_env->getUserContext()->getLevel() == 0);
    return;
  }

  Trace("smt") << "SMT resetAssertions()" << endl;

  d_ctxManager->notifyResetAssertions();

  // reset SmtSolver, which will construct a new prop engine
  d_smtSolver->resetAssertions();
}

void SolverEngine::interrupt()
{
  if (!d_state->isFullyInited())
  {
    return;
  }
  d_smtSolver->interrupt();
}

void SolverEngine::setResourceLimit(uint64_t units, bool cumulative)
{
  if (cumulative)
  {
    d_env->d_options.writeBase().cumulativeResourceLimit = units;
  }
  else
  {
    d_env->d_options.writeBase().perCallResourceLimit = units;
  }
}
void SolverEngine::setTimeLimit(uint64_t millis)
{
  d_env->d_options.writeBase().perCallMillisecondLimit = millis;
}

unsigned long SolverEngine::getResourceUsage() const
{
  return getResourceManager()->getResourceUsage();
}

unsigned long SolverEngine::getTimeUsage() const
{
  return getResourceManager()->getTimeUsage();
}

unsigned long SolverEngine::getResourceRemaining() const
{
  return getResourceManager()->getResourceRemaining();
}

void SolverEngine::printStatisticsSafe(int fd) const
{
  d_env->getStatisticsRegistry().printSafe(fd);
}

void SolverEngine::printStatisticsDiff() const
{
  d_env->getStatisticsRegistry().printDiff(*d_env->getOptions().base.err);
  d_env->getStatisticsRegistry().storeSnapshot();
}

void SolverEngine::setOption(const std::string& key, const std::string& value)
{
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;
  options::set(getOptions(), key, value);
}

void SolverEngine::setIsInternalSubsolver() { d_isInternalSubsolver = true; }

bool SolverEngine::isInternalSubsolver() const { return d_isInternalSubsolver; }

std::string SolverEngine::getOption(const std::string& key) const
{
  Trace("smt") << "SMT getOption(" << key << ")" << endl;
  return options::get(getOptions(), key);
}

Options& SolverEngine::getOptions() { return d_env->d_options; }

const Options& SolverEngine::getOptions() const { return d_env->getOptions(); }

ResourceManager* SolverEngine::getResourceManager() const
{
  return d_env->getResourceManager();
}

}  // namespace cvc5::internal
