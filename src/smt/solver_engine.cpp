/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/options_public.h"
#include "options/parser_options.h"
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/check_models.h"
#include "smt/env.h"
#include "smt/interpolation_solver.h"
#include "smt/listeners.h"
#include "smt/logic_exception.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/preprocessor.h"
#include "smt/proof_manager.h"
#include "smt/quant_elim_solver.h"
#include "smt/set_defaults.h"
#include "smt/smt_solver.h"
#include "smt/solver_engine_scope.h"
#include "smt/solver_engine_state.h"
#include "smt/solver_engine_stats.h"
#include "smt/sygus_solver.h"
#include "smt/unsat_core_manager.h"
#include "theory/quantifiers/instantiation_list.h"
#include "theory/quantifiers/quantifiers_attributes.h"
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
using namespace cvc5::smt;
using namespace cvc5::preprocessing;
using namespace cvc5::prop;
using namespace cvc5::context;
using namespace cvc5::theory;

namespace cvc5 {

SolverEngine::SolverEngine(NodeManager* nm, const Options* optr)
    : d_env(new Env(nm, optr)),
      d_state(new SolverEngineState(*d_env.get(), *this)),
      d_absValues(new AbstractValues(getNodeManager())),
      d_asserts(new Assertions(*d_env.get(), *d_absValues.get())),
      d_routListener(new ResourceOutListener(*this)),
      d_smtSolver(nullptr),
      d_checkModels(nullptr),
      d_pfManager(nullptr),
      d_ucManager(nullptr),
      d_sygusSolver(nullptr),
      d_abductSolver(nullptr),
      d_interpolSolver(nullptr),
      d_quantElimSolver(nullptr),
      d_isInternalSubsolver(false),
      d_stats(nullptr),
      d_scope(nullptr)
{
  // !!!!!!!!!!!!!!!!!!!!!! temporary hack: this makes the current SolverEngine
  // we are constructing the current SolverEngine in scope for the lifetime of
  // this SolverEngine, or until another SolverEngine is constructed (that
  // SolverEngine is then in scope during its lifetime). This is mostly to
  // ensure that options are always in scope, for e.g. printing expressions,
  // which rely on knowing the output language. Notice that the SolverEngine may
  // spawn new SolverEngine "subsolvers" internally. These are created, used,
  // and deleted in a modular fashion while not interleaving calls to the master
  // SolverEngine. Thus the hack here does not break this use case. On the other
  // hand, this hack breaks use cases where multiple SolverEngine objects are
  // created by the user.
  d_scope.reset(new SolverEngineScope(this));
  // listen to resource out
  getResourceManager()->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SolverEngineStatistics());
  // make the SMT solver
  d_smtSolver.reset(new SmtSolver(*d_env, *d_state, *d_absValues, *d_stats));
  // make the SyGuS solver
  d_sygusSolver.reset(new SygusSolver(*d_env.get(), *d_smtSolver));
  // make the quantifier elimination solver
  d_quantElimSolver.reset(new QuantElimSolver(*d_env.get(), *d_smtSolver));
}

bool SolverEngine::isFullyInited() const { return d_state->isFullyInited(); }
bool SolverEngine::isQueryMade() const { return d_state->isQueryMade(); }
size_t SolverEngine::getNumUserLevels() const
{
  return d_state->getNumUserLevels();
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
context::UserContext* SolverEngine::getUserContext()
{
  return d_env->getUserContext();
}
context::Context* SolverEngine::getContext() { return d_env->getContext(); }

TheoryEngine* SolverEngine::getTheoryEngine()
{
  return d_smtSolver->getTheoryEngine();
}

prop::PropEngine* SolverEngine::getPropEngine()
{
  return d_smtSolver->getPropEngine();
}

void SolverEngine::finishInit()
{
  if (d_state->isFullyInited())
  {
    // already initialized, return
    return;
  }

  // Notice that finishInitInternal is called when options are finalized. If we
  // are parsing smt2, this occurs at the moment we enter "Assert mode", page 52
  // of SMT-LIB 2.6 standard.

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

  if (d_env->getOptions().smt.produceProofs)
  {
    // ensure bound variable uses canonical bound variables
    getNodeManager()->getBoundVarManager()->enableKeepCacheValues();
    // make the proof manager
    d_pfManager.reset(new PfManager(*d_env.get()));
    PreprocessProofGenerator* pppg = d_pfManager->getPreprocessProofGenerator();
    // start the unsat core manager
    d_ucManager.reset(new UnsatCoreManager());
    // enable it in the assertions pipeline
    d_asserts->setProofGenerator(pppg);
    // enabled proofs in the preprocessor
    d_smtSolver->getPreprocessor()->setProofGenerator(pppg);
  }

  Trace("smt-debug") << "SolverEngine::finishInit" << std::endl;
  d_smtSolver->finishInit();

  // now can construct the SMT-level model object
  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  Assert(te != nullptr);
  TheoryModel* tm = te->getModel();
  if (tm != nullptr)
  {
    // make the check models utility
    d_checkModels.reset(new CheckModels(*d_env.get()));
  }

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_state->setup();

  Trace("smt-debug") << "Set up assertions..." << std::endl;
  d_asserts->finishInit();

  // subsolvers
  if (d_env->getOptions().smt.produceAbducts)
  {
    d_abductSolver.reset(new AbductionSolver(*d_env.get()));
  }
  if (d_env->getOptions().smt.produceInterpols
      != options::ProduceInterpols::NONE)
  {
    d_interpolSolver.reset(new InterpolationSolver(*d_env));
  }

  AlwaysAssert(getPropEngine()->getAssertionLevel() == 0)
      << "The PropEngine has pushed but the SolverEngine "
         "hasn't finished initializing!";

  Assert(getLogicInfo().isLocked());

  // store that we are finished initializing
  d_state->finishInit();
  Trace("smt-debug") << "SolverEngine::finishInit done" << std::endl;
}

void SolverEngine::shutdown()
{
  d_state->shutdown();

  d_smtSolver->shutdown();

  d_env->shutdown();
}

SolverEngine::~SolverEngine()
{
  SolverEngineScope smts(this);

  try
  {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_state->cleanup();

    // destroy all passes before destroying things that they refer to
    d_smtSolver->getPreprocessor()->cleanup();

    d_pfManager.reset(nullptr);
    d_ucManager.reset(nullptr);

    d_absValues.reset(nullptr);
    d_asserts.reset(nullptr);

    d_abductSolver.reset(nullptr);
    d_interpolSolver.reset(nullptr);
    d_quantElimSolver.reset(nullptr);
    d_sygusSolver.reset(nullptr);
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
  SolverEngineScope smts(this);
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
  SolverEngineScope smts(this);
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
  SolverEngineScope smts(this);

  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if (key == "filename")
  {
    d_env->d_options.driver.filename = value;
    d_env->d_originalOptions->driver.filename = value;
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
    getOptions().base.inputLanguage = Language::LANG_SMTLIB_V2_6;
    // also update the output language
    if (!getOptions().base.outputLanguageWasSetByUser)
    {
      setOption("output-language", "smtlib2.6");
      getOptions().base.outputLanguageWasSetByUser = false;
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
  SolverEngineScope smts(this);

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
    switch (status.asSatisfiabilityResult().isSat())
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
      ss << status.whyUnknown();
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
    size_t ulevel = d_state->getNumUserLevels();
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
    if (!formulaType.isComparableTo(rangeType))
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
    if (!formulaType.isComparableTo(funcType))
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
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  // Substitute out any abstract values in formula
  Node def = d_absValues->substituteAbstractValues(formula);
  if (!formals.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    def = nm->mkNode(
        kind::LAMBDA, nm->mkNode(kind::BOUND_VAR_LIST, formals), def);
  }
  // A define-fun is treated as a (higher-order) assertion. It is provided
  // to the assertions object. It will be added as a top-level substitution
  // within this class, possibly multiple times if global is true.
  Node feq = func.eqNode(def);
  d_asserts->addDefineFunDefinition(feq, global);
}

void SolverEngine::defineFunctionsRec(
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas,
    bool global)
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
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

  NodeManager* nm = getNodeManager();
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
    d_asserts->addDefineFunDefinition(lem, global);
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

Result SolverEngine::quickCheck()
{
  Assert(d_state->isFullyInited());
  Trace("smt") << "SMT quickCheck()" << endl;
  const std::string& filename = d_env->getOptions().driver.filename;
  return Result(
      Result::ENTAILMENT_UNKNOWN, Result::REQUIRES_FULL_CHECK, filename);
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
       << " unless immediately preceded by SAT/NOT_ENTAILED or UNKNOWN "
          "response.";
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
  TheoryModel* m = te->getBuiltModel();

  if (m == nullptr)
  {
    std::stringstream ss;
    ss << "Cannot " << c
       << " since model is not available. Perhaps the most recent call to "
          "check-sat was interrupted?";
    throw RecoverableModalException(ss.str().c_str());
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

void SolverEngine::notifyPushPre()
{
  d_smtSolver->processAssertions(*d_asserts);
}

void SolverEngine::notifyPushPost()
{
  TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
  Assert(getPropEngine() != nullptr);
  getPropEngine()->push();
}

void SolverEngine::notifyPopPre()
{
  TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  pe->pop();
}

void SolverEngine::notifyPostSolvePre()
{
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  pe->resetTrail();
}

void SolverEngine::notifyPostSolvePost()
{
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->postsolve();
}

Result SolverEngine::checkSat()
{
  Node nullNode;
  return checkSat(nullNode);
}

Result SolverEngine::checkSat(const Node& assumption)
{
  std::vector<Node> assump;
  if (!assumption.isNull())
  {
    assump.push_back(assumption);
  }
  return checkSatInternal(assump, false);
}

Result SolverEngine::checkSat(const std::vector<Node>& assumptions)
{
  return checkSatInternal(assumptions, false);
}

Result SolverEngine::checkEntailed(const Node& node)
{
  return checkSatInternal(
             node.isNull() ? std::vector<Node>() : std::vector<Node>{node},
             true)
      .asEntailmentResult();
}

Result SolverEngine::checkEntailed(const std::vector<Node>& nodes)
{
  return checkSatInternal(nodes, true).asEntailmentResult();
}

Result SolverEngine::checkSatInternal(const std::vector<Node>& assumptions,
                                      bool isEntailmentCheck)
{
  try
  {
    SolverEngineScope smts(this);
    finishInit();

    Trace("smt") << "SolverEngine::"
                 << (isEntailmentCheck ? "checkEntailed" : "checkSat") << "("
                 << assumptions << ")" << endl;
    // check the satisfiability with the solver object
    Result r = d_smtSolver->checkSatisfiability(
        *d_asserts.get(), assumptions, isEntailmentCheck);

    Trace("smt") << "SolverEngine::"
                 << (isEntailmentCheck ? "query" : "checkSat") << "("
                 << assumptions << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if (d_env->getOptions().smt.checkModels)
    {
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if (d_env->getOptions().smt.checkProofs
        || d_env->getOptions().proof.proofCheck
               == options::ProofCheckMode::EAGER)
    {
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        if ((d_env->getOptions().smt.checkProofs
             || d_env->getOptions().proof.proofCheck
                    == options::ProofCheckMode::EAGER)
            && !d_env->getOptions().smt.produceProofs)
        {
          throw ModalException(
              "Cannot check-proofs because proofs were disabled.");
        }
        checkProof();
      }
    }
    // Check that UNSAT results generate an unsat core correctly.
    if (d_env->getOptions().smt.checkUnsatCores)
    {
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
        checkUnsatCore();
      }
    }
    if (d_env->getOptions().base.statisticsEveryQuery)
    {
      printStatisticsDiff();
    }
    return r;
  }
  catch (UnsafeInterruptException& e)
  {
    AlwaysAssert(getResourceManager()->out());
    // Notice that we do not notify the state of this result. If we wanted to
    // make the solver resume a working state after an interupt, then we would
    // implement a different callback and use it here, e.g.
    // d_state.notifyCheckSatInterupt.
    Result::UnknownExplanation why = getResourceManager()->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;

    if (d_env->getOptions().base.statisticsEveryQuery)
    {
      printStatisticsDiff();
    }
    return Result(
        Result::SAT_UNKNOWN, why, d_env->getOptions().driver.filename);
  }
}

std::vector<Node> SolverEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  SolverEngineScope smts(this);
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
        "UNSAT/ENTAILED.");
  }
  finishInit();
  UnsatCore core = getUnsatCoreInternal();
  std::vector<Node> res;
  std::vector<Node>& assumps = d_asserts->getAssumptions();
  for (const Node& e : assumps)
  {
    if (std::find(core.begin(), core.end(), e) != core.end())
    {
      res.push_back(e);
    }
  }
  return res;
}

Result SolverEngine::assertFormula(const Node& formula)
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();

  Trace("smt") << "SolverEngine::assertFormula(" << formula << ")" << endl;

  // Substitute out any abstract values in ex
  Node n = d_absValues->substituteAbstractValues(formula);

  d_asserts->assertFormula(n);
  return quickCheck().asEntailmentResult();
} /* SolverEngine::assertFormula() */

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SolverEngine::declareSygusVar(Node var)
{
  SolverEngineScope smts(this);
  d_sygusSolver->declareSygusVar(var);
}

void SolverEngine::declareSynthFun(Node func,
                                   TypeNode sygusType,
                                   bool isInv,
                                   const std::vector<Node>& vars)
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  d_sygusSolver->declareSynthFun(func, sygusType, isInv, vars);
}
void SolverEngine::declareSynthFun(Node func,
                                   bool isInv,
                                   const std::vector<Node>& vars)
{
  // use a null sygus type
  TypeNode sygusType;
  declareSynthFun(func, sygusType, isInv, vars);
}

void SolverEngine::assertSygusConstraint(Node n, bool isAssume)
{
  SolverEngineScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusConstraint(n, isAssume);
}

void SolverEngine::assertSygusInvConstraint(Node inv,
                                            Node pre,
                                            Node trans,
                                            Node post)
{
  SolverEngineScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusInvConstraint(inv, pre, trans, post);
}

Result SolverEngine::checkSynth()
{
  SolverEngineScope smts(this);
  finishInit();
  return d_sygusSolver->checkSynth(*d_asserts);
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
  finishInit();
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("declareTermPool");
  qe->declarePool(p, initValue);
}

Node SolverEngine::simplify(const Node& ex)
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  // ensure we've processed assertions
  d_smtSolver->processAssertions(*d_asserts);
  return d_smtSolver->getPreprocessor()->simplify(ex);
}

Node SolverEngine::expandDefinitions(const Node& ex)
{
  getResourceManager()->spendResource(Resource::PreprocessStep);
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  return d_smtSolver->getPreprocessor()->expandDefinitions(ex);
}

// TODO(#1108): Simplify the error reporting of this method.
Node SolverEngine::getValue(const Node& ex) const
{
  SolverEngineScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  TypeNode expectedType = ex.getType();

  // Substitute out any abstract values in ex and expand
  Node n = d_smtSolver->getPreprocessor()->expandDefinitions(ex);

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
  // Notice that lambdas have function type, which does not respect the subtype
  // relation, so we ignore them here.
  Assert(resultNode.isNull() || resultNode.getKind() == kind::LAMBDA
         || resultNode.getType().isSubtypeOf(expectedType))
      << "Run with -t smt for details.";

  // Ensure it's a constant, or a lambda (for uninterpreted functions). This
  // assertion only holds for models that do not have approximate values.
  Assert(m->hasApproximations() || resultNode.getKind() == kind::LAMBDA
         || resultNode.isConst());

  if (d_env->getOptions().smt.abstractValues && resultNode.getType().isArray())
  {
    resultNode = d_absValues->mkAbstractValue(resultNode);
    Trace("smt") << "--- abstract value >> " << resultNode << endl;
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
  Assert(tn.isSort());
  TheoryModel* m = getAvailableModel("getModelDomainElements");
  return m->getDomainElements(tn);
}

bool SolverEngine::isModelCoreSymbol(Node n)
{
  SolverEngineScope smts(this);
  Assert(n.isVar());
  const Options& opts = d_env->getOptions();
  if (opts.smt.modelCoresMode == options::ModelCoresMode::NONE)
  {
    // if the model core mode is none, we are always a model core symbol
    return true;
  }
  TheoryModel* tm = getAvailableModel("isModelCoreSymbol");
  // compute the model core if not done so already
  if (!tm->isUsingModelCore())
  {
    // If we enabled model cores, we compute a model core for m based on our
    // (expanded) assertions using the model core builder utility. Notice that
    // we get the assertions using the getAssertionsInternal, which does not
    // impact whether we are in "sat" mode
    std::vector<Node> asserts = getAssertionsInternal();
    d_smtSolver->getPreprocessor()->expandDefinitions(asserts);
    ModelCoreBuilder mcb(*d_env.get());
    mcb.setModelCore(asserts, tm, opts.smt.modelCoresMode);
  }
  return tm->isModelCoreSymbol(n);
}

std::string SolverEngine::getModel(const std::vector<TypeNode>& declaredSorts,
                                   const std::vector<Node>& declaredFuns)
{
  SolverEngineScope smts(this);
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

Result SolverEngine::blockModel()
{
  Trace("smt") << "SMT blockModel()" << endl;
  SolverEngineScope smts(this);

  finishInit();

  TheoryModel* m = getAvailableModel("block model");

  if (d_env->getOptions().smt.blockModelsMode == options::BlockModelsMode::NONE)
  {
    std::stringstream ss;
    ss << "Cannot block model when block-models is set to none.";
    throw RecoverableModalException(ss.str().c_str());
  }

  // get expanded assertions
  std::vector<Node> eassertsProc = getExpandedAssertions();
  ModelBlocker mb(*d_env.get());
  Node eblocker = mb.getModelBlocker(
      eassertsProc, m, d_env->getOptions().smt.blockModelsMode);
  Trace("smt") << "Block formula: " << eblocker << std::endl;
  return assertFormula(eblocker);
}

Result SolverEngine::blockModelValues(const std::vector<Node>& exprs)
{
  Trace("smt") << "SMT blockModelValues()" << endl;
  SolverEngineScope smts(this);

  finishInit();

  TheoryModel* m = getAvailableModel("block model values");

  // get expanded assertions
  std::vector<Node> eassertsProc = getExpandedAssertions();
  // we always do block model values mode here
  ModelBlocker mb(*d_env.get());
  Node eblocker = mb.getModelBlocker(
      eassertsProc, m, options::BlockModelsMode::VALUES, exprs);
  return assertFormula(eblocker);
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

std::vector<Node> SolverEngine::getAssertionsInternal()
{
  Assert(d_state->isFullyInited());
  const context::CDList<Node>& al = d_asserts->getAssertionList();
  std::vector<Node> res;
  for (const Node& n : al)
  {
    res.emplace_back(n);
  }
  return res;
}

std::vector<Node> SolverEngine::getExpandedAssertions()
{
  std::vector<Node> easserts = getAssertions();
  // must expand definitions
  d_smtSolver->getPreprocessor()->expandDefinitions(easserts);
  return easserts;
}
Env& SolverEngine::getEnv() { return *d_env.get(); }

void SolverEngine::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  if (!getLogicInfo().isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot declare heap if not using the separation logic theory.";
    throw RecoverableModalException(msg);
  }
  SolverEngineScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  te->declareSepHeap(locT, dataT);
}

bool SolverEngine::getSepHeapTypes(TypeNode& locT, TypeNode& dataT)
{
  SolverEngineScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  return te->getSepHeapTypes(locT, dataT);
}

Node SolverEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Node SolverEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

void SolverEngine::checkProof()
{
  Assert(d_env->getOptions().smt.produceProofs);
  // internal check the proof
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  if (d_env->getOptions().proof.proofCheck == options::ProofCheckMode::EAGER)
  {
    pe->checkProof(d_asserts->getAssertionList());
  }
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pePfn = pe->getProof();
  if (d_env->getOptions().smt.checkProofs)
  {
    d_pfManager->checkProof(pePfn, *d_asserts);
  }
}

StatisticsRegistry& SolverEngine::getStatisticsRegistry()
{
  return d_env->getStatisticsRegistry();
}

UnsatCore SolverEngine::getUnsatCoreInternal()
{
  if (!d_env->getOptions().smt.unsatCores)
  {
    throw ModalException(
        "Cannot get an unsat core when produce-unsat-cores or produce-proofs "
        "option is off.");
  }
  if (d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by "
        "UNSAT/ENTAILED response.");
  }
  // generate with new proofs
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);

  std::shared_ptr<ProofNode> pepf;
  if (options::unsatCoresMode() == options::UnsatCoresMode::ASSUMPTIONS)
  {
    pepf = pe->getRefutation();
  }
  else
  {
    pepf = pe->getProof();
  }
  Assert(pepf != nullptr);
  std::shared_ptr<ProofNode> pfn = d_pfManager->getFinalProof(pepf, *d_asserts);
  std::vector<Node> core;
  d_ucManager->getUnsatCore(pfn, *d_asserts, core);
  if (options::minimalUnsatCores())
  {
    core = reduceUnsatCore(core);
  }
  return UnsatCore(core);
}

std::vector<Node> SolverEngine::reduceUnsatCore(const std::vector<Node>& core)
{
  Assert(options::unsatCores())
      << "cannot reduce unsat core if unsat cores are turned off";

  d_env->verbose(1) << "SolverEngine::reduceUnsatCore(): reducing unsat core"
                    << std::endl;
  std::unordered_set<Node> removed;
  for (const Node& skip : core)
  {
    std::unique_ptr<SolverEngine> coreChecker;
    initializeSubsolver(coreChecker, *d_env.get());
    coreChecker->setLogic(getLogicInfo());
    coreChecker->getOptions().smt.checkUnsatCores = false;
    // disable all proof options
    coreChecker->getOptions().smt.produceProofs = false;
    coreChecker->getOptions().smt.checkProofs = false;

    for (const Node& ucAssertion : core)
    {
      if (ucAssertion != skip && removed.find(ucAssertion) == removed.end())
      {
        Node assertionAfterExpansion = expandDefinitions(ucAssertion);
        coreChecker->assertFormula(assertionAfterExpansion);
      }
    }
    Result r;
    try
    {
      r = coreChecker->checkSat();
    }
    catch (...)
    {
      throw;
    }

    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      removed.insert(skip);
    }
    else if (r.asSatisfiabilityResult().isUnknown())
    {
      d_env->warning()
          << "SolverEngine::reduceUnsatCore(): could not reduce unsat core "
             "due to "
             "unknown result.";
    }
  }

  if (removed.empty())
  {
    return core;
  }
  else
  {
    std::vector<Node> newUcAssertions;
    for (const Node& n : core)
    {
      if (removed.find(n) == removed.end())
      {
        newUcAssertions.push_back(n);
      }
    }

    return newUcAssertions;
  }
}

void SolverEngine::checkUnsatCore()
{
  Assert(d_env->getOptions().smt.unsatCores)
      << "cannot check unsat core if unsat cores are turned off";

  d_env->verbose(1) << "SolverEngine::checkUnsatCore(): generating unsat core"
                    << std::endl;
  UnsatCore core = getUnsatCore();

  // initialize the core checker
  std::unique_ptr<SolverEngine> coreChecker;
  initializeSubsolver(coreChecker, *d_env.get());
  coreChecker->getOptions().smt.checkUnsatCores = false;
  // disable all proof options
  coreChecker->getOptions().smt.produceProofs = false;
  coreChecker->getOptions().smt.checkProofs = false;

  // set up separation logic heap if necessary
  TypeNode sepLocType, sepDataType;
  if (getSepHeapTypes(sepLocType, sepDataType))
  {
    coreChecker->declareSepHeap(sepLocType, sepDataType);
  }

  d_env->verbose(1) << "SolverEngine::checkUnsatCore(): pushing core assertions"
                    << std::endl;
  theory::TrustSubstitutionMap& tls = d_env->getTopLevelSubstitutions();
  for (UnsatCore::iterator i = core.begin(); i != core.end(); ++i)
  {
    Node assertionAfterExpansion = tls.apply(*i, false);
    d_env->verbose(1) << "SolverEngine::checkUnsatCore(): pushing core member "
                      << *i << ", expanded to " << assertionAfterExpansion
                      << std::endl;
    coreChecker->assertFormula(assertionAfterExpansion);
  }
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
  if (r.asSatisfiabilityResult().isUnknown())
  {
    d_env->warning() << "SolverEngine::checkUnsatCore(): could not check core result "
                 "unknown."
              << std::endl;
  }
  else if (r.asSatisfiabilityResult().isSat())
  {
    InternalError()
        << "SolverEngine::checkUnsatCore(): produced core was satisfiable.";
  }
}

void SolverEngine::checkModel(bool hardFailure)
{
  const context::CDList<Node>& al = d_asserts->getAssertionList();
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(d_env->getOptions().smt.produceAssertions)
      << "don't have an assertion list to check in SolverEngine::checkModel()";

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  d_env->verbose(1) << "SolverEngine::checkModel(): generating model"
                    << std::endl;
  TheoryModel* m = getAvailableModel("check model");
  Assert(m != nullptr);

  // check the model with the theory engine for debugging
  if (options::debugCheckModels())
  {
    TheoryEngine* te = getTheoryEngine();
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
  SolverEngineScope smts(this);
  finishInit();
  return getUnsatCoreInternal();
}

void SolverEngine::getRelevantInstantiationTermVectors(
    std::map<Node, InstantiationList>& insts, bool getDebugInfo)
{
  Assert(d_state->getMode() == SmtMode::UNSAT);
  // generate with new proofs
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pfn =
      d_pfManager->getFinalProof(pe->getProof(), *d_asserts);
  d_ucManager->getRelevantInstantiations(pfn, insts, getDebugInfo);
}

std::string SolverEngine::getProof()
{
  Trace("smt") << "SMT getProof()\n";
  SolverEngineScope smts(this);
  finishInit();
  if (!d_env->getOptions().smt.produceProofs)
  {
    throw ModalException("Cannot get a proof when proof option is off.");
  }
  if (d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get a proof unless immediately preceded by "
        "UNSAT/ENTAILED response.");
  }
  // the prop engine has the proof of false
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  Assert(pe->getProof() != nullptr);
  Assert(d_pfManager);
  std::ostringstream ss;
  d_pfManager->printProof(ss, pe->getProof(), *d_asserts);
  return ss.str();
}

void SolverEngine::printInstantiations(std::ostream& out)
{
  SolverEngineScope smts(this);
  finishInit();
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("printInstantiations");

  // First, extract and print the skolemizations
  bool printed = false;
  bool reqNames = !d_env->getOptions().printer.printInstFull;
  // only print when in list mode
  if (d_env->getOptions().printer.printInstMode == options::PrintInstMode::LIST)
  {
    std::map<Node, std::vector<Node>> sks;
    qe->getSkolemTermVectors(sks);
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

  // Second, extract and print the instantiations
  std::map<Node, InstantiationList> rinsts;
  if (d_env->getOptions().smt.produceProofs
      && (!d_env->getOptions().smt.unsatCores
          || d_env->getOptions().smt.unsatCoresMode
                 == options::UnsatCoresMode::FULL_PROOF)
      && getSmtMode() == SmtMode::UNSAT)
  {
    // minimize instantiations based on proof manager
    getRelevantInstantiationTermVectors(rinsts,
                                        options::dumpInstantiationsDebug());
  }
  else
  {
    std::map<Node, std::vector<std::vector<Node>>> insts;
    getInstantiationTermVectors(insts);
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
    if (d_env->getOptions().printer.printInstMode
        == options::PrintInstMode::NUM)
    {
      out << "(num-instantiations " << name << " " << i.second.d_inst.size()
          << ")" << std::endl;
    }
    else
    {
      // take the name
      i.second.d_quant = name;
      Assert(d_env->getOptions().printer.printInstMode
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
  SolverEngineScope smts(this);
  finishInit();
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiationTermVectors");
  // get the list of all instantiations
  qe->getInstantiationTermVectors(insts);
}

bool SolverEngine::getSynthSolutions(std::map<Node, Node>& solMap)
{
  SolverEngineScope smts(this);
  finishInit();
  return d_sygusSolver->getSynthSolutions(solMap);
}

Node SolverEngine::getQuantifierElimination(Node q, bool doFull, bool strict)
{
  SolverEngineScope smts(this);
  finishInit();
  const LogicInfo& logic = getLogicInfo();
  if (!logic.isPure(THEORY_ARITH) && strict)
  {
    d_env->warning() << "Unexpected logic for quantifier elimination " << logic
              << endl;
  }
  return d_quantElimSolver->getQuantifierElimination(
      *d_asserts, q, doFull, d_isInternalSubsolver);
}

bool SolverEngine::getInterpol(const Node& conj,
                               const TypeNode& grammarType,
                               Node& interpol)
{
  SolverEngineScope smts(this);
  finishInit();
  std::vector<Node> axioms = getExpandedAssertions();
  bool success =
      d_interpolSolver->getInterpol(axioms, conj, grammarType, interpol);
  // notify the state of whether the get-interpol call was successfuly, which
  // impacts the SMT mode.
  d_state->notifyGetInterpol(success);
  return success;
}

bool SolverEngine::getInterpol(const Node& conj, Node& interpol)
{
  TypeNode grammarType;
  return getInterpol(conj, grammarType, interpol);
}

bool SolverEngine::getAbduct(const Node& conj,
                             const TypeNode& grammarType,
                             Node& abd)
{
  SolverEngineScope smts(this);
  finishInit();
  std::vector<Node> axioms = getExpandedAssertions();
  bool success = d_abductSolver->getAbduct(axioms, conj, grammarType, abd);
  // notify the state of whether the get-abduct call was successfuly, which
  // impacts the SMT mode.
  d_state->notifyGetAbduct(success);
  return success;
}

bool SolverEngine::getAbduct(const Node& conj, Node& abd)
{
  TypeNode grammarType;
  return getAbduct(conj, grammarType, abd);
}

void SolverEngine::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  SolverEngineScope smts(this);
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiatedQuantifiedFormulas");
  qe->getInstantiatedQuantifiedFormulas(qs);
}

void SolverEngine::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node>>& tvecs)
{
  SolverEngineScope smts(this);
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiationTermVectors");
  qe->getInstantiationTermVectors(q, tvecs);
}

std::vector<Node> SolverEngine::getAssertions()
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  Trace("smt") << "SMT getAssertions()" << endl;
  if (!d_env->getOptions().smt.produceAssertions)
  {
    const char* msg =
        "Cannot query the current assertion list when not in "
        "produce-assertions mode.";
    throw ModalException(msg);
  }
  return getAssertionsInternal();
}

void SolverEngine::getDifficultyMap(std::map<Node, Node>& dmap)
{
  Trace("smt") << "SMT getDifficultyMap()\n";
  SolverEngineScope smts(this);
  finishInit();
  if (!d_env->getOptions().smt.produceDifficulty)
  {
    throw ModalException(
        "Cannot get difficulty when difficulty option is off.");
  }
  // the prop engine has the proof of false
  Assert(d_pfManager);
  // get difficulty map from theory engine first
  TheoryEngine* te = getTheoryEngine();
  te->getDifficultyMap(dmap);
  // then ask proof manager to translate dmap in terms of the input
  d_pfManager->translateDifficultyMap(dmap, *d_asserts);
}

void SolverEngine::push()
{
  SolverEngineScope smts(this);
  finishInit();
  d_state->doPendingPops();
  Trace("smt") << "SMT push()" << endl;
  d_smtSolver->processAssertions(*d_asserts);
  d_state->userPush();
}

void SolverEngine::pop()
{
  SolverEngineScope smts(this);
  finishInit();
  Trace("smt") << "SMT pop()" << endl;
  d_state->userPop();

  // Clear out assertion queues etc., in case anything is still in there
  d_asserts->clearCurrent();
  // clear the learned literals from the preprocessor
  d_smtSolver->getPreprocessor()->clearLearnedLiterals();

  Trace("userpushpop") << "SolverEngine: popped to level "
                       << getUserContext()->getLevel() << endl;
  // should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SolverEngine::resetAssertions()
{
  SolverEngineScope smts(this);

  if (!d_state->isFullyInited())
  {
    // We're still in Start Mode, nothing asserted yet, do nothing.
    // (see solver execution modes in the SMT-LIB standard)
    Assert(getContext()->getLevel() == 0);
    Assert(getUserContext()->getLevel() == 0);
    return;
  }

  Trace("smt") << "SMT resetAssertions()" << endl;

  d_asserts->clearCurrent();
  d_state->notifyResetAssertions();
  // push the state to maintain global context around everything
  d_state->setup();

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
    d_env->d_options.base.cumulativeResourceLimit = units;
  }
  else
  {
    d_env->d_options.base.perCallResourceLimit = units;
  }
}
void SolverEngine::setTimeLimit(uint64_t millis)
{
  d_env->d_options.base.perCallMillisecondLimit = millis;
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

NodeManager* SolverEngine::getNodeManager() const
{
  return d_env->getNodeManager();
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

  if (key == "command-verbosity")
  {
    size_t fstIndex = value.find(" ");
    size_t sndIndex = value.find(" ", fstIndex + 1);
    if (sndIndex == std::string::npos)
    {
      string c = value.substr(1, fstIndex - 1);
      int v =
          std::stoi(value.substr(fstIndex + 1, value.length() - fstIndex - 1));
      if (v < 0 || v > 2)
      {
        throw OptionException("command-verbosity must be 0, 1, or 2");
      }
      d_commandVerbosity[c] = v;
      return;
    }
    throw OptionException(
        "command-verbosity value must be a tuple (command-name integer)");
  }

  if (value.find(" ") != std::string::npos)
  {
    throw OptionException("bad value for :" + key);
  }

  std::string optionarg = value;
  options::set(getOptions(), key, optionarg);
}

void SolverEngine::setIsInternalSubsolver() { d_isInternalSubsolver = true; }

bool SolverEngine::isInternalSubsolver() const { return d_isInternalSubsolver; }

std::string SolverEngine::getOption(const std::string& key) const
{
  NodeManager* nm = d_env->getNodeManager();

  Trace("smt") << "SMT getOption(" << key << ")" << endl;

  if (key.find("command-verbosity:") == 0)
  {
    auto it =
        d_commandVerbosity.find(key.substr(std::strlen("command-verbosity:")));
    if (it != d_commandVerbosity.end())
    {
      return std::to_string(it->second);
    }
    it = d_commandVerbosity.find("*");
    if (it != d_commandVerbosity.end())
    {
      return std::to_string(it->second);
    }
    return "2";
  }

  if (key == "command-verbosity")
  {
    vector<Node> result;
    Node defaultVerbosity;
    for (const auto& verb : d_commandVerbosity)
    {
      // treat the command name as a variable name as opposed to a string
      // constant to avoid printing double quotes around the name
      Node name = nm->mkBoundVar(verb.first, nm->integerType());
      Node value = nm->mkConst(Rational(verb.second));
      if (verb.first == "*")
      {
        // put the default at the end of the SExpr
        defaultVerbosity = nm->mkNode(Kind::SEXPR, name, value);
      }
      else
      {
        result.push_back(nm->mkNode(Kind::SEXPR, name, value));
      }
    }
    // ensure the default is always listed
    if (defaultVerbosity.isNull())
    {
      defaultVerbosity = nm->mkNode(Kind::SEXPR,
                                    nm->mkBoundVar("*", nm->integerType()),
                                    nm->mkConst(Rational(2)));
    }
    result.push_back(defaultVerbosity);
    return nm->mkNode(Kind::SEXPR, result).toString();
  }

  return options::get(getOptions(), key);
}

Options& SolverEngine::getOptions() { return d_env->d_options; }

const Options& SolverEngine::getOptions() const { return d_env->getOptions(); }

ResourceManager* SolverEngine::getResourceManager() const
{
  return d_env->getResourceManager();
}

const Printer& SolverEngine::getPrinter() const { return d_env->getPrinter(); }

theory::Rewriter* SolverEngine::getRewriter() { return d_env->getRewriter(); }

}  // namespace cvc5
