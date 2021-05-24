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

#include "smt/smt_engine.h"

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
#include "options/printer_options.h"
#include "options/proof_options.h"
#include "options/resource_manager_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "prop/prop_engine.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/check_models.h"
#include "smt/dump.h"
#include "smt/dump_manager.h"
#include "smt/env.h"
#include "smt/interpolation_solver.h"
#include "smt/listeners.h"
#include "smt/logic_exception.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/node_command.h"
#include "smt/options_manager.h"
#include "smt/preprocessor.h"
#include "smt/proof_manager.h"
#include "smt/quant_elim_solver.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_engine_state.h"
#include "smt/smt_engine_stats.h"
#include "smt/smt_solver.h"
#include "smt/sygus_solver.h"
#include "smt/unsat_core_manager.h"
#include "theory/quantifiers/instantiation_list.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "util/random.h"
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

SmtEngine::SmtEngine(NodeManager* nm, Options* optr)
    : d_env(new Env(nm, optr)),
      d_state(new SmtEngineState(getContext(), getUserContext(), *this)),
      d_absValues(new AbstractValues(getNodeManager())),
      d_asserts(new Assertions(*d_env.get(), *d_absValues.get())),
      d_routListener(new ResourceOutListener(*this)),
      d_snmListener(new SmtNodeManagerListener(*getDumpManager(), d_outMgr)),
      d_smtSolver(nullptr),
      d_model(nullptr),
      d_checkModels(nullptr),
      d_pfManager(nullptr),
      d_ucManager(nullptr),
      d_sygusSolver(nullptr),
      d_abductSolver(nullptr),
      d_interpolSolver(nullptr),
      d_quantElimSolver(nullptr),
      d_isInternalSubsolver(false),
      d_stats(nullptr),
      d_outMgr(this),
      d_optm(nullptr),
      d_pp(nullptr),
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
  // set the options manager
  d_optm.reset(new smt::OptionsManager(&getOptions()));
  // listen to node manager events
  getNodeManager()->subscribeEvents(d_snmListener.get());
  // listen to resource out
  getResourceManager()->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SmtEngineStatistics());
  // reset the preprocessor
  d_pp.reset(
      new smt::Preprocessor(*this, *d_env.get(), *d_absValues.get(), *d_stats));
  // make the SMT solver
  d_smtSolver.reset(
      new SmtSolver(*this, *d_env.get(), *d_state, *d_pp, *d_stats));
  // make the SyGuS solver
  d_sygusSolver.reset(
      new SygusSolver(*d_smtSolver, *d_pp, getUserContext(), d_outMgr));
  // make the quantifier elimination solver
  d_quantElimSolver.reset(new QuantElimSolver(*d_smtSolver));

}

bool SmtEngine::isFullyInited() const { return d_state->isFullyInited(); }
bool SmtEngine::isQueryMade() const { return d_state->isQueryMade(); }
size_t SmtEngine::getNumUserLevels() const
{
  return d_state->getNumUserLevels();
}
SmtMode SmtEngine::getSmtMode() const { return d_state->getMode(); }
bool SmtEngine::isSmtModeSat() const
{
  SmtMode mode = getSmtMode();
  return mode == SmtMode::SAT || mode == SmtMode::SAT_UNKNOWN;
}
Result SmtEngine::getStatusOfLastCommand() const
{
  return d_state->getStatus();
}
context::UserContext* SmtEngine::getUserContext()
{
  return d_env->getUserContext();
}
context::Context* SmtEngine::getContext() { return d_env->getContext(); }

TheoryEngine* SmtEngine::getTheoryEngine()
{
  return d_smtSolver->getTheoryEngine();
}

prop::PropEngine* SmtEngine::getPropEngine()
{
  return d_smtSolver->getPropEngine();
}

void SmtEngine::finishInit()
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
  Random::getRandom().setSeed(d_env->getOption(options::seed));

  // Call finish init on the options manager. This inializes the resource
  // manager based on the options, and sets up the best default options
  // based on our heuristics.
  d_optm->finishInit(d_env->d_logic, d_isInternalSubsolver);

  ProofNodeManager* pnm = nullptr;
  if (d_env->getOption(options::produceProofs))
  {
    // ensure bound variable uses canonical bound variables
    getNodeManager()->getBoundVarManager()->enableKeepCacheValues();
    // make the proof manager
    d_pfManager.reset(new PfManager(getUserContext(), this));
    PreprocessProofGenerator* pppg = d_pfManager->getPreprocessProofGenerator();
    // start the unsat core manager
    d_ucManager.reset(new UnsatCoreManager());
    // use this proof node manager
    pnm = d_pfManager->getProofNodeManager();
    // enable proof support in the environment/rewriter
    d_env->setProofNodeManager(pnm);
    // enable it in the assertions pipeline
    d_asserts->setProofGenerator(pppg);
    // enable it in the SmtSolver
    d_smtSolver->setProofNodeManager(pnm);
    // enabled proofs in the preprocessor
    d_pp->setProofGenerator(pppg);
  }

  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  d_smtSolver->finishInit(logic);

  // now can construct the SMT-level model object
  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  Assert(te != nullptr);
  TheoryModel* tm = te->getModel();
  if (tm != nullptr)
  {
    d_model.reset(new Model(tm));
    // make the check models utility
    d_checkModels.reset(new CheckModels(*d_env.get()));
  }

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_state->setup();

  Trace("smt-debug") << "Set up assertions..." << std::endl;
  d_asserts->finishInit();

  // dump out a set-logic command only when raw-benchmark is disabled to avoid
  // dumping the command twice.
  if (Dump.isOn("benchmark") && !Dump.isOn("raw-benchmark"))
  {
      LogicInfo everything;
      everything.lock();
      getPrinter().toStreamCmdComment(
          getOutputManager().getDumpOut(),
          "cvc5 always dumps the most general, all-supported logic (below), as "
          "some internals might require the use of a logic more general than "
          "the input.");
      getPrinter().toStreamCmdSetBenchmarkLogic(getOutputManager().getDumpOut(),
                                                everything.getLogicString());
  }

  // initialize the dump manager
  getDumpManager()->finishInit();

  // subsolvers
  if (d_env->getOption(options::produceAbducts))
  {
    d_abductSolver.reset(new AbductionSolver(this));
  }
  if (d_env->getOption(options::produceInterpols)
      != options::ProduceInterpols::NONE)
  {
    d_interpolSolver.reset(new InterpolationSolver(this));
  }

  d_pp->finishInit();

  AlwaysAssert(getPropEngine()->getAssertionLevel() == 0)
      << "The PropEngine has pushed but the SmtEngine "
         "hasn't finished initializing!";

  Assert(getLogicInfo().isLocked());

  // store that we are finished initializing
  d_state->finishInit();
  Trace("smt-debug") << "SmtEngine::finishInit done" << std::endl;
}

void SmtEngine::shutdown() {
  d_state->shutdown();

  d_smtSolver->shutdown();

  d_env->shutdown();
}

SmtEngine::~SmtEngine()
{
  SmtScope smts(this);

  try {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_state->cleanup();

    //destroy all passes before destroying things that they refer to
    d_pp->cleanup();

    d_pfManager.reset(nullptr);
    d_ucManager.reset(nullptr);

    d_absValues.reset(nullptr);
    d_asserts.reset(nullptr);
    d_model.reset(nullptr);

    d_abductSolver.reset(nullptr);
    d_interpolSolver.reset(nullptr);
    d_quantElimSolver.reset(nullptr);
    d_sygusSolver.reset(nullptr);
    d_smtSolver.reset(nullptr);

    d_stats.reset(nullptr);
    getNodeManager()->unsubscribeEvents(d_snmListener.get());
    d_snmListener.reset(nullptr);
    d_routListener.reset(nullptr);
    d_optm.reset(nullptr);
    d_pp.reset(nullptr);
    // destroy the state
    d_state.reset(nullptr);
    // destroy the environment
    d_env.reset(nullptr);
  } catch(Exception& e) {
    Warning() << "cvc5 threw an exception during cleanup." << endl << e << endl;
  }
}

void SmtEngine::setLogic(const LogicInfo& logic)
{
  SmtScope smts(this);
  if (d_state->isFullyInited())
  {
    throw ModalException("Cannot set logic in SmtEngine after the engine has "
                         "finished initializing.");
  }
  d_env->d_logic = logic;
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
      getPrinter().toStreamCmdSetBenchmarkLogic(
          getOutputManager().getDumpOut(), getLogicInfo().getLogicString());
    }
  }
  catch (IllegalArgumentException& e)
  {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) { setLogic(string(logic)); }

const LogicInfo& SmtEngine::getLogicInfo() const
{
  return d_env->getLogicInfo();
}

LogicInfo SmtEngine::getUserLogicInfo() const
{
  // Lock the logic to make sure that this logic can be queried. We create a
  // copy of the user logic here to keep this method const.
  LogicInfo res = d_userLogic;
  res.lock();
  return res;
}

void SmtEngine::notifyStartParsing(const std::string& filename)
{
  d_state->setFilename(filename);
  d_env->getStatisticsRegistry().registerValue<std::string>("driver::filename",
                                                            filename);
  // Copy the original options. This is called prior to beginning parsing.
  // Hence reset should revert to these options, which note is after reading
  // the command line.
}

const std::string& SmtEngine::getFilename() const
{
  return d_state->getFilename();
}

void SmtEngine::setResultStatistic(const std::string& result) {
  d_env->getStatisticsRegistry().registerValue<std::string>("driver::sat/unsat",
                                                            result);
}
void SmtEngine::setTotalTimeStatistic(double seconds) {
  d_env->getStatisticsRegistry().registerValue<double>("driver::totalTime",
                                                       seconds);
}

void SmtEngine::setLogicInternal()
{
  Assert(!d_state->isFullyInited())
      << "setting logic in SmtEngine but the engine has already"
         " finished initializing for this run";
  d_env->d_logic.lock();
  d_userLogic.lock();
}

void SmtEngine::setInfo(const std::string& key, const std::string& value)
{
  SmtScope smts(this);

  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if (Dump.isOn("benchmark"))
  {
    if (key == "status")
    {
      Result::Sat status =
          (value == "sat")
              ? Result::SAT
              : ((value == "unsat") ? Result::UNSAT : Result::SAT_UNKNOWN);
      getPrinter().toStreamCmdSetBenchmarkStatus(
          getOutputManager().getDumpOut(), status);
    }
    else
    {
      getPrinter().toStreamCmdSetInfo(
          getOutputManager().getDumpOut(), key, value);
    }
  }

  if (key == "filename")
  {
    d_state->setFilename(value);
  }
  else if (key == "smt-lib-version" && !Options::current().wasSetByUser(options::inputLanguage))
  {
    language::input::Language ilang = language::input::LANG_SMTLIB_V2_6;

    if (value != "2" && value != "2.6")
    {
      Warning() << "SMT-LIB version " << value
                << " unsupported, defaulting to language (and semantics of) "
                   "SMT-LIB 2.6\n";
    }
    Options::current().set(options::inputLanguage, ilang);
    // also update the output language
    if (!Options::current().wasSetByUser(options::outputLanguage))
    {
      language::output::Language olang = language::toOutputLanguage(ilang);
      if (d_env->getOption(options::outputLanguage) != olang)
      {
        Options::current().set(options::outputLanguage, olang);
        *d_env->getOption(options::out) << language::SetLanguage(olang);
      }
    }
  }
  else if (key == "status")
  {
    d_state->notifyExpectedStatus(value);
  }
}

bool SmtEngine::isValidGetInfoFlag(const std::string& key) const
{
  if (key == "all-statistics" || key == "error-behavior" || key == "name"
      || key == "version" || key == "authors" || key == "status"
      || key == "reason-unknown" || key == "assertion-stack-levels"
      || key == "all-options" || key == "time")
  {
    return true;
  }
  return false;
}

std::string SmtEngine::getInfo(const std::string& key) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if (key == "all-statistics")
  {
    return toSExpr(d_env->getStatisticsRegistry().begin(), d_env->getStatisticsRegistry().end());
  }
  if (key == "error-behavior")
  {
    return "immediate-exit";
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
    return toSExpr(Configuration::about());
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
  return toSExpr(Options::current().getOptions());
}

void SmtEngine::debugCheckFormals(const std::vector<Node>& formals, Node func)
{
  for (std::vector<Node>::const_iterator i = formals.begin();
       i != formals.end();
       ++i)
  {
    if((*i).getKind() != kind::BOUND_VARIABLE) {
      stringstream ss;
      ss << "All formal arguments to defined functions must be BOUND_VARIABLEs, but in the\n"
         << "definition of function " << func << ", formal\n"
         << "  " << *i << "\n"
         << "has kind " << (*i).getKind();
      throw TypeCheckingExceptionPrivate(func, ss.str());
    }
  }
}

void SmtEngine::debugCheckFunctionBody(Node formula,
                                       const std::vector<Node>& formals,
                                       Node func)
{
  TypeNode formulaType =
      formula.getType(d_env->getOption(options::typeChecking));
  TypeNode funcType = func.getType();
  // We distinguish here between definitions of constants and functions,
  // because the type checking for them is subtly different.  Perhaps we
  // should instead have SmtEngine::defineFunction() and
  // SmtEngine::defineConstant() for better clarity, although then that
  // doesn't match the SMT-LIBv2 standard...
  if(formals.size() > 0) {
    TypeNode rangeType = funcType.getRangeType();
    if(! formulaType.isComparableTo(rangeType)) {
      stringstream ss;
      ss << "Type of defined function does not match its declaration\n"
         << "The function  : " << func << "\n"
         << "Declared type : " << rangeType << "\n"
         << "The body      : " << formula << "\n"
         << "Body type     : " << formulaType;
      throw TypeCheckingExceptionPrivate(func, ss.str());
    }
  } else {
    if(! formulaType.isComparableTo(funcType)) {
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

void SmtEngine::defineFunction(Node func,
                               const std::vector<Node>& formals,
                               Node formula,
                               bool global)
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  stringstream ss;
  ss << language::SetLanguage(
            language::SetLanguage::getLanguage(Dump.getStream()))
     << func;

  DefineFunctionNodeCommand nc(ss.str(), func, formals, formula);
  getDumpManager()->addToDump(nc, "declarations");

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

void SmtEngine::defineFunctionsRec(
    const std::vector<Node>& funcs,
    const std::vector<std::vector<Node>>& formals,
    const std::vector<Node>& formulas,
    bool global)
{
  SmtScope smts(this);
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

  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdDefineFunctionRec(
        getOutputManager().getDumpOut(), funcs, formals, formulas);
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
    // assert the quantified formula
    //   notice we don't call assertFormula directly, since this would
    //   duplicate the output on raw-benchmark.
    // add define recursive definition to the assertions
    d_asserts->addDefineFunDefinition(lem, global);
  }
}

void SmtEngine::defineFunctionRec(Node func,
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

Result SmtEngine::quickCheck() {
  Assert(d_state->isFullyInited());
  Trace("smt") << "SMT quickCheck()" << endl;
  const std::string& filename = d_state->getFilename();
  return Result(
      Result::ENTAILMENT_UNKNOWN, Result::REQUIRES_FULL_CHECK, filename);
}

Model* SmtEngine::getAvailableModel(const char* c) const
{
  if (!d_env->getOption(options::assignFunctionValues))
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

  if (!d_env->getOption(options::produceModels))
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

  return d_model.get();
}

QuantifiersEngine* SmtEngine::getAvailableQuantifiersEngine(const char* c) const
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

void SmtEngine::notifyPushPre() { d_smtSolver->processAssertions(*d_asserts); }

void SmtEngine::notifyPushPost()
{
  TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
  Assert(getPropEngine() != nullptr);
  getPropEngine()->push();
}

void SmtEngine::notifyPopPre()
{
  TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  pe->pop();
}

void SmtEngine::notifyPostSolvePre()
{
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  pe->resetTrail();
}

void SmtEngine::notifyPostSolvePost()
{
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->postsolve();
}

Result SmtEngine::checkSat()
{
  Node nullNode;
  return checkSat(nullNode);
}

Result SmtEngine::checkSat(const Node& assumption, bool inUnsatCore)
{
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdCheckSat(getOutputManager().getDumpOut(),
                                     assumption);
  }
  std::vector<Node> assump;
  if (!assumption.isNull())
  {
    assump.push_back(assumption);
  }
  return checkSatInternal(assump, inUnsatCore, false);
}

Result SmtEngine::checkSat(const std::vector<Node>& assumptions,
                           bool inUnsatCore)
{
  if (Dump.isOn("benchmark"))
  {
    if (assumptions.empty())
    {
      getPrinter().toStreamCmdCheckSat(getOutputManager().getDumpOut());
    }
    else
    {
      getPrinter().toStreamCmdCheckSatAssuming(getOutputManager().getDumpOut(),
                                               assumptions);
    }
  }
  return checkSatInternal(assumptions, inUnsatCore, false);
}

Result SmtEngine::checkEntailed(const Node& node, bool inUnsatCore)
{
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdQuery(getOutputManager().getDumpOut(), node);
  }
  return checkSatInternal(
             node.isNull() ? std::vector<Node>() : std::vector<Node>{node},
             inUnsatCore,
             true)
      .asEntailmentResult();
}

Result SmtEngine::checkEntailed(const std::vector<Node>& nodes,
                                bool inUnsatCore)
{
  return checkSatInternal(nodes, inUnsatCore, true).asEntailmentResult();
}

Result SmtEngine::checkSatInternal(const std::vector<Node>& assumptions,
                                   bool inUnsatCore,
                                   bool isEntailmentCheck)
{
  try
  {
    SmtScope smts(this);
    finishInit();

    Trace("smt") << "SmtEngine::"
                 << (isEntailmentCheck ? "checkEntailed" : "checkSat") << "("
                 << assumptions << ")" << endl;
    // check the satisfiability with the solver object
    Result r = d_smtSolver->checkSatisfiability(
        *d_asserts.get(), assumptions, inUnsatCore, isEntailmentCheck);

    Trace("smt") << "SmtEngine::" << (isEntailmentCheck ? "query" : "checkSat")
                 << "(" << assumptions << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if (d_env->getOption(options::checkModels))
    {
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if (d_env->getOption(options::checkProofs)
        || d_env->getOption(options::proofEagerChecking))
    {
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        if ((d_env->getOption(options::checkProofs)
             || d_env->getOption(options::proofEagerChecking))
            && !d_env->getOption(options::produceProofs))
        {
          throw ModalException(
              "Cannot check-proofs because proofs were disabled.");
        }
        checkProof();
      }
    }
    // Check that UNSAT results generate an unsat core correctly.
    if (d_env->getOption(options::checkUnsatCores))
    {
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        TimerStat::CodeTimer checkUnsatCoreTimer(d_stats->d_checkUnsatCoreTime);
        checkUnsatCore();
      }
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
    return Result(Result::SAT_UNKNOWN, why, d_state->getFilename());
  }
}

std::vector<Node> SmtEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  SmtScope smts(this);
  if (!d_env->getOption(options::unsatAssumptions))
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
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetUnsatAssumptions(
        getOutputManager().getDumpOut());
  }
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

Result SmtEngine::assertFormula(const Node& formula, bool inUnsatCore)
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();

  Trace("smt") << "SmtEngine::assertFormula(" << formula << ")" << endl;

  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdAssert(getOutputManager().getDumpOut(), formula);
  }

  // Substitute out any abstract values in ex
  Node n = d_absValues->substituteAbstractValues(formula);

  d_asserts->assertFormula(n, inUnsatCore);
  return quickCheck().asEntailmentResult();
}/* SmtEngine::assertFormula() */

/*
   --------------------------------------------------------------------------
    Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SmtEngine::declareSygusVar(Node var)
{
  SmtScope smts(this);
  d_sygusSolver->declareSygusVar(var);
  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdDeclareVar(
        getOutputManager().getDumpOut(), var, var.getType());
  }
  // don't need to set that the conjecture is stale
}

void SmtEngine::declareSynthFun(Node func,
                                TypeNode sygusType,
                                bool isInv,
                                const std::vector<Node>& vars)
{
  SmtScope smts(this);
  d_state->doPendingPops();
  d_sygusSolver->declareSynthFun(func, sygusType, isInv, vars);

  // !!! TEMPORARY: We cannot construct a SynthFunCommand since we cannot
  // construct a Term-level Grammar from a Node-level sygus TypeNode. Thus we
  // must print the command using the Node-level utility method for now.

  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdSynthFun(
        getOutputManager().getDumpOut(), func, vars, isInv, sygusType);
  }
}
void SmtEngine::declareSynthFun(Node func,
                                bool isInv,
                                const std::vector<Node>& vars)
{
  // use a null sygus type
  TypeNode sygusType;
  declareSynthFun(func, sygusType, isInv, vars);
}

void SmtEngine::assertSygusConstraint(Node constraint)
{
  SmtScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusConstraint(constraint);
  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdConstraint(getOutputManager().getDumpOut(),
                                       constraint);
  }
}

void SmtEngine::assertSygusInvConstraint(Node inv,
                                         Node pre,
                                         Node trans,
                                         Node post)
{
  SmtScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusInvConstraint(inv, pre, trans, post);
  if (Dump.isOn("raw-benchmark"))
  {
    getPrinter().toStreamCmdInvConstraint(
        getOutputManager().getDumpOut(), inv, pre, trans, post);
  }
}

Result SmtEngine::checkSynth()
{
  SmtScope smts(this);
  finishInit();
  return d_sygusSolver->checkSynth(*d_asserts);
}

/*
   --------------------------------------------------------------------------
    End of Handling SyGuS commands
   --------------------------------------------------------------------------
*/

void SmtEngine::declarePool(const Node& p, const std::vector<Node>& initValue)
{
  Assert(p.isVar() && p.getType().isSet());
  finishInit();
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("declareTermPool");
  qe->declarePool(p, initValue);
}

Node SmtEngine::simplify(const Node& ex)
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  // ensure we've processed assertions
  d_smtSolver->processAssertions(*d_asserts);
  return d_pp->simplify(ex);
}

Node SmtEngine::expandDefinitions(const Node& ex)
{
  getResourceManager()->spendResource(Resource::PreprocessStep);
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  return d_pp->expandDefinitions(ex);
}

// TODO(#1108): Simplify the error reporting of this method.
Node SmtEngine::getValue(const Node& ex) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetValue(d_outMgr.getDumpOut(), {ex});
  }
  TypeNode expectedType = ex.getType();

  // Substitute out any abstract values in ex and expand
  Node n = d_pp->expandDefinitions(ex);

  Trace("smt") << "--- getting value of " << n << endl;
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
  Model* m = getAvailableModel("get-value");
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

  if (d_env->getOption(options::abstractValues)
      && resultNode.getType().isArray())
  {
    resultNode = d_absValues->mkAbstractValue(resultNode);
    Trace("smt") << "--- abstract value >> " << resultNode << endl;
  }

  return resultNode;
}

std::vector<Node> SmtEngine::getValues(const std::vector<Node>& exprs)
{
  std::vector<Node> result;
  for (const Node& e : exprs)
  {
    result.push_back(getValue(e));
  }
  return result;
}

// TODO(#1108): Simplify the error reporting of this method.
Model* SmtEngine::getModel() {
  Trace("smt") << "SMT getModel()" << endl;
  SmtScope smts(this);

  finishInit();

  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetModel(getOutputManager().getDumpOut());
  }

  Model* m = getAvailableModel("get model");

  // Since model m is being returned to the user, we must ensure that this
  // model object remains valid with future check-sat calls. Hence, we set
  // the theory engine into "eager model building" mode. TODO #2648: revisit.
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->setEagerModelBuilding();

  if (d_env->getOption(options::modelCoresMode)
      != options::ModelCoresMode::NONE)
  {
    // If we enabled model cores, we compute a model core for m based on our
    // (expanded) assertions using the model core builder utility
    std::vector<Node> eassertsProc = getExpandedAssertions();
    ModelCoreBuilder::setModelCore(eassertsProc,
                                   m->getTheoryModel(),
                                   d_env->getOption(options::modelCoresMode));
  }
  // set the information on the SMT-level model
  Assert(m != nullptr);
  m->d_inputName = d_state->getFilename();
  m->d_isKnownSat = (d_state->getMode() == SmtMode::SAT);
  return m;
}

Result SmtEngine::blockModel()
{
  Trace("smt") << "SMT blockModel()" << endl;
  SmtScope smts(this);

  finishInit();

  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdBlockModel(getOutputManager().getDumpOut());
  }

  Model* m = getAvailableModel("block model");

  if (d_env->getOption(options::blockModelsMode)
      == options::BlockModelsMode::NONE)
  {
    std::stringstream ss;
    ss << "Cannot block model when block-models is set to none.";
    throw RecoverableModalException(ss.str().c_str());
  }

  // get expanded assertions
  std::vector<Node> eassertsProc = getExpandedAssertions();
  Node eblocker =
      ModelBlocker::getModelBlocker(eassertsProc,
                                    m->getTheoryModel(),
                                    d_env->getOption(options::blockModelsMode));
  Trace("smt") << "Block formula: " << eblocker << std::endl;
  return assertFormula(eblocker);
}

Result SmtEngine::blockModelValues(const std::vector<Node>& exprs)
{
  Trace("smt") << "SMT blockModelValues()" << endl;
  SmtScope smts(this);

  finishInit();

  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdBlockModelValues(getOutputManager().getDumpOut(),
                                             exprs);
  }

  Model* m = getAvailableModel("block model values");

  // get expanded assertions
  std::vector<Node> eassertsProc = getExpandedAssertions();
  // we always do block model values mode here
  Node eblocker =
      ModelBlocker::getModelBlocker(eassertsProc,
                                    m->getTheoryModel(),
                                    options::BlockModelsMode::VALUES,
                                    exprs);
  return assertFormula(eblocker);
}

std::pair<Node, Node> SmtEngine::getSepHeapAndNilExpr(void)
{
  if (!getLogicInfo().isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot obtain separation logic expressions if not using the "
        "separation logic theory.";
    throw RecoverableModalException(msg);
  }
  NodeManagerScope nms(getNodeManager());
  Node heap;
  Node nil;
  Model* m = getAvailableModel("get separation logic heap and nil");
  TheoryModel* tm = m->getTheoryModel();
  if (!tm->getHeapModel(heap, nil))
  {
    const char* msg =
        "Failed to obtain heap/nil "
        "expressions from theory model.";
    throw RecoverableModalException(msg);
  }
  return std::make_pair(heap, nil);
}

std::vector<Node> SmtEngine::getExpandedAssertions()
{
  std::vector<Node> easserts = getAssertions();
  // must expand definitions
  std::vector<Node> eassertsProc;
  std::unordered_map<Node, Node> cache;
  for (const Node& e : easserts)
  {
    Node eae = d_pp->expandDefinitions(e, cache);
    eassertsProc.push_back(eae);
  }
  return eassertsProc;
}
Env& SmtEngine::getEnv() { return *d_env.get(); }

void SmtEngine::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  if (!getLogicInfo().isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot declare heap if not using the separation logic theory.";
    throw RecoverableModalException(msg);
  }
  SmtScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  te->declareSepHeap(locT, dataT);
}

bool SmtEngine::getSepHeapTypes(TypeNode& locT, TypeNode& dataT)
{
  SmtScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  return te->getSepHeapTypes(locT, dataT);
}

Node SmtEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Node SmtEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

void SmtEngine::checkProof()
{
  Assert(d_env->getOption(options::produceProofs));
  // internal check the proof
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  if (d_env->getOption(options::proofEagerChecking))
  {
    pe->checkProof(d_asserts->getAssertionList());
  }
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pePfn = pe->getProof();
  if (d_env->getOption(options::checkProofs))
  {
    d_pfManager->checkProof(pePfn, *d_asserts);
  }
}

StatisticsRegistry& SmtEngine::getStatisticsRegistry()
{
  return d_env->getStatisticsRegistry();
}

UnsatCore SmtEngine::getUnsatCoreInternal()
{
  if (!d_env->getOption(options::unsatCores))
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
  return UnsatCore(core);
}

void SmtEngine::checkUnsatCore() {
  Assert(d_env->getOption(options::unsatCores))
      << "cannot check unsat core if unsat cores are turned off";

  Notice() << "SmtEngine::checkUnsatCore(): generating unsat core" << endl;
  UnsatCore core = getUnsatCore();

  // initialize the core checker
  std::unique_ptr<SmtEngine> coreChecker;
  initializeSubsolver(coreChecker);
  coreChecker->getOptions().set(options::checkUnsatCores, false);
  // disable all proof options
  coreChecker->getOptions().set(options::produceProofs, false);
  coreChecker->getOptions().set(options::checkProofs, false);
  coreChecker->getOptions().set(options::proofEagerChecking, false);

  // set up separation logic heap if necessary
  TypeNode sepLocType, sepDataType;
  if (getSepHeapTypes(sepLocType, sepDataType))
  {
    coreChecker->declareSepHeap(sepLocType, sepDataType);
  }

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions"
           << std::endl;
  theory::TrustSubstitutionMap& tls = d_env->getTopLevelSubstitutions();
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Node assertionAfterExpansion = tls.apply(*i, false);
    Notice() << "SmtEngine::checkUnsatCore(): pushing core member " << *i
             << ", expanded to " << assertionAfterExpansion << "\n";
    coreChecker->assertFormula(assertionAfterExpansion);
  }
  Result r;
  try {
    r = coreChecker->checkSat();
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
  context::CDList<Node>* al = d_asserts->getAssertionList();
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(al != nullptr)
      << "don't have an assertion list to check in SmtEngine::checkModel()";

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  Notice() << "SmtEngine::checkModel(): generating model" << endl;
  Model* m = getAvailableModel("check model");
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

UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << std::endl;
  SmtScope smts(this);
  finishInit();
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetUnsatCore(getOutputManager().getDumpOut());
  }
  return getUnsatCoreInternal();
}

void SmtEngine::getRelevantInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  Assert(d_state->getMode() == SmtMode::UNSAT);
  // generate with new proofs
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pfn =
      d_pfManager->getFinalProof(pe->getProof(), *d_asserts);
  d_ucManager->getRelevantInstantiations(pfn, insts);
}

std::string SmtEngine::getProof()
{
  Trace("smt") << "SMT getProof()\n";
  SmtScope smts(this);
  finishInit();
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetProof(getOutputManager().getDumpOut());
  }
  if (!d_env->getOption(options::produceProofs))
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

void SmtEngine::printInstantiations( std::ostream& out ) {
  SmtScope smts(this);
  finishInit();
  if (d_env->getOption(options::instFormatMode) == options::InstFormatMode::SZS)
  {
    out << "% SZS output start Proof for " << d_state->getFilename()
        << std::endl;
  }
  QuantifiersEngine* qe = getAvailableQuantifiersEngine("printInstantiations");

  // First, extract and print the skolemizations
  bool printed = false;
  bool reqNames = !d_env->getOption(options::printInstFull);
  // only print when in list mode
  if (d_env->getOption(options::printInstMode) == options::PrintInstMode::LIST)
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
  std::map<Node, std::vector<std::vector<Node>>> insts;
  getInstantiationTermVectors(insts);
  for (const std::pair<const Node, std::vector<std::vector<Node>>>& i : insts)
  {
    if (i.second.empty())
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
    if (d_env->getOption(options::printInstMode) == options::PrintInstMode::NUM)
    {
      out << "(num-instantiations " << name << " " << i.second.size() << ")"
          << std::endl;
    }
    else
    {
      Assert(d_env->getOption(options::printInstMode)
             == options::PrintInstMode::LIST);
      InstantiationList ilist(name, i.second);
      out << ilist;
    }
    printed = true;
  }
  // if we did not print anything, we indicate this
  if (!printed)
  {
    out << "No instantiations" << std::endl;
  }
  if (d_env->getOption(options::instFormatMode) == options::InstFormatMode::SZS)
  {
    out << "% SZS output end Proof for " << d_state->getFilename() << std::endl;
  }
}

void SmtEngine::getInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  SmtScope smts(this);
  finishInit();
  if (d_env->getOption(options::produceProofs)
      && (!d_env->getOption(options::unsatCores)
          || d_env->getOption(options::unsatCoresMode) == options::UnsatCoresMode::FULL_PROOF)
      && getSmtMode() == SmtMode::UNSAT)
  {
    // minimize instantiations based on proof manager
    getRelevantInstantiationTermVectors(insts);
  }
  else
  {
    QuantifiersEngine* qe =
        getAvailableQuantifiersEngine("getInstantiationTermVectors");
    // otherwise, just get the list of all instantiations
    qe->getInstantiationTermVectors(insts);
  }
}

bool SmtEngine::getSynthSolutions(std::map<Node, Node>& solMap)
{
  SmtScope smts(this);
  finishInit();
  return d_sygusSolver->getSynthSolutions(solMap);
}

Node SmtEngine::getQuantifierElimination(Node q, bool doFull, bool strict)
{
  SmtScope smts(this);
  finishInit();
  const LogicInfo& logic = getLogicInfo();
  if (!logic.isPure(THEORY_ARITH) && strict)
  {
    Warning() << "Unexpected logic for quantifier elimination " << logic
              << endl;
  }
  return d_quantElimSolver->getQuantifierElimination(
      *d_asserts, q, doFull, d_isInternalSubsolver);
}

bool SmtEngine::getInterpol(const Node& conj,
                            const TypeNode& grammarType,
                            Node& interpol)
{
  SmtScope smts(this);
  finishInit();
  bool success = d_interpolSolver->getInterpol(conj, grammarType, interpol);
  // notify the state of whether the get-interpol call was successfuly, which
  // impacts the SMT mode.
  d_state->notifyGetInterpol(success);
  return success;
}

bool SmtEngine::getInterpol(const Node& conj, Node& interpol)
{
  TypeNode grammarType;
  return getInterpol(conj, grammarType, interpol);
}

bool SmtEngine::getAbduct(const Node& conj,
                          const TypeNode& grammarType,
                          Node& abd)
{
  SmtScope smts(this);
  finishInit();
  bool success = d_abductSolver->getAbduct(conj, grammarType, abd);
  // notify the state of whether the get-abduct call was successfuly, which
  // impacts the SMT mode.
  d_state->notifyGetAbduct(success);
  return success;
}

bool SmtEngine::getAbduct(const Node& conj, Node& abd)
{
  TypeNode grammarType;
  return getAbduct(conj, grammarType, abd);
}

void SmtEngine::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  SmtScope smts(this);
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiatedQuantifiedFormulas");
  qe->getInstantiatedQuantifiedFormulas(qs);
}

void SmtEngine::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node>>& tvecs)
{
  SmtScope smts(this);
  QuantifiersEngine* qe =
      getAvailableQuantifiersEngine("getInstantiationTermVectors");
  qe->getInstantiationTermVectors(q, tvecs);
}

std::vector<Node> SmtEngine::getAssertions()
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetAssertions(getOutputManager().getDumpOut());
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if (!d_env->getOption(options::produceAssertions))
  {
    const char* msg =
      "Cannot query the current assertion list when not in produce-assertions mode.";
    throw ModalException(msg);
  }
  context::CDList<Node>* al = d_asserts->getAssertionList();
  Assert(al != nullptr);
  std::vector<Node> res;
  for (const Node& n : *al)
  {
    res.emplace_back(n);
  }
  // copy the result out
  return res;
}

void SmtEngine::push()
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  Trace("smt") << "SMT push()" << endl;
  d_smtSolver->processAssertions(*d_asserts);
  if(Dump.isOn("benchmark")) {
    getPrinter().toStreamCmdPush(getOutputManager().getDumpOut());
  }
  d_state->userPush();
}

void SmtEngine::pop() {
  SmtScope smts(this);
  finishInit();
  Trace("smt") << "SMT pop()" << endl;
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdPop(getOutputManager().getDumpOut());
  }
  d_state->userPop();

  // Clear out assertion queues etc., in case anything is still in there
  d_asserts->clearCurrent();
  // clear the learned literals from the preprocessor
  d_pp->clearLearnedLiterals();

  Trace("userpushpop") << "SmtEngine: popped to level "
                       << getUserContext()->getLevel() << endl;
  // should we reset d_status here?
  // SMT-LIBv2 spec seems to imply no, but it would make sense to..
}

void SmtEngine::resetAssertions()
{
  SmtScope smts(this);

  if (!d_state->isFullyInited())
  {
    // We're still in Start Mode, nothing asserted yet, do nothing.
    // (see solver execution modes in the SMT-LIB standard)
    Assert(getContext()->getLevel() == 0);
    Assert(getUserContext()->getLevel() == 0);
    getDumpManager()->resetAssertions();
    return;
  }


  Trace("smt") << "SMT resetAssertions()" << endl;
  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdResetAssertions(getOutputManager().getDumpOut());
  }

  d_asserts->clearCurrent();
  d_state->notifyResetAssertions();
  getDumpManager()->resetAssertions();
  // push the state to maintain global context around everything
  d_state->setup();

  // reset SmtSolver, which will construct a new prop engine
  d_smtSolver->resetAssertions();
}

void SmtEngine::interrupt()
{
  if (!d_state->isFullyInited())
  {
    return;
  }
  d_smtSolver->interrupt();
}

void SmtEngine::setResourceLimit(uint64_t units, bool cumulative)
{
  if (cumulative)
  {
    d_env->d_options.set(options::cumulativeResourceLimit__option_t(), units);
  }
  else
  {
    d_env->d_options.set(options::perCallResourceLimit__option_t(), units);
  }
}
void SmtEngine::setTimeLimit(uint64_t millis)
{
  d_env->d_options.set(options::perCallMillisecondLimit__option_t(), millis);
}

unsigned long SmtEngine::getResourceUsage() const
{
  return getResourceManager()->getResourceUsage();
}

unsigned long SmtEngine::getTimeUsage() const
{
  return getResourceManager()->getTimeUsage();
}

unsigned long SmtEngine::getResourceRemaining() const
{
  return getResourceManager()->getResourceRemaining();
}

NodeManager* SmtEngine::getNodeManager() const
{
  return d_env->getNodeManager();
}

void SmtEngine::printStatistics(std::ostream& out) const
{
  d_env->getStatisticsRegistry().print(out);
}

void SmtEngine::printStatisticsSafe(int fd) const
{
  d_env->getStatisticsRegistry().printSafe(fd);
}

void SmtEngine::printStatisticsDiff(std::ostream& out) const
{
  d_env->getStatisticsRegistry().printDiff(out);
  d_env->getStatisticsRegistry().storeSnapshot();
}

void SmtEngine::setUserAttribute(const std::string& attr,
                                 Node expr,
                                 const std::vector<Node>& expr_values,
                                 const std::string& str_value)
{
  SmtScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->setUserAttribute(attr, expr, expr_values, str_value);
}

void SmtEngine::setOption(const std::string& key, const std::string& value)
{
  NodeManagerScope nms(getNodeManager());
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;

  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdSetOption(
        getOutputManager().getDumpOut(), key, value);
  }

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
  getOptions().setOption(key, optionarg);
}

void SmtEngine::setIsInternalSubsolver() { d_isInternalSubsolver = true; }

bool SmtEngine::isInternalSubsolver() const { return d_isInternalSubsolver; }

std::string SmtEngine::getOption(const std::string& key) const
{
  NodeManagerScope nms(getNodeManager());
  NodeManager* nm = d_env->getNodeManager();

  Trace("smt") << "SMT getOption(" << key << ")" << endl;

  if (key.find("command-verbosity:") == 0)
  {
    auto it = d_commandVerbosity.find(key.substr(std::strlen("command-verbosity:")));
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

  if (Dump.isOn("benchmark"))
  {
    getPrinter().toStreamCmdGetOption(d_outMgr.getDumpOut(), key);
  }

  if (key == "command-verbosity")
  {
    vector<Node> result;
    Node defaultVerbosity;
    for (const auto& verb: d_commandVerbosity)
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

  std::string atom = getOptions().getOption(key);

  if (atom != "true" && atom != "false")
  {
    try
    {
      Integer z(atom);
    }
    catch (std::invalid_argument&)
    {
      atom = "\"" + atom + "\"";
    }
  }

  return atom;
}

Options& SmtEngine::getOptions() { return d_env->d_options; }

const Options& SmtEngine::getOptions() const { return d_env->getOptions(); }

ResourceManager* SmtEngine::getResourceManager() const
{
  return d_env->getResourceManager();
}

DumpManager* SmtEngine::getDumpManager() { return d_env->getDumpManager(); }

const Printer& SmtEngine::getPrinter() const { return d_env->getPrinter(); }

OutputManager& SmtEngine::getOutputManager() { return d_outMgr; }

theory::Rewriter* SmtEngine::getRewriter() { return d_env->getRewriter(); }

}  // namespace cvc5
