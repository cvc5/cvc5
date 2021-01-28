/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The main entry point into the CVC4 library's SMT interface
 **
 ** The main entry point into the CVC4 library's SMT interface.
 **/

#include "smt/smt_engine.h"

#include "api/cvc4cpp.h"
#include "base/check.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "base/output.h"
#include "decision/decision_engine.h"
#include "expr/node.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/printer_options.h"
#include "options/smt_options.h"
#include "options/theory_options.h"
#include "printer/printer.h"
#include "proof/proof_manager.h"
#include "proof/unsat_core.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/check_models.h"
#include "smt/defined_function.h"
#include "smt/dump_manager.h"
#include "smt/interpolation_solver.h"
#include "smt/listeners.h"
#include "smt/logic_request.h"
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
#include "theory/quantifiers/instantiation_list.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "util/random.h"
#include "util/resource_manager.h"

// required for hacks related to old proofs for unsat cores
#include "base/configuration.h"
#include "base/configuration_private.h"

using namespace std;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {

SmtEngine::SmtEngine(NodeManager* nm, Options* optr)
    : d_state(new SmtEngineState(*this)),
      d_nodeManager(nm),
      d_absValues(new AbstractValues(d_nodeManager)),
      d_asserts(new Assertions(getUserContext(), *d_absValues.get())),
      d_dumpm(new DumpManager(getUserContext())),
      d_routListener(new ResourceOutListener(*this)),
      d_snmListener(new SmtNodeManagerListener(*d_dumpm.get(), d_outMgr)),
      d_smtSolver(nullptr),
      d_proofManager(nullptr),
      d_model(nullptr),
      d_checkModels(nullptr),
      d_pfManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_definedFunctions(nullptr),
      d_sygusSolver(nullptr),
      d_abductSolver(nullptr),
      d_interpolSolver(nullptr),
      d_quantElimSolver(nullptr),
      d_logic(),
      d_originalOptions(),
      d_isInternalSubsolver(false),
      d_statisticsRegistry(nullptr),
      d_stats(nullptr),
      d_outMgr(this),
      d_resourceManager(nullptr),
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
  // listen to node manager events
  d_nodeManager->subscribeEvents(d_snmListener.get());
  // listen to resource out
  d_resourceManager->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SmtEngineStatistics());
  // reset the preprocessor
  d_pp.reset(new smt::Preprocessor(
      *this, getUserContext(), *d_absValues.get(), *d_stats));
  // make the SMT solver
  d_smtSolver.reset(
      new SmtSolver(*this, *d_state, d_resourceManager.get(), *d_pp, *d_stats));
  // make the SyGuS solver
  d_sygusSolver.reset(
      new SygusSolver(*d_smtSolver, *d_pp, getUserContext(), d_outMgr));
  // make the quantifier elimination solver
  d_quantElimSolver.reset(new QuantElimSolver(*d_smtSolver));

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
  return d_state->getUserContext();
}
context::Context* SmtEngine::getContext() { return d_state->getContext(); }

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
  if (!d_logic.isLocked())
  {
    setLogicInternal();
  }

  // set the random seed
  Random::getRandom().setSeed(options::seed());

  // Call finish init on the options manager. This inializes the resource
  // manager based on the options, and sets up the best default options
  // based on our heuristics.
  d_optm->finishInit(d_logic, d_isInternalSubsolver);

  ProofNodeManager* pnm = nullptr;
  if (options::proofNew())
  {
    d_pfManager.reset(new PfManager(getUserContext(), this));
    PreprocessProofGenerator* pppg = d_pfManager->getPreprocessProofGenerator();
    // use this proof node manager
    pnm = d_pfManager->getProofNodeManager();
    // enable proof support in the rewriter
    d_rewriter->setProofNodeManager(pnm);
    // enable it in the assertions pipeline
    d_asserts->setProofGenerator(pppg);
    // enable it in the SmtSolver
    d_smtSolver->setProofNodeManager(pnm);
    // enabled proofs in the preprocessor
    d_pp->setProofGenerator(pppg);
  }

  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  d_smtSolver->finishInit(const_cast<const LogicInfo&>(d_logic));

  // now can construct the SMT-level model object
  TheoryEngine* te = d_smtSolver->getTheoryEngine();
  Assert(te != nullptr);
  TheoryModel* tm = te->getModel();
  if (tm != nullptr)
  {
    d_model.reset(new Model(tm));
    // make the check models utility
    d_checkModels.reset(new CheckModels(*d_smtSolver.get()));
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
      getOutputManager().getPrinter().toStreamCmdComment(
          getOutputManager().getDumpOut(),
          "CVC4 always dumps the most general, all-supported logic (below), as "
          "some internals might require the use of a logic more general than "
          "the input.");
      getOutputManager().getPrinter().toStreamCmdSetBenchmarkLogic(
          getOutputManager().getDumpOut(), everything.getLogicString());
  }

  // initialize the dump manager
  d_dumpm->finishInit();

  // subsolvers
  if (options::produceAbducts())
  {
    d_abductSolver.reset(new AbductionSolver(this));
  }
  if (options::produceInterpols() != options::ProduceInterpols::NONE)
  {
    d_interpolSolver.reset(new InterpolationSolver(this));
  }

  d_pp->finishInit();

  AlwaysAssert(getPropEngine()->getAssertionLevel() == 0)
      << "The PropEngine has pushed but the SmtEngine "
         "hasn't finished initializing!";

  Assert(d_logic.isLocked());

  // store that we are finished initializing
  d_state->finishInit();
  Trace("smt-debug") << "SmtEngine::finishInit done" << std::endl;
}

void SmtEngine::shutdown() {
  d_state->shutdown();

  d_smtSolver->shutdown();
}

SmtEngine::~SmtEngine()
{
  SmtScope smts(this);

  try {
    shutdown();

    // global push/pop around everything, to ensure proper destruction
    // of context-dependent data structures
    d_state->cleanup();

    d_definedFunctions->deleteSelf();

    //destroy all passes before destroying things that they refer to
    d_pp->cleanup();

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
    d_rewriter.reset(nullptr);
    d_pfManager.reset(nullptr);

    d_absValues.reset(nullptr);
    d_asserts.reset(nullptr);
    d_dumpm.reset(nullptr);
    d_model.reset(nullptr);

    d_sygusSolver.reset(nullptr);

    d_smtSolver.reset(nullptr);

    d_stats.reset(nullptr);
    d_nodeManager->unsubscribeEvents(d_snmListener.get());
    d_snmListener.reset(nullptr);
    d_routListener.reset(nullptr);
    d_optm.reset(nullptr);
    d_pp.reset(nullptr);
    // d_resourceManager must be destroyed before d_statisticsRegistry
    d_resourceManager.reset(nullptr);
    d_statisticsRegistry.reset(nullptr);
    // destroy the state
    d_state.reset(nullptr);
  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << endl
              << e << endl;
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
      getOutputManager().getPrinter().toStreamCmdSetBenchmarkLogic(
          getOutputManager().getDumpOut(), d_logic.getLogicString());
    }
  }
  catch (IllegalArgumentException& e)
  {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) { setLogic(string(logic)); }

const LogicInfo& SmtEngine::getLogicInfo() const { return d_logic; }

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
  d_state->setFilename(filename);
  // Copy the original options. This is called prior to beginning parsing.
  // Hence reset should revert to these options, which note is after reading
  // the command line.
  d_originalOptions.copyValues(d_options);
}

const std::string& SmtEngine::getFilename() const
{
  return d_state->getFilename();
}
void SmtEngine::setLogicInternal()
{
  Assert(!d_state->isFullyInited())
      << "setting logic in SmtEngine but the engine has already"
         " finished initializing for this run";
  d_logic.lock();
  d_userLogic.lock();
}

void SmtEngine::setInfo(const std::string& key, const CVC4::SExpr& value)
{
  SmtScope smts(this);

  Trace("smt") << "SMT setInfo(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    if(key == "status") {
      string s = value.getValue();
      Result::Sat status =
          (s == "sat") ? Result::SAT
                       : ((s == "unsat") ? Result::UNSAT : Result::SAT_UNKNOWN);
      getOutputManager().getPrinter().toStreamCmdSetBenchmarkStatus(
          getOutputManager().getDumpOut(), status);
    } else {
      getOutputManager().getPrinter().toStreamCmdSetInfo(
          getOutputManager().getDumpOut(), key, value);
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
    d_state->setFilename(value.getValue());
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
    d_state->notifyExpectedStatus(s);
    return;
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

CVC4::SExpr SmtEngine::getInfo(const std::string& key) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if (key == "all-statistics")
  {
    vector<SExpr> stats;
    StatisticsRegistry* sr = d_nodeManager->getStatisticsRegistry();
    for (StatisticsRegistry::const_iterator i = sr->begin(); i != sr->end();
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
    Result status = d_state->getStatus();
    switch (status.asSatisfiabilityResult().isSat())
    {
      case Result::SAT: return SExpr(SExpr::Keyword("sat"));
      case Result::UNSAT: return SExpr(SExpr::Keyword("unsat"));
      default: return SExpr(SExpr::Keyword("unknown"));
    }
  }
  if (key == "time")
  {
    return SExpr(std::clock());
  }
  if (key == "reason-unknown")
  {
    Result status = d_state->getStatus();
    if (!status.isNull() && status.isUnknown())
    {
      std::stringstream ss;
      ss << status.whyUnknown();
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
    size_t ulevel = d_state->getNumUserLevels();
    AlwaysAssert(ulevel <= std::numeric_limits<unsigned long int>::max());
    return SExpr(static_cast<unsigned long int>(ulevel));
  }
  Assert(key == "all-options");
  // get the options, like all-statistics
  std::vector<std::vector<std::string>> current_options =
      Options::current()->getOptions();
  return SExpr::parseListOfListOfAtoms(current_options);
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
      throw TypeCheckingException(func.toExpr(), ss.str());
    }
  }
}

void SmtEngine::debugCheckFunctionBody(Node formula,
                                       const std::vector<Node>& formals,
                                       Node func)
{
  TypeNode formulaType = formula.getType(options::typeChecking());
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
      throw TypeCheckingException(func.toExpr(), ss.str());
    }
  } else {
    if(! formulaType.isComparableTo(funcType)) {
      stringstream ss;
      ss << "Declared type of defined constant does not match its definition\n"
         << "The constant   : " << func << "\n"
         << "Declared type  : " << funcType << "\n"
         << "The definition : " << formula << "\n"
         << "Definition type: " << formulaType;
      throw TypeCheckingException(func.toExpr(), ss.str());
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
  std::vector<Node> nFormals;
  nFormals.reserve(formals.size());

  for (const Node& formal : formals)
  {
    nFormals.push_back(formal);
  }

  DefineFunctionNodeCommand nc(ss.str(), func, nFormals, formula);
  d_dumpm->addToDump(nc, "declarations");

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  // Substitute out any abstract values in formula
  Node formNode = d_absValues->substituteAbstractValues(formula);
  DefinedFunction def(func, formals, formNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  Debug("smt") << "definedFunctions insert " << func << " " << formNode << endl;

  if (global)
  {
    d_definedFunctions->insertAtContextLevelZero(func, def);
  }
  else
  {
    d_definedFunctions->insert(func, def);
  }
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
    getOutputManager().getPrinter().toStreamCmdDefineFunctionRec(
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
    d_asserts->addDefineFunRecDefinition(lem, global);
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

bool SmtEngine::isDefinedFunction(Node func)
{
  Debug("smt") << "isDefined function " << func << "?" << std::endl;
  return d_definedFunctions->find(func) != d_definedFunctions->end();
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
  if (!options::assignFunctionValues())
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

  if (!options::produceModels())
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
    getOutputManager().getPrinter().toStreamCmdCheckSat(
        getOutputManager().getDumpOut(), assumption);
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
      getOutputManager().getPrinter().toStreamCmdCheckSat(
          getOutputManager().getDumpOut());
    }
    else
    {
      getOutputManager().getPrinter().toStreamCmdCheckSatAssuming(
          getOutputManager().getDumpOut(), assumptions);
    }
  }
  return checkSatInternal(assumptions, inUnsatCore, false);
}

Result SmtEngine::checkEntailed(const Node& node, bool inUnsatCore)
{
  if (Dump.isOn("benchmark"))
  {
    getOutputManager().getPrinter().toStreamCmdQuery(
        getOutputManager().getDumpOut(), node);
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
    if(options::checkModels()) {
      if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        checkModel();
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if (options::checkProofsNew() || options::proofNewEagerChecking())
    {
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        if ((options::checkProofsNew() || options::proofNewEagerChecking())
            && !options::proofNew())
        {
          throw ModalException(
              "Cannot check-proofs-new because proof-new was disabled.");
        }
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
    // Notice that we do not notify the state of this result. If we wanted to
    // make the solver resume a working state after an interupt, then we would
    // implement a different callback and use it here, e.g.
    // d_state.notifyCheckSatInterupt.
    Result::UnknownExplanation why = d_resourceManager->outOfResources()
                                         ? Result::RESOURCEOUT
                                         : Result::TIMEOUT;
    return Result(Result::SAT_UNKNOWN, why, d_state->getFilename());
  }
}

std::vector<Node> SmtEngine::getUnsatAssumptions(void)
{
  Trace("smt") << "SMT getUnsatAssumptions()" << endl;
  SmtScope smts(this);
  if (!options::unsatAssumptions())
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
    getOutputManager().getPrinter().toStreamCmdGetUnsatAssumptions(
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

  if (Dump.isOn("raw-benchmark")) {
    getOutputManager().getPrinter().toStreamCmdAssert(
        getOutputManager().getDumpOut(), formula);
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
    getOutputManager().getPrinter().toStreamCmdDeclareVar(
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
    getOutputManager().getPrinter().toStreamCmdSynthFun(
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
    getOutputManager().getPrinter().toStreamCmdConstraint(
        getOutputManager().getDumpOut(), constraint);
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
    getOutputManager().getPrinter().toStreamCmdInvConstraint(
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

Node SmtEngine::simplify(const Node& ex)
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  // ensure we've processed assertions
  d_smtSolver->processAssertions(*d_asserts);
  return d_pp->simplify(ex);
}

Node SmtEngine::expandDefinitions(const Node& ex, bool expandOnly)
{
  d_resourceManager->spendResource(ResourceManager::Resource::PreprocessStep);

  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  return d_pp->expandDefinitions(ex, expandOnly);
}

// TODO(#1108): Simplify the error reporting of this method.
Node SmtEngine::getValue(const Node& ex) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  if(Dump.isOn("benchmark")) {
    d_outMgr.getPrinter().toStreamCmdGetValue(d_outMgr.getDumpOut(), {ex});
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

  if(options::abstractValues() && resultNode.getType().isArray()) {
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

  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdGetModel(
        getOutputManager().getDumpOut());
  }

  Model* m = getAvailableModel("get model");

  // Since model m is being returned to the user, we must ensure that this
  // model object remains valid with future check-sat calls. Hence, we set
  // the theory engine into "eager model building" mode. TODO #2648: revisit.
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->setEagerModelBuilding();

  if (options::modelCoresMode() != options::ModelCoresMode::NONE)
  {
    // If we enabled model cores, we compute a model core for m based on our
    // (expanded) assertions using the model core builder utility
    std::vector<Node> eassertsProc = getExpandedAssertions();
    ModelCoreBuilder::setModelCore(
        eassertsProc, m->getTheoryModel(), options::modelCoresMode());
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
    getOutputManager().getPrinter().toStreamCmdBlockModel(
        getOutputManager().getDumpOut());
  }

  Model* m = getAvailableModel("block model");

  if (options::blockModelsMode() == options::BlockModelsMode::NONE)
  {
    std::stringstream ss;
    ss << "Cannot block model when block-models is set to none.";
    throw RecoverableModalException(ss.str().c_str());
  }

  // get expanded assertions
  std::vector<Node> eassertsProc = getExpandedAssertions();
  Node eblocker = ModelBlocker::getModelBlocker(
      eassertsProc, m->getTheoryModel(), options::blockModelsMode());
  return assertFormula(eblocker);
}

Result SmtEngine::blockModelValues(const std::vector<Node>& exprs)
{
  Trace("smt") << "SMT blockModelValues()" << endl;
  SmtScope smts(this);

  finishInit();

  if (Dump.isOn("benchmark"))
  {
    getOutputManager().getPrinter().toStreamCmdBlockModelValues(
        getOutputManager().getDumpOut(), exprs);
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
  if (!d_logic.isTheoryEnabled(THEORY_SEP))
  {
    const char* msg =
        "Cannot obtain separation logic expressions if not using the "
        "separation logic theory.";
    throw RecoverableModalException(msg);
  }
  NodeManagerScope nms(d_nodeManager);
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
  std::unordered_map<Node, Node, NodeHashFunction> cache;
  for (const Node& e : easserts)
  {
    Node eae = d_pp->expandDefinitions(e, cache);
    eassertsProc.push_back(eae);
  }
  return eassertsProc;
}

void SmtEngine::declareSepHeap(TypeNode locT, TypeNode dataT)
{
  if (!d_logic.isTheoryEnabled(THEORY_SEP))
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
  Assert(options::proofNew());
  // internal check the proof
  PropEngine* pe = getPropEngine();
  Assert(pe != nullptr);
  Assert(pe->getProof() != nullptr);
  std::shared_ptr<ProofNode> pePfn = pe->getProof();
  if (options ::checkProofsNew())
  {
    d_pfManager->checkProof(pePfn, *d_asserts, *d_definedFunctions);
  }
}

UnsatCore SmtEngine::getUnsatCoreInternal()
{
#if IS_PROOFS_BUILD
  if (!options::unsatCores())
  {
    throw ModalException(
        "Cannot get an unsat core when produce-unsat-cores option is off.");
  }
  if (d_state->getMode() != SmtMode::UNSAT)
  {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by "
        "UNSAT/ENTAILED response.");
  }

  d_proofManager->traceUnsatCore();  // just to trigger core creation
  return UnsatCore(d_proofManager->extractUnsatCore());
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

  // initialize the core checker
  std::unique_ptr<SmtEngine> coreChecker;
  initializeSubsolver(coreChecker);
  coreChecker->getOptions().set(options::checkUnsatCores, false);

  // set up separation logic heap if necessary
  TypeNode sepLocType, sepDataType;
  if (getSepHeapTypes(sepLocType, sepDataType))
  {
    coreChecker->declareSepHeap(sepLocType, sepDataType);
  }

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions"
           << std::endl;
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Node assertionAfterExpansion = expandDefinitions(*i);
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

  // check the model with the check models utility
  Assert(d_checkModels != nullptr);
  d_checkModels->checkModel(m, al, hardFailure);
}

// TODO(#1108): Simplify the error reporting of this method.
UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << endl;
  SmtScope smts(this);
  finishInit();
  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdGetUnsatCore(
        getOutputManager().getDumpOut());
  }
  return getUnsatCoreInternal();
}

std::string SmtEngine::getProof()
{
  Trace("smt") << "SMT getProof()\n";
  SmtScope smts(this);
  finishInit();
  if (Dump.isOn("benchmark"))
  {
    getOutputManager().getPrinter().toStreamCmdGetProof(
        getOutputManager().getDumpOut());
  }
#if IS_PROOFS_BUILD
  if (!options::proofNew())
  {
    throw ModalException("Cannot get a proof when proof-new option is off.");
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
  d_pfManager->printProof(ss, pe->getProof(), *d_asserts, *d_definedFunctions);
  return ss.str();
#else  /* IS_PROOFS_BUILD */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::printInstantiations( std::ostream& out ) {
  SmtScope smts(this);
  finishInit();
  if (options::instFormatMode() == options::InstFormatMode::SZS)
  {
    out << "% SZS output start Proof for " << d_state->getFilename()
        << std::endl;
  }
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  QuantifiersEngine* qe = te->getQuantifiersEngine();

  // First, extract and print the skolemizations
  bool printed = false;
  bool reqNames = !options::printInstFull();
  // only print when in list mode
  if (options::printInstMode() == options::PrintInstMode::LIST)
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
    if (options::printInstMode() == options::PrintInstMode::NUM)
    {
      out << "(num-instantiations " << name << " " << i.second.size() << ")"
          << std::endl;
    }
    else
    {
      Assert(options::printInstMode() == options::PrintInstMode::LIST);
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
  if (options::instFormatMode() == options::InstFormatMode::SZS)
  {
    out << "% SZS output end Proof for " << d_state->getFilename() << std::endl;
  }
}

void SmtEngine::getInstantiationTermVectors(
    std::map<Node, std::vector<std::vector<Node>>>& insts)
{
  SmtScope smts(this);
  finishInit();
  if (options::proofNew() && getSmtMode() == SmtMode::UNSAT)
  {
    // TODO (project #37): minimize instantiations based on proof manager
  }
  else
  {
    TheoryEngine* te = getTheoryEngine();
    Assert(te != nullptr);
    QuantifiersEngine* qe = te->getQuantifiersEngine();
    // otherwise, just get the list of all instantiations
    qe->getInstantiationTermVectors(insts);
  }
}

void SmtEngine::printSynthSolution( std::ostream& out ) {
  SmtScope smts(this);
  finishInit();
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->printSynthSolution(out);
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
  if(!d_logic.isPure(THEORY_ARITH) && strict){
    Warning() << "Unexpected logic for quantifier elimination " << d_logic << endl;
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
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  QuantifiersEngine* qe = te->getQuantifiersEngine();
  qe->getInstantiatedQuantifiedFormulas(qs);
}

void SmtEngine::getInstantiationTermVectors(
    Node q, std::vector<std::vector<Node>>& tvecs)
{
  SmtScope smts(this);
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  QuantifiersEngine* qe = te->getQuantifiersEngine();
  qe->getInstantiationTermVectors(q, tvecs);
}

std::vector<Node> SmtEngine::getAssertions()
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdGetAssertions(
        getOutputManager().getDumpOut());
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!options::produceAssertions()) {
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
    getOutputManager().getPrinter().toStreamCmdPush(
        getOutputManager().getDumpOut());
  }
  d_state->userPush();
}

void SmtEngine::pop() {
  SmtScope smts(this);
  finishInit();
  Trace("smt") << "SMT pop()" << endl;
  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdPop(
        getOutputManager().getDumpOut());
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

void SmtEngine::reset()
{
  SmtScope smts(this);
  Trace("smt") << "SMT reset()" << endl;
  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdReset(
        getOutputManager().getDumpOut());
  }
  std::string filename = d_state->getFilename();
  Options opts;
  opts.copyValues(d_originalOptions);
  this->~SmtEngine();
  new (this) SmtEngine(d_nodeManager, &opts);
  // Restore data set after creation
  notifyStartParsing(filename);
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
    d_dumpm->resetAssertions();
    return;
  }


  Trace("smt") << "SMT resetAssertions()" << endl;
  if (Dump.isOn("benchmark"))
  {
    getOutputManager().getPrinter().toStreamCmdResetAssertions(
        getOutputManager().getDumpOut());
  }

  d_asserts->clearCurrent();
  d_state->notifyResetAssertions();
  d_dumpm->resetAssertions();
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

NodeManager* SmtEngine::getNodeManager() const { return d_nodeManager; }

Statistics SmtEngine::getStatistics() const
{
  return Statistics(*d_statisticsRegistry);
}

SExpr SmtEngine::getStatistic(std::string name) const
{
  return d_statisticsRegistry->getStatistic(name);
}

void SmtEngine::flushStatistics(std::ostream& out) const
{
  d_nodeManager->getStatisticsRegistry()->flushInformation(out);
  d_statisticsRegistry->flushInformation(out);
}

void SmtEngine::safeFlushStatistics(int fd) const
{
  d_nodeManager->getStatisticsRegistry()->safeFlushInformation(fd);
  d_statisticsRegistry->safeFlushInformation(fd);
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

void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
{
  // Always check whether the SmtEngine has been initialized (which is done
  // upon entering Assert mode the first time). No option can  be set after
  // initialized.
  if (d_state->isFullyInited())
  {
    throw ModalException("SmtEngine::setOption called after initialization.");
  }
  NodeManagerScope nms(d_nodeManager);
  Trace("smt") << "SMT setOption(" << key << ", " << value << ")" << endl;

  if(Dump.isOn("benchmark")) {
    getOutputManager().getPrinter().toStreamCmdSetOption(
        getOutputManager().getDumpOut(), key, value);
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
    d_outMgr.getPrinter().toStreamCmdGetOption(d_outMgr.getDumpOut(), key);
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

Options& SmtEngine::getOptions() { return d_options; }

const Options& SmtEngine::getOptions() const { return d_options; }

ResourceManager* SmtEngine::getResourceManager()
{
  return d_resourceManager.get();
}

DumpManager* SmtEngine::getDumpManager() { return d_dumpm.get(); }

const Printer* SmtEngine::getPrinter() const
{
  return Printer::getPrinter(d_options[options::outputLanguage]);
}

OutputManager& SmtEngine::getOutputManager() { return d_outMgr; }

}/* CVC4 namespace */
