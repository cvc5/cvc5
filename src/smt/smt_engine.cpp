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
#include "proof/proof_manager.h"
#include "proof/unsat_core.h"
#include "smt/abduction_solver.h"
#include "smt/abstract_values.h"
#include "smt/assertions.h"
#include "smt/command.h"
#include "smt/defined_function.h"
#include "smt/dump_manager.h"
#include "smt/expr_names.h"
#include "smt/listeners.h"
#include "smt/logic_request.h"
#include "smt/model_blocker.h"
#include "smt/model_core_builder.h"
#include "smt/options_manager.h"
#include "smt/preprocessor.h"
#include "smt/quant_elim_solver.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_engine_state.h"
#include "smt/smt_engine_stats.h"
#include "smt/smt_solver.h"
#include "smt/sygus_solver.h"
#include "smt/term_formula_removal.h"
#include "smt/update_ostream.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/nary_builder.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/logic_info.h"
#include "theory/rewriter.h"
#include "theory/sort_inference.h"
#include "theory/strings/theory_strings.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "theory/theory_traits.h"
#include "util/hash.h"
#include "util/random.h"
#include "util/resource_manager.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {

namespace smt {

}/* namespace CVC4::smt */

SmtEngine::SmtEngine(ExprManager* em, Options* optr)
    : d_state(new SmtEngineState(*this)),
      d_exprManager(em),
      d_nodeManager(d_exprManager->getNodeManager()),
      d_absValues(new AbstractValues(d_nodeManager)),
      d_asserts(new Assertions(getUserContext(), *d_absValues.get())),
      d_exprNames(new ExprNames(getUserContext())),
      d_dumpm(new DumpManager(getUserContext())),
      d_routListener(new ResourceOutListener(*this)),
      d_snmListener(new SmtNodeManagerListener(*d_dumpm.get())),
      d_smtSolver(nullptr),
      d_proofManager(nullptr),
      d_rewriter(new theory::Rewriter()),
      d_definedFunctions(nullptr),
      d_sygusSolver(nullptr),
      d_abductSolver(nullptr),
      d_quantElimSolver(nullptr),
      d_assignments(nullptr),
      d_logic(),
      d_originalOptions(),
      d_isInternalSubsolver(false),
      d_statisticsRegistry(nullptr),
      d_stats(nullptr),
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
  d_pp.reset(
      new smt::Preprocessor(*this, getUserContext(), *d_absValues.get()));
  // listen to node manager events
  d_nodeManager->subscribeEvents(d_snmListener.get());
  // listen to resource out
  d_resourceManager->registerListener(d_routListener.get());
  // make statistics
  d_stats.reset(new SmtEngineStatistics());
  // make the SMT solver
  d_smtSolver.reset(
      new SmtSolver(*this, *d_state, d_resourceManager.get(), *d_pp, *d_stats));
  // make the SyGuS solver
  d_sygusSolver.reset(new SygusSolver(*d_smtSolver, *d_pp, getUserContext()));
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

  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  d_smtSolver->finishInit(const_cast<const LogicInfo&>(d_logic));

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

    if(d_assignments != NULL) {
      d_assignments->deleteSelf();
    }

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

    d_absValues.reset(nullptr);
    d_asserts.reset(nullptr);
    d_exprNames.reset(nullptr);
    d_dumpm.reset(nullptr);

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
    d_state->notifyExpectedStatus(s);
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
    Result status = d_state->getStatus();
    switch (status.asSatisfiabilityResult().isSat())
    {
      case Result::SAT: return SExpr(SExpr::Keyword("sat"));
      case Result::UNSAT: return SExpr(SExpr::Keyword("unsat"));
      default: return SExpr(SExpr::Keyword("unknown"));
    }
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

  for (const Expr& formal : formals)
  {
    nFormals.push_back(formal.getNode());
  }

  DefineFunctionNodeCommand nc(
      ss.str(), func.getNode(), nFormals, formula.getNode());
  d_dumpm->addToModelCommandAndDump(
      nc, ExprManager::VAR_FLAG_DEFINED, true, "declarations");

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
    Node lemn = Node::fromExpr(lem);
    // add define recursive definition to the assertions
    d_asserts->addDefineFunRecDefinition(lemn, global);
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

Result SmtEngine::quickCheck() {
  Assert(d_state->isFullyInited());
  Trace("smt") << "SMT quickCheck()" << endl;
  const std::string& filename = d_state->getFilename();
  return Result(
      Result::ENTAILMENT_UNKNOWN, Result::REQUIRES_FULL_CHECK, filename);
}

theory::TheoryModel* SmtEngine::getAvailableModel(const char* c) const
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

  return m;
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

Result SmtEngine::checkSat(const Expr& assumption, bool inUnsatCore)
{
  Dump("benchmark") << CheckSatCommand(assumption);
  std::vector<Node> assump;
  if (!assumption.isNull())
  {
    assump.push_back(Node::fromExpr(assumption));
  }
  return checkSatInternal(assump, inUnsatCore, false);
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
  std::vector<Node> assumps;
  for (const Expr& e : assumptions)
  {
    assumps.push_back(Node::fromExpr(e));
  }
  return checkSatInternal(assumps, inUnsatCore, false);
}

Result SmtEngine::checkEntailed(const Expr& node, bool inUnsatCore)
{
  Dump("benchmark") << QueryCommand(node, inUnsatCore);
  return checkSatInternal(node.isNull()
                              ? std::vector<Node>()
                              : std::vector<Node>{Node::fromExpr(node)},
                          inUnsatCore,
                          true)
      .asEntailmentResult();
}

Result SmtEngine::checkEntailed(const vector<Expr>& nodes, bool inUnsatCore)
{
  std::vector<Node> ns;
  for (const Expr& e : nodes)
  {
    ns.push_back(Node::fromExpr(e));
  }
  return checkSatInternal(ns, inUnsatCore, true).asEntailmentResult();
}

Result SmtEngine::checkSatInternal(const vector<Node>& assumptions,
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
    Dump("benchmark") << GetUnsatAssumptionsCommand();
  }
  UnsatCore core = getUnsatCoreInternal();
  std::vector<Node> res;
  std::vector<Node>& assumps = d_asserts->getAssumptions();
  for (const Node& e : assumps)
  {
    if (std::find(core.begin(), core.end(), e.toExpr()) != core.end())
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
    Dump("raw-benchmark") << AssertCommand(formula.toExpr());
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

void SmtEngine::declareSygusVar(const std::string& id, Node var, TypeNode type)
{
  SmtScope smts(this);
  finishInit();
  d_sygusSolver->declareSygusVar(id, var, type);
  Dump("raw-benchmark") << DeclareSygusVarCommand(
      id, var.toExpr(), type.toType());
  // don't need to set that the conjecture is stale
}

void SmtEngine::declareSynthFun(const std::string& id,
                                Node func,
                                TypeNode sygusType,
                                bool isInv,
                                const std::vector<Node>& vars)
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  d_sygusSolver->declareSynthFun(id, func, sygusType, isInv, vars);

  // !!! TEMPORARY: We cannot construct a SynthFunCommand since we cannot
  // construct a Term-level Grammar from a Node-level sygus TypeNode. Thus we
  // must print the command using the Node-level utility method for now.

  if (Dump.isOn("raw-benchmark"))
  {
    std::stringstream ss;

    Printer::getPrinter(options::outputLanguage())
        ->toStreamCmdSynthFun(ss,
                              id,
                              vars,
                              func.getType().isFunction()
                                  ? func.getType().getRangeType()
                                  : func.getType(),
                              isInv,
                              sygusType);

    // must print it on the standard output channel since it is not possible
    // to print anything except for commands with Dump.
    std::ostream& out = *d_options.getOut();
    out << ss.str() << std::endl;
  }
}

void SmtEngine::assertSygusConstraint(Node constraint)
{
  SmtScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusConstraint(constraint);
  Dump("raw-benchmark") << SygusConstraintCommand(constraint.toExpr());
}

void SmtEngine::assertSygusInvConstraint(Node inv,
                                         Node pre,
                                         Node trans,
                                         Node post)
{
  SmtScope smts(this);
  finishInit();
  d_sygusSolver->assertSygusInvConstraint(inv, pre, trans, post);
  Dump("raw-benchmark") << SygusInvConstraintCommand(
      inv.toExpr(), pre.toExpr(), trans.toExpr(), post.toExpr());
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

Node SmtEngine::expandDefinitions(const Node& ex)
{
  d_resourceManager->spendResource(ResourceManager::Resource::PreprocessStep);

  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  // set expandOnly flag to true
  return d_pp->expandDefinitions(ex, true);
}

// TODO(#1108): Simplify the error reporting of this method.
Node SmtEngine::getValue(const Node& ex) const
{
  SmtScope smts(this);

  Trace("smt") << "SMT getValue(" << ex << ")" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetValueCommand(ex.toExpr());
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
  TheoryModel* m = getAvailableModel("get-value");
  Node resultNode;
  if(m != NULL) {
    resultNode = m->getValue(n);
  }
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

vector<Expr> SmtEngine::getValues(const vector<Expr>& exprs)
{
  vector<Expr> result;
  for (const Expr& e : exprs)
  {
    result.push_back(getValue(e).toExpr());
  }
  return result;
}

bool SmtEngine::addToAssignment(const Expr& ex) {
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
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
  finishInit();
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
      std::unordered_map<Node, Node, NodeHashFunction> cache;
      Node n = d_pp->expandDefinitions(as, cache);
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

  finishInit();

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetModelCommand();
  }

  TheoryModel* m = getAvailableModel("get model");

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
    std::vector<Expr> eassertsProc = getExpandedAssertions();
    ModelCoreBuilder::setModelCore(eassertsProc, m, options::modelCoresMode());
  }
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

  finishInit();

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
    Node eae = d_pp->expandDefinitions(ea, cache);
    eassertsProc.push_back(eae.toExpr());
  }
  return eassertsProc;
}

Expr SmtEngine::getSepHeapExpr() { return getSepHeapAndNilExpr().first; }

Expr SmtEngine::getSepNilExpr() { return getSepHeapAndNilExpr().second; }

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

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions (size == " << core.size() << ")" << endl;
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Node assertionAfterExpansion = expandDefinitions(Node::fromExpr(*i));
    Notice() << "SmtEngine::checkUnsatCore(): pushing core member " << *i
             << ", expanded to " << assertionAfterExpansion << "\n";
    coreChecker.assertFormula(assertionAfterExpansion);
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
  context::CDList<Node>* al = d_asserts->getAssertionList();
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(al != nullptr)
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
    TheoryEngine* te = getTheoryEngine();
    Assert(te != nullptr);
    te->checkTheoryAssertionsWithModel(hardFailure);
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
  for (const Node& assertion : *al)
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
      n = d_pp->expandDefinitions(n, cache);
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

    // Simplify the result and replace the already-known ITEs (this is important
    // for ground ITEs under quantifiers).
    n = d_pp->simplify(n, true);
    Notice()
        << "SmtEngine::checkModel(): -- simplifies with ite replacement to  "
        << n << endl;

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

void SmtEngine::checkInterpol(Expr interpol,
                              const std::vector<Expr>& easserts,
                              const Node& conj)
{
}

// TODO(#1108): Simplify the error reporting of this method.
UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << endl;
  SmtScope smts(this);
  finishInit();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetUnsatCoreCommand();
  }
  return getUnsatCoreInternal();
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
  te->printInstantiations(out);
  if (options::instFormatMode() == options::InstFormatMode::SZS)
  {
    out << "% SZS output end Proof for " << d_state->getFilename() << std::endl;
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
  return d_quantElimSolver->getQuantifierElimination(*d_asserts, q, doFull);
}

bool SmtEngine::getInterpol(const Node& conj,
                            const TypeNode& grammarType,
                            Node& interpol)
{
  return false;
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

void SmtEngine::getInstantiatedQuantifiedFormulas( std::vector< Expr >& qs ) {
  SmtScope smts(this);
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  std::vector<Node> qs_n;
  te->getInstantiatedQuantifiedFormulas(qs_n);
  for (std::size_t i = 0, n = qs_n.size(); i < n; i++)
  {
    qs.push_back(qs_n[i].toExpr());
  }
}

void SmtEngine::getInstantiations( Expr q, std::vector< Expr >& insts ) {
  SmtScope smts(this);
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  std::vector<Node> insts_n;
  te->getInstantiations(Node::fromExpr(q), insts_n);
  for (std::size_t i = 0, n = insts_n.size(); i < n; i++)
  {
    insts.push_back(insts_n[i].toExpr());
  }
}

void SmtEngine::getInstantiationTermVectors( Expr q, std::vector< std::vector< Expr > >& tvecs ) {
  SmtScope smts(this);
  Assert(options::trackInstLemmas());
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  std::vector<std::vector<Node>> tvecs_n;
  te->getInstantiationTermVectors(Node::fromExpr(q), tvecs_n);
  for (std::size_t i = 0, n = tvecs_n.size(); i < n; i++)
  {
    std::vector<Expr> tvec;
    for (std::size_t j = 0, m = tvecs_n[i].size(); j < m; j++)
    {
      tvec.push_back(tvecs_n[i][j].toExpr());
    }
    tvecs.push_back(tvec);
  }
}

std::vector<Expr> SmtEngine::getAssertions()
{
  SmtScope smts(this);
  finishInit();
  d_state->doPendingPops();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssertionsCommand();
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!options::produceAssertions()) {
    const char* msg =
      "Cannot query the current assertion list when not in produce-assertions mode.";
    throw ModalException(msg);
  }
  context::CDList<Node>* al = d_asserts->getAssertionList();
  Assert(al != nullptr);
  std::vector<Expr> res;
  for (const Node& n : *al)
  {
    res.emplace_back(n.toExpr());
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
    Dump("benchmark") << PushCommand();
  }
  d_state->userPush();
}

void SmtEngine::pop() {
  SmtScope smts(this);
  finishInit();
  Trace("smt") << "SMT pop()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << PopCommand();
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
  ExprManager *em = d_exprManager;
  Trace("smt") << "SMT reset()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ResetCommand();
  }
  std::string filename = d_state->getFilename();
  Options opts;
  opts.copyValues(d_originalOptions);
  this->~SmtEngine();
  new (this) SmtEngine(em, &opts);
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
    Dump("benchmark") << ResetAssertionsCommand();
  }

  d_state->notifyResetAssertions();
  d_dumpm->resetAssertions();
  // push the state to maintain global context around everything
  d_state->setup();

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
  finishInit();
  std::vector<Node> node_values;
  for (std::size_t i = 0, n = expr_values.size(); i < n; i++)
  {
    node_values.push_back( expr_values[i].getNode() );
  }
  TheoryEngine* te = getTheoryEngine();
  Assert(te != nullptr);
  te->setUserAttribute(attr, expr.getNode(), node_values, str_value);
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

}/* CVC4 namespace */
