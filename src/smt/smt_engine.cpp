/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include <unordered_map>
#include <unordered_set>
#include <iterator>
#include <sstream>
#include <stack>
#include <string>
#include <utility>
#include <vector>

#include "base/configuration.h"
#include "base/configuration_private.h"
#include "base/exception.h"
#include "base/listener.h"
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
#include "expr/node_builder.h"
#include "expr/node_self_iterator.h"
#include "options/arith_options.h"
#include "options/arrays_options.h"
#include "options/base_options.h"
#include "options/booleans_options.h"
#include "options/bv_options.h"
#include "options/datatypes_options.h"
#include "options/decision_mode.h"
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
#include "smt/command.h"
#include "smt/command_list.h"
#include "smt/logic_request.h"
#include "smt/managed_ostreams.h"
#include "smt/smt_engine_scope.h"
#include "smt/term_formula_removal.h"
#include "smt/update_ostream.h"
#include "smt_util/boolean_simplification.h"
#include "smt_util/nary_builder.h"
#include "smt_util/node_visitor.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/bv/bvgauss.h"
#include "theory/bv/bvintropow2.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"
#include "theory/quantifiers/fun_def_process.h"
#include "theory/quantifiers/global_negate.h"
#include "theory/quantifiers/macros.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/single_inv_partition.h"
#include "theory/quantifiers/term_util.h"
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

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::preprocessing;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {
namespace smt {

struct DeleteCommandFunction : public std::unary_function<const Command*, void>
{
  void operator()(const Command* command) { delete command; }
};

void DeleteAndClearCommandVector(std::vector<Command*>& commands) {
  std::for_each(commands.begin(), commands.end(), DeleteCommandFunction());
  commands.clear();
}

/** Useful for counting the number of recursive calls. */
class ScopeCounter {
private:
  unsigned& d_depth;
public:
  ScopeCounter(unsigned& d) : d_depth(d) {
    ++d_depth;
  }
  ~ScopeCounter(){
    --d_depth;
  }
};

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

struct SmtEngineStatistics {
  /** time spent in gaussian elimination */
  TimerStat d_gaussElimTime;
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** time spent in non-clausal simplification */
  TimerStat d_nonclausalSimplificationTime;
  /** time spent in miplib pass */
  TimerStat d_miplibPassTime;
  /** number of assertions removed by miplib pass */
  IntStat d_numMiplibAssertionsRemoved;
  /** number of constant propagations found during nonclausal simp */
  IntStat d_numConstantProps;
  /** time spent in static learning */
  TimerStat d_staticLearningTime;
  /** time spent in simplifying ITEs */
  TimerStat d_simpITETime;
  /** time spent in simplifying ITEs */
  TimerStat d_unconstrainedSimpTime;
  /** time spent removing ITEs */
  TimerStat d_iteRemovalTime;
  /** time spent in theory preprocessing */
  TimerStat d_theoryPreprocessTime;
  /** time spent in theory preprocessing */
  TimerStat d_rewriteApplyToConstTime;
  /** time spent converting to CNF */
  TimerStat d_cnfConversionTime;
  /** Num of assertions before ite removal */
  IntStat d_numAssertionsPre;
  /** Num of assertions after ite removal */
  IntStat d_numAssertionsPost;
  /** time spent in checkModel() */
  TimerStat d_checkModelTime;
  /** time spent in checkProof() */
  TimerStat d_checkProofTime;
  /** time spent in checkUnsatCore() */
  TimerStat d_checkUnsatCoreTime;
  /** time spent in PropEngine::checkSat() */
  TimerStat d_solveTime;
  /** time spent in pushing/popping */
  TimerStat d_pushPopTime;
  /** time spent in processAssertions() */
  TimerStat d_processAssertionsTime;

  /** Has something simplified to false? */
  IntStat d_simplifiedToFalse;
  /** Number of resource units spent. */
  ReferenceStat<uint64_t> d_resourceUnitsUsed;

  SmtEngineStatistics() :
    d_gaussElimTime("smt::SmtEngine::gaussElimTime"),
    d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
    d_nonclausalSimplificationTime("smt::SmtEngine::nonclausalSimplificationTime"),
    d_miplibPassTime("smt::SmtEngine::miplibPassTime"),
    d_numMiplibAssertionsRemoved("smt::SmtEngine::numMiplibAssertionsRemoved", 0),
    d_numConstantProps("smt::SmtEngine::numConstantProps", 0),
    d_staticLearningTime("smt::SmtEngine::staticLearningTime"),
    d_simpITETime("smt::SmtEngine::simpITETime"),
    d_unconstrainedSimpTime("smt::SmtEngine::unconstrainedSimpTime"),
    d_iteRemovalTime("smt::SmtEngine::iteRemovalTime"),
    d_theoryPreprocessTime("smt::SmtEngine::theoryPreprocessTime"),
    d_rewriteApplyToConstTime("smt::SmtEngine::rewriteApplyToConstTime"),
    d_cnfConversionTime("smt::SmtEngine::cnfConversionTime"),
    d_numAssertionsPre("smt::SmtEngine::numAssertionsPreITERemoval", 0),
    d_numAssertionsPost("smt::SmtEngine::numAssertionsPostITERemoval", 0),
    d_checkModelTime("smt::SmtEngine::checkModelTime"),
    d_checkProofTime("smt::SmtEngine::checkProofTime"),
    d_checkUnsatCoreTime("smt::SmtEngine::checkUnsatCoreTime"),
    d_solveTime("smt::SmtEngine::solveTime"),
    d_pushPopTime("smt::SmtEngine::pushPopTime"),
    d_processAssertionsTime("smt::SmtEngine::processAssertionsTime"),
    d_simplifiedToFalse("smt::SmtEngine::simplifiedToFalse", 0),
    d_resourceUnitsUsed("smt::SmtEngine::resourceUnitsUsed")
 {

    smtStatisticsRegistry()->registerStat(&d_gaussElimTime);
    smtStatisticsRegistry()->registerStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->registerStat(&d_nonclausalSimplificationTime);
    smtStatisticsRegistry()->registerStat(&d_miplibPassTime);
    smtStatisticsRegistry()->registerStat(&d_numMiplibAssertionsRemoved);
    smtStatisticsRegistry()->registerStat(&d_numConstantProps);
    smtStatisticsRegistry()->registerStat(&d_staticLearningTime);
    smtStatisticsRegistry()->registerStat(&d_simpITETime);
    smtStatisticsRegistry()->registerStat(&d_unconstrainedSimpTime);
    smtStatisticsRegistry()->registerStat(&d_iteRemovalTime);
    smtStatisticsRegistry()->registerStat(&d_theoryPreprocessTime);
    smtStatisticsRegistry()->registerStat(&d_rewriteApplyToConstTime);
    smtStatisticsRegistry()->registerStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->registerStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->registerStat(&d_checkModelTime);
    smtStatisticsRegistry()->registerStat(&d_checkProofTime);
    smtStatisticsRegistry()->registerStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->registerStat(&d_solveTime);
    smtStatisticsRegistry()->registerStat(&d_pushPopTime);
    smtStatisticsRegistry()->registerStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->registerStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->registerStat(&d_resourceUnitsUsed);
  }

  ~SmtEngineStatistics() {
    smtStatisticsRegistry()->unregisterStat(&d_gaussElimTime);
    smtStatisticsRegistry()->unregisterStat(&d_definitionExpansionTime);
    smtStatisticsRegistry()->unregisterStat(&d_nonclausalSimplificationTime);
    smtStatisticsRegistry()->unregisterStat(&d_miplibPassTime);
    smtStatisticsRegistry()->unregisterStat(&d_numMiplibAssertionsRemoved);
    smtStatisticsRegistry()->unregisterStat(&d_numConstantProps);
    smtStatisticsRegistry()->unregisterStat(&d_staticLearningTime);
    smtStatisticsRegistry()->unregisterStat(&d_simpITETime);
    smtStatisticsRegistry()->unregisterStat(&d_unconstrainedSimpTime);
    smtStatisticsRegistry()->unregisterStat(&d_iteRemovalTime);
    smtStatisticsRegistry()->unregisterStat(&d_theoryPreprocessTime);
    smtStatisticsRegistry()->unregisterStat(&d_rewriteApplyToConstTime);
    smtStatisticsRegistry()->unregisterStat(&d_cnfConversionTime);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPre);
    smtStatisticsRegistry()->unregisterStat(&d_numAssertionsPost);
    smtStatisticsRegistry()->unregisterStat(&d_checkModelTime);
    smtStatisticsRegistry()->unregisterStat(&d_checkProofTime);
    smtStatisticsRegistry()->unregisterStat(&d_checkUnsatCoreTime);
    smtStatisticsRegistry()->unregisterStat(&d_solveTime);
    smtStatisticsRegistry()->unregisterStat(&d_pushPopTime);
    smtStatisticsRegistry()->unregisterStat(&d_processAssertionsTime);
    smtStatisticsRegistry()->unregisterStat(&d_simplifiedToFalse);
    smtStatisticsRegistry()->unregisterStat(&d_resourceUnitsUsed);
  }
};/* struct SmtEngineStatistics */


class SoftResourceOutListener : public Listener {
 public:
  SoftResourceOutListener(SmtEngine& smt) : d_smt(&smt) {}
  virtual void notify() {
    SmtScope scope(d_smt);
    Assert(smt::smtEngineInScope());
    d_smt->interrupt();
  }
 private:
  SmtEngine* d_smt;
}; /* class SoftResourceOutListener */


class HardResourceOutListener : public Listener {
 public:
  HardResourceOutListener(SmtEngine& smt) : d_smt(&smt) {}
  virtual void notify() {
    SmtScope scope(d_smt);
    theory::Rewriter::clearCaches();
  }
 private:
  SmtEngine* d_smt;
}; /* class HardResourceOutListener */

class SetLogicListener : public Listener {
 public:
  SetLogicListener(SmtEngine& smt) : d_smt(&smt) {}
  virtual void notify() {
    LogicInfo inOptions(options::forceLogicString());
    d_smt->setLogic(inOptions);
  }
 private:
  SmtEngine* d_smt;
}; /* class SetLogicListener */

class BeforeSearchListener : public Listener {
 public:
  BeforeSearchListener(SmtEngine& smt) : d_smt(&smt) {}
  virtual void notify() {
    d_smt->beforeSearch();
  }
 private:
  SmtEngine* d_smt;
}; /* class BeforeSearchListener */

class UseTheoryListListener : public Listener {
 public:
  UseTheoryListListener(TheoryEngine* theoryEngine)
      : d_theoryEngine(theoryEngine)
  {}

  void notify() {
    std::stringstream commaList(options::useTheoryList());
    std::string token;

    Debug("UseTheoryListListener") << "UseTheoryListListener::notify() "
                                   << options::useTheoryList() << std::endl;

    while(std::getline(commaList, token, ',')){
      if(token == "help") {
        puts(theory::useTheoryHelp);
        exit(1);
      }
      if(theory::useTheoryValidate(token)) {
        d_theoryEngine->enableTheoryAlternative(token);
      } else {
        throw OptionException(
            std::string("unknown option for --use-theory : `") + token +
            "'.  Try --use-theory=help.");
      }
    }
  }

 private:
  TheoryEngine* d_theoryEngine;
}; /* class UseTheoryListListener */


class SetDefaultExprDepthListener : public Listener {
 public:
  virtual void notify() {
    int depth = options::defaultExprDepth();
    Debug.getStream() << expr::ExprSetDepth(depth);
    Trace.getStream() << expr::ExprSetDepth(depth);
    Notice.getStream() << expr::ExprSetDepth(depth);
    Chat.getStream() << expr::ExprSetDepth(depth);
    Message.getStream() << expr::ExprSetDepth(depth);
    Warning.getStream() << expr::ExprSetDepth(depth);
    // intentionally exclude Dump stream from this list
  }
};

class SetDefaultExprDagListener : public Listener {
 public:
  virtual void notify() {
    int dag = options::defaultDagThresh();
    Debug.getStream() << expr::ExprDag(dag);
    Trace.getStream() << expr::ExprDag(dag);
    Notice.getStream() << expr::ExprDag(dag);
    Chat.getStream() << expr::ExprDag(dag);
    Message.getStream() << expr::ExprDag(dag);
    Warning.getStream() << expr::ExprDag(dag);
    Dump.getStream() << expr::ExprDag(dag);
  }
};

class SetPrintExprTypesListener : public Listener {
 public:
  virtual void notify() {
    bool value = options::printExprTypes();
    Debug.getStream() << expr::ExprPrintTypes(value);
    Trace.getStream() << expr::ExprPrintTypes(value);
    Notice.getStream() << expr::ExprPrintTypes(value);
    Chat.getStream() << expr::ExprPrintTypes(value);
    Message.getStream() << expr::ExprPrintTypes(value);
    Warning.getStream() << expr::ExprPrintTypes(value);
    // intentionally exclude Dump stream from this list
  }
};

class DumpModeListener : public Listener {
 public:
  virtual void notify() {
    const std::string& value = options::dumpModeString();
    Dump.setDumpFromString(value);
  }
};

class PrintSuccessListener : public Listener {
 public:
  virtual void notify() {
    bool value = options::printSuccess();
    Debug.getStream() << Command::printsuccess(value);
    Trace.getStream() << Command::printsuccess(value);
    Notice.getStream() << Command::printsuccess(value);
    Chat.getStream() << Command::printsuccess(value);
    Message.getStream() << Command::printsuccess(value);
    Warning.getStream() << Command::printsuccess(value);
    *options::out() << Command::printsuccess(value);
  }
};



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
class SmtEnginePrivate : public NodeManagerListener {
  SmtEngine& d_smt;

  typedef unordered_map<Node, Node, NodeHashFunction> NodeToNodeHashMap;
  typedef unordered_map<Node, bool, NodeHashFunction> NodeToBoolHashMap;

  /**
   * Manager for limiting time and abstract resource usage.
   */
  ResourceManager* d_resourceManager;

  /** Manager for the memory of regular-output-channel. */
  ManagedRegularOutputChannel d_managedRegularChannel;

  /** Manager for the memory of diagnostic-output-channel. */
  ManagedDiagnosticOutputChannel d_managedDiagnosticChannel;

  /** Manager for the memory of --dump-to. */
  ManagedDumpOStream d_managedDumpChannel;

  /** Manager for --replay-log. */
  ManagedReplayLogOstream d_managedReplayLog;

  /**
   * This list contains:
   *  softResourceOut
   *  hardResourceOut
   *  setForceLogic
   *  beforeSearchListener
   *  UseTheoryListListener
   *
   * This needs to be deleted before both NodeManager's Options,
   * SmtEngine, d_resourceManager, and TheoryEngine.
   */
  ListenerRegistrationList* d_listenerRegistrations;

  /** Learned literals */
  vector<Node> d_nonClausalLearnedLiterals;

  /** Size of assertions array when preprocessing starts */
  unsigned d_realAssertionsEnd;

  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;
  bool d_propagatorNeedsFinish;
  std::vector<Node> d_boolVars;

  /** Assertions in the preprocessing pipeline */
  AssertionPipeline d_assertions;

  /** Whether any assertions have been processed */
  CDO<bool> d_assertionsProcessed;

  /** Index for where to store substitutions */
  CDO<unsigned> d_substitutionsIndex;

  // Cached true value
  Node d_true;

  /**
   * A context that never pushes/pops, for use by CD structures (like
   * SubstitutionMaps) that should be "global".
   */
  context::Context d_fakeContext;

  /**
   * A map of AbsractValues to their actual constants.  Only used if
   * options::abstractValues() is on.
   */
  SubstitutionMap d_abstractValueMap;

  /**
   * A mapping of all abstract values (actual value |-> abstract) that
   * we've handed out.  This is necessary to ensure that we give the
   * same AbstractValues for the same real constants.  Only used if
   * options::abstractValues() is on.
   */
  NodeToNodeHashMap d_abstractValues;

  /** Number of calls of simplify assertions active.
   */
  unsigned d_simplifyAssertionsDepth;

  /** TODO: whether certain preprocess steps are necessary */
  //bool d_needsExpandDefs;
  
  //------------------------------- expression names
  /** mapping from expressions to name */
  context::CDHashMap< Node, std::string, NodeHashFunction > d_exprNames;
  //------------------------------- end expression names
public:
  /**
   * Map from skolem variables to index in d_assertions containing
   * corresponding introduced Boolean ite
   */
  IteSkolemMap d_iteSkolemMap;

  /** Instance of the ITE remover */
  RemoveTermFormulas d_iteRemover;

  /* Finishes the initialization of the private portion of SMTEngine. */
  void finishInit();

 private:
  std::unique_ptr<PreprocessingPassContext> d_preprocessingPassContext;
  PreprocessingPassRegistry d_preprocessingPassRegistry;
  theory::arith::PseudoBooleanProcessor d_pbsProcessor;

  /** The top level substitutions */
  SubstitutionMap d_topLevelSubstitutions;

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

  Node realToInt(TNode n, NodeToNodeHashMap& cache, std::vector< Node >& var_eq);
  Node intToBV(TNode n, NodeToNodeHashMap& cache);
  Node intToBVMakeBinary(TNode n, NodeToNodeHashMap& cache);
  Node purifyNlTerms(TNode n, NodeToNodeHashMap& cache, NodeToNodeHashMap& bcache, std::vector< Node >& var_eq, bool beneathMult = false);

  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  void collectSkolems(TNode n, set<TNode>& skolemSet, NodeToBoolHashMap& cache);

  /**
   * Helper function to fix up assertion list to restore invariants needed after
   * ite removal.
   */
  bool checkForBadSkolems(TNode n, TNode skolem, NodeToBoolHashMap& cache);

  // Lift bit-vectors of size 1 to booleans
  void bvToBool();

  // Convert booleans to bit-vectors of size 1
  void boolToBv();

  // Abstract common structure over small domains to UF
  // return true if changes were made.
  void bvAbstraction();

  // Simplify ITE structure
  bool simpITE();

  // Simplify based on unconstrained values
  void unconstrainedSimp();

  /**
   * Ensures the assertions asserted after before now effectively come before
   * d_realAssertionsEnd.
   */
  void compressBeforeRealAssertions(size_t before);

  /**
   * Trace nodes back to their assertions using CircuitPropagator's
   * BackEdgesMap.
   */
  void traceBackToAssertions(const std::vector<Node>& nodes,
                             std::vector<TNode>& assertions);

  /**
   * Remove conjuncts in toRemove from conjunction n. Return # of removed
   * conjuncts.
   */
  size_t removeFromConjunction(Node& n,
                               const std::unordered_set<unsigned long>& toRemove);

  /** Scrub miplib encodings. */
  void doMiplibTrick();

  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions();

 public:

  SmtEnginePrivate(SmtEngine& smt) :
    d_smt(smt),
    d_managedRegularChannel(),
    d_managedDiagnosticChannel(),
    d_managedDumpChannel(),
    d_managedReplayLog(),
    d_listenerRegistrations(new ListenerRegistrationList()),
    d_nonClausalLearnedLiterals(),
    d_realAssertionsEnd(0),
    d_propagator(d_nonClausalLearnedLiterals, true, true),
    d_propagatorNeedsFinish(false),
    d_assertions(),
    d_assertionsProcessed(smt.d_userContext, false),
    d_substitutionsIndex(smt.d_userContext, 0),
    d_fakeContext(),
    d_abstractValueMap(&d_fakeContext),
    d_abstractValues(),
    d_simplifyAssertionsDepth(0),
    //d_needsExpandDefs(true),  //TODO?
    d_exprNames(smt.d_userContext),
    d_iteSkolemMap(),
    d_iteRemover(smt.d_userContext),
    d_pbsProcessor(smt.d_userContext),
    d_topLevelSubstitutions(smt.d_userContext)
  {
    d_smt.d_nodeManager->subscribeEvents(this);
    d_true = NodeManager::currentNM()->mkConst(true);
    d_resourceManager = NodeManager::currentResourceManager();

    d_listenerRegistrations->add(d_resourceManager->registerSoftListener(
        new SoftResourceOutListener(d_smt)));

    d_listenerRegistrations->add(d_resourceManager->registerHardListener(
        new HardResourceOutListener(d_smt)));

    Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
    d_listenerRegistrations->add(
        nodeManagerOptions.registerForceLogicListener(
            new SetLogicListener(d_smt), true));

    // Multiple options reuse BeforeSearchListener so registration requires an
    // extra bit of care.
    // We can safely not call notify on this before search listener at
    // registration time. This d_smt cannot be beforeSearch at construction
    // time. Therefore the BeforeSearchListener is a no-op. Therefore it does
    // not have to be called.
    d_listenerRegistrations->add(
        nodeManagerOptions.registerBeforeSearchListener(
            new BeforeSearchListener(d_smt)));

    // These do need registration calls.
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDefaultExprDepthListener(
            new SetDefaultExprDepthListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDefaultExprDagListener(
            new SetDefaultExprDagListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetPrintExprTypesListener(
            new SetPrintExprTypesListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDumpModeListener(
            new DumpModeListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetPrintSuccessListener(
            new PrintSuccessListener(), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetRegularOutputChannelListener(
            new SetToDefaultSourceListener(&d_managedRegularChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetDiagnosticOutputChannelListener(
            new SetToDefaultSourceListener(&d_managedDiagnosticChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerDumpToFileNameListener(
            new SetToDefaultSourceListener(&d_managedDumpChannel), true));
    d_listenerRegistrations->add(
        nodeManagerOptions.registerSetReplayLogFilename(
            new SetToDefaultSourceListener(&d_managedReplayLog), true));
  }

  ~SmtEnginePrivate()
  {
    delete d_listenerRegistrations;

    if(d_propagatorNeedsFinish) {
      d_propagator.finish();
      d_propagatorNeedsFinish = false;
    }
    d_smt.d_nodeManager->unsubscribeEvents(this);
  }

  ResourceManager* getResourceManager() { return d_resourceManager; }
  void spendResource(unsigned amount)
  {
    d_resourceManager->spendResource(amount);
  }

  void nmNotifyNewSort(TypeNode tn, uint32_t flags) {
    DeclareTypeCommand c(tn.getAttribute(expr::VarNameAttr()),
                         0,
                         tn.toType());
    if((flags & ExprManager::SORT_FLAG_PLACEHOLDER) == 0) {
      d_smt.addToModelCommandAndDump(c, flags);
    }
  }

  void nmNotifyNewSortConstructor(TypeNode tn) {
    DeclareTypeCommand c(tn.getAttribute(expr::VarNameAttr()),
                         tn.getAttribute(expr::SortArityAttr()),
                         tn.toType());
    d_smt.addToModelCommandAndDump(c);
  }

  void nmNotifyNewDatatypes(const std::vector<DatatypeType>& dtts) {
    DatatypeDeclarationCommand c(dtts);
    d_smt.addToModelCommandAndDump(c);
  }

  void nmNotifyNewVar(TNode n, uint32_t flags) {
    DeclareFunctionCommand c(n.getAttribute(expr::VarNameAttr()),
                             n.toExpr(),
                             n.getType().toType());
    if((flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
      d_smt.addToModelCommandAndDump(c, flags);
    }
    if(n.getType().isBoolean() && !options::incrementalSolving()) {
      d_boolVars.push_back(n);
    }
  }

  void nmNotifyNewSkolem(TNode n, const std::string& comment, uint32_t flags) {
    string id = n.getAttribute(expr::VarNameAttr());
    DeclareFunctionCommand c(id,
                             n.toExpr(),
                             n.getType().toType());
    if(Dump.isOn("skolems") && comment != "") {
      Dump("skolems") << CommentCommand(id + " is " + comment);
    }
    if((flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
      d_smt.addToModelCommandAndDump(c, flags, false, "skolems");
    }
    if(n.getType().isBoolean() && !options::incrementalSolving()) {
      d_boolVars.push_back(n);
    }
  }

  void nmNotifyDeleteNode(TNode n) {}

  Node applySubstitutions(TNode node) const {
    return Rewriter::rewrite(d_topLevelSubstitutions.apply(node));
  }

  /**
   * Apply the substitutions in d_topLevelAssertions and the rewriter to each of
   * the assertions in d_assertions, and store the result back in d_assertions.
   */
  void applySubstitutionsToAssertions();
  
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
    d_nonClausalLearnedLiterals.clear();
    d_realAssertionsEnd = 0;
    d_iteSkolemMap.clear();
  }

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   * the 2nd and 3rd arguments added for bookkeeping for proofs
   */
  void addFormula(TNode n, bool inUnsatCore, bool inInput = true);

  /** Expand definitions in n. */
  Node expandDefinitions(TNode n,
                         NodeToNodeHashMap& cache,
                         bool expandOnly = false);

  /**
   * Simplify node "in" by expanding definitions and applying any
   * substitutions learned from preprocessing.
   */
  Node simplify(TNode in) {
    // Substitute out any abstract values in ex.
    // Expand definitions.
    NodeToNodeHashMap cache;
    Node n = expandDefinitions(in, cache).toExpr();
    // Make sure we've done all preprocessing, etc.
    Assert(d_assertions.size() == 0);
    return applySubstitutions(n).toExpr();
  }

  /**
   * Substitute away all AbstractValues in a node.
   */
  Node substituteAbstractValues(TNode n) {
    // We need to do this even if options::abstractValues() is off,
    // since the setting might have changed after we already gave out
    // some abstract values.
    return d_abstractValueMap.apply(n);
  }

  /**
   * Make a new (or return an existing) abstract value for a node.
   * Can only use this if options::abstractValues() is on.
   */
  Node mkAbstractValue(TNode n) {
    Assert(options::abstractValues());
    Node& val = d_abstractValues[n];
    if(val.isNull()) {
      val = d_smt.d_nodeManager->mkAbstractValue(n.getType());
      d_abstractValueMap.addSubstitution(val, n);
    }
    // We are supposed to ascribe types to all abstract values that go out.
    NodeManager* current = d_smt.d_nodeManager;
    Node ascription = current->mkConst(AscriptionType(n.getType().toType()));
    Node retval = current->mkNode(kind::APPLY_TYPE_ASCRIPTION, ascription, val);
    return retval;
  }

  NodeToNodeHashMap d_rewriteApplyToConstCache;
  Node rewriteApplyToConst(TNode n) {
    Trace("rewriteApplyToConst") << "rewriteApplyToConst :: " << n << std::endl;

    if(n.getMetaKind() == kind::metakind::CONSTANT ||
       n.getMetaKind() == kind::metakind::VARIABLE ||
       n.getMetaKind() == kind::metakind::NULLARY_OPERATOR)
    {
      return n;
    }

    if(d_rewriteApplyToConstCache.find(n) != d_rewriteApplyToConstCache.end()) {
      Trace("rewriteApplyToConst") << "in cache :: "
                                   << d_rewriteApplyToConstCache[n]
                                   << std::endl;
      return d_rewriteApplyToConstCache[n];
    }

    if(n.getKind() == kind::APPLY_UF) {
      if(n.getNumChildren() == 1 && n[0].isConst() &&
         n[0].getType().isInteger())
      {
        stringstream ss;
        ss << n.getOperator() << "_";
        if(n[0].getConst<Rational>() < 0) {
          ss << "m" << -n[0].getConst<Rational>();
        } else {
          ss << n[0];
        }
        Node newvar = NodeManager::currentNM()->mkSkolem(
            ss.str(), n.getType(), "rewriteApplyToConst skolem",
            NodeManager::SKOLEM_EXACT_NAME);
        d_rewriteApplyToConstCache[n] = newvar;
        Trace("rewriteApplyToConst") << "made :: " << newvar << std::endl;
        return newvar;
      } else {
        stringstream ss;
        ss << "The rewrite-apply-to-const preprocessor is currently limited;"
           << std::endl
           << "it only works if all function symbols are unary and with Integer"
           << std::endl
           << "domain, and all applications are to integer values." << std::endl
           << "Found application: " << n;
        Unhandled(ss.str());
      }
    }

    NodeBuilder<> builder(n.getKind());
    if(n.getMetaKind() == kind::metakind::PARAMETERIZED) {
      builder << n.getOperator();
    }
    for(unsigned i = 0; i < n.getNumChildren(); ++i) {
      builder << rewriteApplyToConst(n[i]);
    }
    Node rewr = builder;
    d_rewriteApplyToConstCache[n] = rewr;
    Trace("rewriteApplyToConst") << "built :: " << rewr << std::endl;
    return rewr;
  }

  void addUseTheoryListListener(TheoryEngine* theoryEngine){
    Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
    d_listenerRegistrations->add(
        nodeManagerOptions.registerUseTheoryListListener(
            new UseTheoryListListener(theoryEngine), true));
  }

  std::ostream* getReplayLog() const {
    return d_managedReplayLog.getReplayLog();
  }
  
  //------------------------------- expression names
  // implements setExpressionName, as described in smt_engine.h
  void setExpressionName(Expr e, std::string name) {
    d_exprNames[Node::fromExpr(e)] = name;
  }
  
  // implements getExpressionName, as described in smt_engine.h
  bool getExpressionName(Expr e, std::string& name) const {
    context::CDHashMap< Node, std::string, NodeHashFunction >::const_iterator it = d_exprNames.find(e);
    if(it!=d_exprNames.end()) {
      name = (*it).second;
      return true;
    }else{
      return false;
    }
  }
  //------------------------------- end expression names

};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

SmtEngine::SmtEngine(ExprManager* em)
    : d_context(new Context()),
      d_userLevels(),
      d_userContext(new UserContext()),
      d_exprManager(em),
      d_nodeManager(d_exprManager->getNodeManager()),
      d_decisionEngine(NULL),
      d_theoryEngine(NULL),
      d_propEngine(NULL),
      d_proofManager(NULL),
      d_definedFunctions(NULL),
      d_fmfRecFunctionsDefined(NULL),
      d_assertionList(NULL),
      d_assignments(NULL),
      d_modelGlobalCommands(),
      d_modelCommands(NULL),
      d_dumpCommands(),
      d_defineCommands(),
      d_logic(),
      d_originalOptions(),
      d_pendingPops(0),
      d_fullyInited(false),
      d_problemExtended(false),
      d_queryMade(false),
      d_needPostsolve(false),
      d_earlyTheoryPP(true),
      d_globalNegation(false),
      d_status(),
      d_replayStream(NULL),
      d_private(NULL),
      d_statisticsRegistry(NULL),
      d_stats(NULL),
      d_channels(new LemmaChannels())
{
  SmtScope smts(this);
  d_originalOptions.copyValues(em->getOptions());
  d_private = new smt::SmtEnginePrivate(*this);
  d_statisticsRegistry = new StatisticsRegistry();
  d_stats = new SmtEngineStatistics();
  d_stats->d_resourceUnitsUsed.setData(
      d_private->getResourceManager()->getResourceUsage());

  // The ProofManager is constructed before any other proof objects such as
  // SatProof and TheoryProofs. The TheoryProofEngine and the SatProof are
  // initialized in TheoryEngine and PropEngine respectively.
  Assert(d_proofManager == NULL);

  // d_proofManager must be created before Options has been finished
  // being parsed from the input file. Because of this, we cannot trust
  // that options::proof() is set correctly yet.
#ifdef CVC4_PROOF
  d_proofManager = new ProofManager(d_userContext);
#endif

  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context, d_userContext,
                                    d_private->d_iteRemover,
                                    const_cast<const LogicInfo&>(d_logic),
                                    d_channels);

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(d_theoryEngine, id);
    //register with proof engine if applicable
#ifdef CVC4_PROOF
    ProofManager::currentPM()->getTheoryProofEngine()->registerTheory(d_theoryEngine->theoryOf(id));
#endif
  }

  d_private->addUseTheoryListListener(d_theoryEngine);

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_userContext->push();
  d_context->push();

  d_definedFunctions = new(true) DefinedFunctionMap(d_userContext);
  d_fmfRecFunctionsDefined = new(true) NodeList(d_userContext);
  d_modelCommands = new(true) smt::CommandList(d_userContext);
}

void SmtEngine::finishInit() {
  Trace("smt-debug") << "SmtEngine::finishInit" << std::endl;
  // ensure that our heuristics are properly set up
  setDefaults();

  Trace("smt-debug") << "Making decision engine..." << std::endl;

  d_decisionEngine = new DecisionEngine(d_context, d_userContext);
  d_decisionEngine->init();   // enable appropriate strategies

  Trace("smt-debug") << "Making prop engine..." << std::endl;
  d_propEngine = new PropEngine(d_theoryEngine, d_decisionEngine, d_context,
                                d_userContext, d_private->getReplayLog(),
                                d_replayStream, d_channels);

  Trace("smt-debug") << "Setting up theory engine..." << std::endl;
  d_theoryEngine->setPropEngine(d_propEngine);
  d_theoryEngine->setDecisionEngine(d_decisionEngine);
  Trace("smt-debug") << "Finishing init for theory engine..." << std::endl;
  d_theoryEngine->finishInit();

  Trace("smt-debug") << "Set up assertion list..." << std::endl;
  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(options::produceAssertions() ||
     options::incrementalSolving()) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new(true) AssertionList(d_userContext);
  }

  // dump out a set-logic command
  if(Dump.isOn("benchmark")) {
    if (Dump.isOn("raw-benchmark")) {
      Dump("raw-benchmark") << SetBenchmarkLogicCommand(d_logic.getLogicString());
    } else {
      LogicInfo everything;
      everything.lock();
      Dump("benchmark") << CommentCommand("CVC4 always dumps the most general, all-supported logic (below), as some internals might require the use of a logic more general than the input.")
                        << SetBenchmarkLogicCommand(everything.getLogicString());
    }
  }

  Trace("smt-debug") << "Dump declaration commands..." << std::endl;
  // dump out any pending declaration commands
  for(unsigned i = 0; i < d_dumpCommands.size(); ++i) {
    Dump("declarations") << *d_dumpCommands[i];
    delete d_dumpCommands[i];
  }
  d_dumpCommands.clear();

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

  AlwaysAssert( d_propEngine->getAssertionLevel() == 0,
                "The PropEngine has pushed but the SmtEngine "
                "hasn't finished initializing!" );

  d_fullyInited = true;
  Assert(d_logic.isLocked());

  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(true));
  d_propEngine->assertFormula(NodeManager::currentNM()->mkConst<bool>(false).notNode());
}

void SmtEngine::shutdown() {
  doPendingPops();

  while(options::incrementalSolving() && d_userContext->getLevel() > 1) {
    internalPop(true);
  }

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  if(d_propEngine != NULL) {
    d_propEngine->shutdown();
  }
  if(d_theoryEngine != NULL) {
    d_theoryEngine->shutdown();
  }
  if(d_decisionEngine != NULL) {
    d_decisionEngine->shutdown();
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

    if(d_assertionList != NULL) {
      d_assertionList->deleteSelf();
    }

    for(unsigned i = 0; i < d_dumpCommands.size(); ++i) {
      delete d_dumpCommands[i];
      d_dumpCommands[i] = NULL;
    }
    d_dumpCommands.clear();

    DeleteAndClearCommandVector(d_modelGlobalCommands);

    if(d_modelCommands != NULL) {
      d_modelCommands->deleteSelf();
    }

    d_definedFunctions->deleteSelf();
    d_fmfRecFunctionsDefined->deleteSelf();

    delete d_theoryEngine;
    d_theoryEngine = NULL;
    delete d_propEngine;
    d_propEngine = NULL;
    delete d_decisionEngine;
    d_decisionEngine = NULL;


// d_proofManager is always created when proofs are enabled at configure time.
// Becuase of this, this code should not be wrapped in PROOF() which
// additionally checks flags such as options::proof().
#ifdef CVC4_PROOF
    delete d_proofManager;
    d_proofManager = NULL;
#endif

    delete d_stats;
    d_stats = NULL;
    delete d_statisticsRegistry;
    d_statisticsRegistry = NULL;

    delete d_private;
    d_private = NULL;

    delete d_userContext;
    d_userContext = NULL;
    delete d_context;
    d_context = NULL;

    delete d_channels;
    d_channels = NULL;

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
  setLogicInternal();
}

void SmtEngine::setLogic(const std::string& s)
{
  SmtScope smts(this);
  try {
    setLogic(LogicInfo(s));
  } catch(IllegalArgumentException& e) {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) { setLogic(string(logic)); }
LogicInfo SmtEngine::getLogicInfo() const {
  return d_logic;
}
void SmtEngine::setLogicInternal()
{
  Assert(!d_fullyInited, "setting logic in SmtEngine but the engine has already"
         " finished initializing for this run");
  d_logic.lock();
}

void SmtEngine::setDefaults() {
  Random::getRandom().setSeed(options::seed());
  // Language-based defaults
  if (!options::bitvectorDivByZeroConst.wasSetByUser())
  {
    options::bitvectorDivByZeroConst.set(options::inputLanguage()
                                         == language::input::LANG_SMTLIB_V2_6);
  }
  if (options::inputLanguage() == language::input::LANG_SYGUS)
  {
    if (!options::ceGuidedInst.wasSetByUser())
    {
      options::ceGuidedInst.set(true);
    }
    // must use Ferrante/Rackoff for real arithmetic
    if (!options::cbqiMidpoint.wasSetByUser())
    {
      options::cbqiMidpoint.set(true);
    }
  }

  if(options::forceLogicString.wasSetByUser()) {
    d_logic = LogicInfo(options::forceLogicString());
  }else if (options::solveIntAsBV() > 0) {
    d_logic = LogicInfo("QF_BV");
  }else if (d_logic.getLogicString() == "QF_NRA" && options::solveRealAsInt()) {
    d_logic = LogicInfo("QF_NIA");
  } else if ((d_logic.getLogicString() == "QF_UFBV" ||
              d_logic.getLogicString() == "QF_ABV") &&
             options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    d_logic = LogicInfo("QF_BV");
  }

  // set strings-exp
  /* - disabled for 1.4 release [MGD 2014.06.25]
  if(!d_logic.hasEverything() && d_logic.isTheoryEnabled(THEORY_STRINGS) ) {
    if(! options::stringExp.wasSetByUser()) {
      options::stringExp.set( true );
      Trace("smt") << "turning on strings-exp, for the theory of strings" << std::endl;
    }
  }
  */
  // for strings
  if(options::stringExp()) {
    if( !d_logic.isQuantified() ) {
      d_logic = d_logic.getUnlockedCopy();
      d_logic.enableQuantifiers();
      d_logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp"
                   << std::endl;
    }
    if(! options::fmfBound.wasSetByUser()) {
      options::fmfBound.set( true );
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    if(! options::fmfInstEngine.wasSetByUser()) {
      options::fmfInstEngine.set( true );
      Trace("smt") << "turning on fmf-inst-engine, for strings-exp" << std::endl;
    }
    /*
    if(! options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
      Trace("smt") << "turning on rewrite-divk, for strings-exp" << std::endl;
    }*/
    /*
    if(! options::stringFMF.wasSetByUser()) {
      options::stringFMF.set( true );
      Trace("smt") << "turning on strings-fmf, for strings-exp" << std::endl;
    }
    */
  }

  if ((options::checkModels() || options::checkSynthSol())
      && !options::produceAssertions())
  {
      Notice() << "SmtEngine: turning on produce-assertions to support "
               << "check-models or check-synth-sol." << endl;
      setOption("produce-assertions", SExpr("true"));
    }

  if(options::unsatCores()) {
    if(options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      if(options::simplificationMode.wasSetByUser()) {
        throw OptionException("simplification not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off simplification to support unsat-cores"
               << endl;
      options::simplificationMode.set(SIMPLIFICATION_MODE_NONE);
    }

    if(options::unconstrainedSimp()) {
      if(options::unconstrainedSimp.wasSetByUser()) {
        throw OptionException("unconstrained simplification not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off unconstrained simplification to support unsat-cores" << endl;
      options::unconstrainedSimp.set(false);
    }

    if(options::pbRewrites()) {
      if(options::pbRewrites.wasSetByUser()) {
        throw OptionException("pseudoboolean rewrites not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pseudoboolean rewrites to support unsat-cores" << endl;
      setOption("pb-rewrites", false);
    }

    if(options::sortInference()) {
      if(options::sortInference.wasSetByUser()) {
        throw OptionException("sort inference not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off sort inference to support unsat-cores" << endl;
      options::sortInference.set(false);
    }

    if(options::preSkolemQuant()) {
      if(options::preSkolemQuant.wasSetByUser()) {
        throw OptionException("pre-skolemization not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off pre-skolemization to support unsat-cores" << endl;
      options::preSkolemQuant.set(false);
    }

    if(options::bitvectorToBool()) {
      if(options::bitvectorToBool.wasSetByUser()) {
        throw OptionException("bv-to-bool not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bitvector-to-bool to support unsat-cores" << endl;
      options::bitvectorToBool.set(false);
    }

    if(options::boolToBitvector()) {
      if(options::boolToBitvector.wasSetByUser()) {
        throw OptionException("bool-to-bv not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bool-to-bitvector to support unsat-cores" << endl;
      options::boolToBitvector.set(false);
    }

    if(options::bvIntroducePow2()) {
      if(options::bvIntroducePow2.wasSetByUser()) {
        throw OptionException("bv-intro-pow2 not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off bv-intro-pow2 to support unsat-cores" << endl;
      setOption("bv-intro-pow2", false);
    }

    if(options::repeatSimp()) {
      if(options::repeatSimp.wasSetByUser()) {
        throw OptionException("repeat-simp not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off repeat-simp to support unsat-cores" << endl;
      setOption("repeat-simp", false);
    }

    if (options::globalNegate())
    {
      if (options::globalNegate.wasSetByUser())
      {
        throw OptionException("global-negate not supported with unsat cores");
      }
      Notice() << "SmtEngine: turning off global-negate to support unsat-cores"
               << endl;
      setOption("global-negate", false);
    }
  }

  if (options::cbqiBv()) {
    if(options::boolToBitvector.wasSetByUser()) {
      throw OptionException("bool-to-bv not supported with CBQI BV");
    }
    Notice() << "SmtEngine: turning off bool-to-bitvector to support CBQI BV"
             << endl;
    options::boolToBitvector.set(false);
  }

  if(options::produceAssignments() && !options::produceModels()) {
    Notice() << "SmtEngine: turning on produce-models to support produce-assignments" << endl;
    setOption("produce-models", SExpr("true"));
  }

  // Set the options for the theoryOf
  if(!options::theoryOfMode.wasSetByUser()) {
    if(d_logic.isSharingEnabled() &&
       !d_logic.isTheoryEnabled(THEORY_BV) &&
       !d_logic.isTheoryEnabled(THEORY_STRINGS) &&
       !d_logic.isTheoryEnabled(THEORY_SETS) ) {
      Trace("smt") << "setting theoryof-mode to term-based" << endl;
      options::theoryOfMode.set(THEORY_OF_TERM_BASED);
    }
  }

  // strings require LIA, UF; widen the logic
  if(d_logic.isTheoryEnabled(THEORY_STRINGS)) {
    LogicInfo log(d_logic.getUnlockedCopy());
    // Strings requires arith for length constraints, and also UF
    if(!d_logic.isTheoryEnabled(THEORY_UF)) {
      Trace("smt") << "because strings are enabled, also enabling UF" << endl;
      log.enableTheory(THEORY_UF);
    }
    if(!d_logic.isTheoryEnabled(THEORY_ARITH) || d_logic.isDifferenceLogic() || !d_logic.areIntegersUsed()) {
      Trace("smt") << "because strings are enabled, also enabling linear integer arithmetic" << endl;
      log.enableTheory(THEORY_ARITH);
      log.enableIntegers();
      log.arithOnlyLinear();
    }
    d_logic = log;
    d_logic.lock();
  }
  if(d_logic.isTheoryEnabled(THEORY_ARRAY) || d_logic.isTheoryEnabled(THEORY_DATATYPES) || d_logic.isTheoryEnabled(THEORY_SETS)) {
    if(!d_logic.isTheoryEnabled(THEORY_UF)) {
      LogicInfo log(d_logic.getUnlockedCopy());
      Trace("smt") << "because a theory that permits Boolean terms is enabled, also enabling UF" << endl;
      log.enableTheory(THEORY_UF);
      d_logic = log;
      d_logic.lock();
    }
  }

  // by default, symmetry breaker is on only for QF_UF
  if(! options::ufSymmetryBreaker.wasSetByUser()) {
    bool qf_uf = d_logic.isPure(THEORY_UF) && !d_logic.isQuantified() && !options::proof();
    Trace("smt") << "setting uf symmetry breaker to " << qf_uf << endl;
    options::ufSymmetryBreaker.set(qf_uf);
  }
  // by default, nonclausal simplification is off for QF_SAT
  if(! options::simplificationMode.wasSetByUser()) {
    bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
    Trace("smt") << "setting simplification mode to <" << d_logic.getLogicString() << "> " << (!qf_sat) << endl;
    //simplification=none works better for SMT LIB benchmarks with quantifiers, not others
    //options::simplificationMode.set(qf_sat || quantifiers ? SIMPLIFICATION_MODE_NONE : SIMPLIFICATION_MODE_BATCH);
    options::simplificationMode.set(qf_sat ? SIMPLIFICATION_MODE_NONE : SIMPLIFICATION_MODE_BATCH);
  }

  // If in arrays, set the UF handler to arrays
  if(d_logic.isTheoryEnabled(THEORY_ARRAY) && ( !d_logic.isQuantified() ||
     (d_logic.isQuantified() && !d_logic.isTheoryEnabled(THEORY_UF)))) {
    Theory::setUninterpretedSortOwner(THEORY_ARRAY);
  } else {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }

  // Turn on ite simplification for QF_LIA and QF_AUFBV
  // WARNING: These checks match much more than just QF_AUFBV and
  // QF_LIA logics. --K [2014/10/15]
  if(! options::doITESimp.wasSetByUser()) {
    bool qf_aufbv = !d_logic.isQuantified() &&
      d_logic.isTheoryEnabled(THEORY_ARRAY) &&
      d_logic.isTheoryEnabled(THEORY_UF) &&
      d_logic.isTheoryEnabled(THEORY_BV);
    bool qf_lia = !d_logic.isQuantified() &&
      d_logic.isPure(THEORY_ARITH) &&
      d_logic.isLinear() &&
      !d_logic.isDifferenceLogic() &&
      !d_logic.areRealsUsed();

    bool iteSimp = (qf_aufbv || qf_lia);
    Trace("smt") << "setting ite simplification to " << iteSimp << endl;
    options::doITESimp.set(iteSimp);
  }
  if(! options::compressItes.wasSetByUser() ){
    bool qf_lia = !d_logic.isQuantified() &&
      d_logic.isPure(THEORY_ARITH) &&
      d_logic.isLinear() &&
      !d_logic.isDifferenceLogic() &&
      !d_logic.areRealsUsed();

    bool compressIte = qf_lia;
    Trace("smt") << "setting ite compression to " << compressIte << endl;
    options::compressItes.set(compressIte);
  }
  if(! options::simplifyWithCareEnabled.wasSetByUser() ){
    bool qf_aufbv = !d_logic.isQuantified() &&
      d_logic.isTheoryEnabled(THEORY_ARRAY) &&
      d_logic.isTheoryEnabled(THEORY_UF) &&
      d_logic.isTheoryEnabled(THEORY_BV);

    bool withCare = qf_aufbv;
    Trace("smt") << "setting ite simplify with care to " << withCare << endl;
    options::simplifyWithCareEnabled.set(withCare);
  }
  // Turn off array eager index splitting for QF_AUFLIA
  if(! options::arraysEagerIndexSplitting.wasSetByUser()) {
    if (not d_logic.isQuantified() &&
        d_logic.isTheoryEnabled(THEORY_ARRAY) &&
        d_logic.isTheoryEnabled(THEORY_UF) &&
        d_logic.isTheoryEnabled(THEORY_ARITH)) {
      Trace("smt") << "setting array eager index splitting to false" << endl;
      options::arraysEagerIndexSplitting.set(false);
    }
  }
  // Turn on model-based arrays for QF_AX (unless models are enabled)
  // if(! options::arraysModelBased.wasSetByUser()) {
  //   if (not d_logic.isQuantified() &&
  //       d_logic.isTheoryEnabled(THEORY_ARRAY) &&
  //       d_logic.isPure(THEORY_ARRAY) &&
  //       !options::produceModels() &&
  //       !options::checkModels()) {
  //     Trace("smt") << "turning on model-based array solver" << endl;
  //     options::arraysModelBased.set(true);
  //   }
  // }
  // Turn on multiple-pass non-clausal simplification for QF_AUFBV
  if(! options::repeatSimp.wasSetByUser()) {
    bool repeatSimp = !d_logic.isQuantified() &&
                      (d_logic.isTheoryEnabled(THEORY_ARRAY) &&
                      d_logic.isTheoryEnabled(THEORY_UF) &&
                      d_logic.isTheoryEnabled(THEORY_BV)) &&
                      !options::unsatCores();
    Trace("smt") << "setting repeat simplification to " << repeatSimp << endl;
    options::repeatSimp.set(repeatSimp);
  }
  // Turn on unconstrained simplification for QF_AUFBV
  if(!options::unconstrainedSimp.wasSetByUser() ||
      options::incrementalSolving()) {
    //    bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
    //    bool uncSimp = false && !qf_sat && !options::incrementalSolving();
    bool uncSimp = !options::incrementalSolving() &&
                   !d_logic.isQuantified() &&
                   !options::produceModels() &&
                   !options::produceAssignments() &&
                   !options::checkModels() &&
                   !options::unsatCores() &&
                   (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_BV));
    Trace("smt") << "setting unconstrained simplification to " << uncSimp << endl;
    options::unconstrainedSimp.set(uncSimp);
  }
  // Unconstrained simp currently does *not* support model generation
  if (options::unconstrainedSimp.wasSetByUser() && options::unconstrainedSimp()) {
    if (options::produceModels()) {
      if (options::produceModels.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation.");
      }
      Notice() << "SmtEngine: turning off produce-models to support unconstrainedSimp" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      if (options::produceAssignments.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation (produce-assignments).");
      }
      Notice() << "SmtEngine: turning off produce-assignments to support unconstrainedSimp" << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      if (options::checkModels.wasSetByUser()) {
        throw OptionException("Cannot use unconstrained-simp with model generation (check-models).");
      }
      Notice() << "SmtEngine: turning off check-models to support unconstrainedSimp" << endl;
      setOption("check-models", SExpr("false"));
    }
  }


  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER &&
      options::incrementalSolving()) {
    if (options::incrementalSolving.wasSetByUser()) {
      throw OptionException(std::string("Eager bit-blasting does not currently support incremental mode. \n\
                                         Try --bitblast=lazy"));
    }
    Notice() << "SmtEngine: turning off incremental to support eager bit-blasting" << endl;
    setOption("incremental", SExpr("false"));
  }

  if (! options::bvEagerExplanations.wasSetByUser() &&
      d_logic.isTheoryEnabled(THEORY_ARRAY) &&
      d_logic.isTheoryEnabled(THEORY_BV)) {
    Trace("smt") << "enabling eager bit-vector explanations " << endl;
    options::bvEagerExplanations.set(true);
  }

  if( !options::bitvectorEqualitySolver() ){
    Trace("smt") << "disabling bvLazyRewriteExtf since equality solver is disabled" << endl;
    options::bvLazyRewriteExtf.set(false);
  }

  // Turn on arith rewrite equalities only for pure arithmetic
  if(! options::arithRewriteEq.wasSetByUser()) {
    bool arithRewriteEq = d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isQuantified();
    Trace("smt") << "setting arith rewrite equalities " << arithRewriteEq << endl;
    options::arithRewriteEq.set(arithRewriteEq);
  }
  if(!  options::arithHeuristicPivots.wasSetByUser()) {
    int16_t heuristicPivots = 5;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()) {
      if(d_logic.isDifferenceLogic()) {
        heuristicPivots = -1;
      } else if(!d_logic.areIntegersUsed()) {
        heuristicPivots = 0;
      }
    }
    Trace("smt") << "setting arithHeuristicPivots  " << heuristicPivots << endl;
    options::arithHeuristicPivots.set(heuristicPivots);
  }
  if(! options::arithPivotThreshold.wasSetByUser()){
    uint16_t pivotThreshold = 2;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      if(d_logic.isDifferenceLogic()){
        pivotThreshold = 16;
      }
    }
    Trace("smt") << "setting arith arithPivotThreshold  " << pivotThreshold << endl;
    options::arithPivotThreshold.set(pivotThreshold);
  }
  if(! options::arithStandardCheckVarOrderPivots.wasSetByUser()){
    int16_t varOrderPivots = -1;
    if(d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified()){
      varOrderPivots = 200;
    }
    Trace("smt") << "setting arithStandardCheckVarOrderPivots  " << varOrderPivots << endl;
    options::arithStandardCheckVarOrderPivots.set(varOrderPivots);
  }
  // Turn off early theory preprocessing if arithRewriteEq is on
  if (options::arithRewriteEq()) {
    d_earlyTheoryPP = false;
  }

  // Set decision mode based on logic (if not set by user)
  if(!options::decisionMode.wasSetByUser()) {
    decision::DecisionMode decMode =
      // ALL
      d_logic.hasEverything() ? decision::DECISION_STRATEGY_JUSTIFICATION :
      ( // QF_BV
        (not d_logic.isQuantified() &&
          d_logic.isPure(THEORY_BV)
          ) ||
        // QF_AUFBV or QF_ABV or QF_UFBV
        (not d_logic.isQuantified() &&
         (d_logic.isTheoryEnabled(THEORY_ARRAY) ||
          d_logic.isTheoryEnabled(THEORY_UF)) &&
         d_logic.isTheoryEnabled(THEORY_BV)
         ) ||
        // QF_AUFLIA (and may be ends up enabling QF_AUFLRA?)
        (not d_logic.isQuantified() &&
         d_logic.isTheoryEnabled(THEORY_ARRAY) &&
         d_logic.isTheoryEnabled(THEORY_UF) &&
         d_logic.isTheoryEnabled(THEORY_ARITH)
         ) ||
        // QF_LRA
        (not d_logic.isQuantified() &&
         d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
         ) ||
        // Quantifiers
        d_logic.isQuantified() ||
        // Strings
        d_logic.isTheoryEnabled(THEORY_STRINGS)
        ? decision::DECISION_STRATEGY_JUSTIFICATION
        : decision::DECISION_STRATEGY_INTERNAL
      );

    bool stoponly =
      // ALL
      d_logic.hasEverything() || d_logic.isTheoryEnabled(THEORY_STRINGS) ? false :
      ( // QF_AUFLIA
        (not d_logic.isQuantified() &&
         d_logic.isTheoryEnabled(THEORY_ARRAY) &&
         d_logic.isTheoryEnabled(THEORY_UF) &&
         d_logic.isTheoryEnabled(THEORY_ARITH)
         ) ||
        // QF_LRA
        (not d_logic.isQuantified() &&
         d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
         )
        ? true : false
      );

    Trace("smt") << "setting decision mode to " << decMode << endl;
    options::decisionMode.set(decMode);
    options::decisionStopOnly.set(stoponly);
  }
  if( options::incrementalSolving() ){
    //disable modes not supported by incremental
    options::sortInference.set( false );
    options::ufssFairnessMonotone.set( false );
    options::quantEpr.set( false );
    options::globalNegate.set(false);
  }
  if( d_logic.hasCardinalityConstraints() ){
    //must have finite model finding on
    options::finiteModelFind.set( true );
  }

  //if it contains a theory with non-termination, do not strictly enforce that quantifiers and theory combination must be interleaved
  if( d_logic.isTheoryEnabled(THEORY_STRINGS) || (d_logic.isTheoryEnabled(THEORY_ARITH) && !d_logic.isLinear()) ){
    if( !options::instWhenStrictInterleave.wasSetByUser() ){
      options::instWhenStrictInterleave.set( false );
    }
  }

  //local theory extensions
  if( options::localTheoryExt() ){
    if( !options::instMaxLevel.wasSetByUser() ){
      options::instMaxLevel.set( 0 );
    }
  }
  if( options::instMaxLevel()!=-1 ){
    Notice() << "SmtEngine: turning off cbqi to support instMaxLevel" << endl;
    options::cbqi.set(false);
  }
  //track instantiations?
  if( options::cbqiNestedQE() || ( options::proof() && !options::trackInstLemmas.wasSetByUser() ) ){
    options::trackInstLemmas.set( true );
  }

  if( ( options::fmfBoundLazy.wasSetByUser() && options::fmfBoundLazy() ) ||
      ( options::fmfBoundInt.wasSetByUser() && options::fmfBoundInt() ) ) {
    options::fmfBound.set( true );
  }
  //now have determined whether fmfBoundInt is on/off
  //apply fmfBoundInt options
  if( options::fmfBound() ){
    //must have finite model finding on
    options::finiteModelFind.set( true );
    if( ! options::mbqiMode.wasSetByUser() ||
        ( options::mbqiMode()!=quantifiers::MBQI_NONE &&
          options::mbqiMode()!=quantifiers::MBQI_FMC &&
          options::mbqiMode()!=quantifiers::MBQI_FMC_INTERVAL ) ){
      //if bounded integers are set, use no MBQI by default
      options::mbqiMode.set( quantifiers::MBQI_NONE );
    }
    if( ! options::prenexQuant.wasSetByUser() ){
      options::prenexQuant.set( quantifiers::PRENEX_QUANT_NONE );
    }
  }
  if( options::ufHo() ){
    //if higher-order, then current variants of model-based instantiation cannot be used
    if( options::mbqiMode()!=quantifiers::MBQI_NONE ){
      options::mbqiMode.set( quantifiers::MBQI_NONE );
    }
  }
  if( options::mbqiMode()==quantifiers::MBQI_ABS ){
    if( !d_logic.isPure(THEORY_UF) ){
      //MBQI_ABS is only supported in pure quantified UF
      options::mbqiMode.set( quantifiers::MBQI_FMC );
    }
  }
  if( options::ufssSymBreak() ){
    options::sortInference.set( true );
  }
  if( options::fmfFunWellDefinedRelevant() ){
    if( !options::fmfFunWellDefined.wasSetByUser() ){
      options::fmfFunWellDefined.set( true );
    }
  }
  if( options::fmfFunWellDefined() ){
    if( !options::finiteModelFind.wasSetByUser() ){
      options::finiteModelFind.set( true );
    }
  }
  //EPR
  if( options::quantEpr() ){
    if( !options::preSkolemQuant.wasSetByUser() ){
      options::preSkolemQuant.set( true );
    }
  }

  //now, have determined whether finite model find is on/off
  //apply finite model finding options
  if( options::finiteModelFind() ){
    //apply conservative quantifiers splitting
    if( !options::quantDynamicSplit.wasSetByUser() ){
      options::quantDynamicSplit.set( quantifiers::QUANT_DSPLIT_MODE_DEFAULT );
    }
    //do not eliminate extended arithmetic symbols from quantified formulas
    if( !options::elimExtArithQuant.wasSetByUser() ){
      options::elimExtArithQuant.set( false );
    }
    if( !options::eMatching.wasSetByUser() ){
      options::eMatching.set( options::fmfInstEngine() );
    }
    if( !options::instWhenMode.wasSetByUser() ){
      //instantiate only on last call
      if( options::eMatching() ){
        options::instWhenMode.set( quantifiers::INST_WHEN_LAST_CALL );
      }
    }
    if( options::mbqiMode()==quantifiers::MBQI_ABS ){
      if( !options::preSkolemQuant.wasSetByUser() ){
        options::preSkolemQuant.set( true );
      }
      if( !options::preSkolemQuantNested.wasSetByUser() ){
        options::preSkolemQuantNested.set( true );
      }
      if( !options::fmfOneInstPerRound.wasSetByUser() ){
        options::fmfOneInstPerRound.set( true );
      }
    }
  }

  //apply counterexample guided instantiation options
  if( options::cegqiSingleInvMode()!=quantifiers::CEGQI_SI_MODE_NONE ){
    if( !options::ceGuidedInst.wasSetByUser() ){
      options::ceGuidedInst.set( true );
    }
  }
  if( options::ceGuidedInst() ){
    //counterexample-guided instantiation for sygus
    if( !options::cegqiSingleInvMode.wasSetByUser() ){
      options::cegqiSingleInvMode.set( quantifiers::CEGQI_SI_MODE_USE );
    }
    if( !options::quantConflictFind.wasSetByUser() ){
      options::quantConflictFind.set( false );
    }
    if( !options::instNoEntail.wasSetByUser() ){
      options::instNoEntail.set( false );
    }
    if (options::sygusRew())
    {
      options::sygusRewSynth.set(true);
      options::sygusRewVerify.set(true);
    }
    if (options::sygusRewSynth() || options::sygusRewVerify())
    {
      // rewrite rule synthesis implies that sygus stream must be true
      options::sygusStream.set(true);
    }
    if (options::sygusStream())
    {
      // PBE and streaming modes are incompatible
      if (!options::sygusPbe.wasSetByUser())
      {
        options::sygusPbe.set(false);
      }
    }
    //do not allow partial functions
    if( !options::bitvectorDivByZeroConst.wasSetByUser() ){
      options::bitvectorDivByZeroConst.set( true );
    }
    if( !options::dtRewriteErrorSel.wasSetByUser() ){
      options::dtRewriteErrorSel.set( true );
    }
    //do not miniscope
    if( !options::miniscopeQuant.wasSetByUser() ){
      options::miniscopeQuant.set( false );
    }
    if( !options::miniscopeQuantFreeVar.wasSetByUser() ){
      options::miniscopeQuantFreeVar.set( false );
    }
    //rewrite divk
    if( !options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
    }
    //do not do macros
    if( !options::macrosQuant.wasSetByUser()) {
      options::macrosQuant.set( false );
    }
    if( !options::cbqiPreRegInst.wasSetByUser()) {
      options::cbqiPreRegInst.set( true );
    }
  }
  //counterexample-guided instantiation for non-sygus
  // enable if any possible quantifiers with arithmetic, datatypes or bitvectors
  if( d_logic.isQuantified() && 
      ( ( options::decisionMode()!=decision::DECISION_STRATEGY_INTERNAL &&
          ( d_logic.isTheoryEnabled(THEORY_ARITH) || d_logic.isTheoryEnabled(THEORY_DATATYPES) || d_logic.isTheoryEnabled(THEORY_BV) ) ) ||
        d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV) ||
        options::cbqiAll() ) ){
    if( !options::cbqi.wasSetByUser() ){
      options::cbqi.set( true );
    }
    // check whether we should apply full cbqi
    if (d_logic.isPure(THEORY_BV))
    {
      if (!options::cbqiFullEffort.wasSetByUser())
      {
        options::cbqiFullEffort.set(true);
      }
    }
  }
  if( options::cbqi() ){
    //must rewrite divk
    if( !options::rewriteDivk.wasSetByUser()) {
      options::rewriteDivk.set( true );
    }
    if (d_logic.isPure(THEORY_ARITH) || d_logic.isPure(THEORY_BV))
    {
      options::cbqiAll.set( false );
      if( !options::quantConflictFind.wasSetByUser() ){
        options::quantConflictFind.set( false );
      }
      if( !options::instNoEntail.wasSetByUser() ){
        options::instNoEntail.set( false );
      }
      if( !options::instWhenMode.wasSetByUser() && options::cbqiModel() ){
        //only instantiation should happen at last call when model is avaiable
        options::instWhenMode.set( quantifiers::INST_WHEN_LAST_CALL );
      }
    }else{
      // only supported in pure arithmetic or pure BV
      options::cbqiNestedQE.set(false);
    }
    // prenexing
    if (options::cbqiNestedQE()
        || options::decisionMode() == decision::DECISION_STRATEGY_INTERNAL)
    {
      // only complete with prenex = disj_normal or normal
      if (options::prenexQuant() <= quantifiers::PRENEX_QUANT_DISJ_NORMAL)
      {
        options::prenexQuant.set(quantifiers::PRENEX_QUANT_DISJ_NORMAL);
      }
    }
    else if (options::globalNegate())
    {
      if (!options::prenexQuant.wasSetByUser())
      {
        options::prenexQuant.set(quantifiers::PRENEX_QUANT_NONE);
      }
    }
  }
  //implied options...
  if( options::strictTriggers() ){
    if( !options::userPatternsQuant.wasSetByUser() ){
      options::userPatternsQuant.set( quantifiers::USER_PAT_MODE_TRUST );
    }
  }
  if( options::qcfMode.wasSetByUser() || options::qcfTConstraint() ){
    options::quantConflictFind.set( true );
  }
  if( options::cbqiNestedQE() ){
    options::prenexQuantUser.set( true );
    if( !options::preSkolemQuant.wasSetByUser() ){
      options::preSkolemQuant.set( true );
    }
  }
  //for induction techniques
  if( options::quantInduction() ){
    if( !options::dtStcInduction.wasSetByUser() ){
      options::dtStcInduction.set( true );
    }
    if( !options::intWfInduction.wasSetByUser() ){
      options::intWfInduction.set( true );
    }
  }
  if( options::dtStcInduction() ){
    //leads to unfairness FIXME
    if( !options::dtForceAssignment.wasSetByUser() ){
      options::dtForceAssignment.set( true );
    }
    //try to remove ITEs from quantified formulas
    if( !options::iteDtTesterSplitQuant.wasSetByUser() ){
      options::iteDtTesterSplitQuant.set( true );
    }
    if( !options::iteLiftQuant.wasSetByUser() ){
      options::iteLiftQuant.set( quantifiers::ITE_LIFT_QUANT_MODE_ALL );
    }
  }
  if( options::intWfInduction() ){
    if( !options::purifyTriggers.wasSetByUser() ){
      options::purifyTriggers.set( true );
    }
  }
  if( options::conjectureNoFilter() ){
    if( !options::conjectureFilterActiveTerms.wasSetByUser() ){
      options::conjectureFilterActiveTerms.set( false );
    }
    if( !options::conjectureFilterCanonical.wasSetByUser() ){
      options::conjectureFilterCanonical.set( false );
    }
    if( !options::conjectureFilterModel.wasSetByUser() ){
      options::conjectureFilterModel.set( false );
    }
  }
  if( options::conjectureGenPerRound.wasSetByUser() ){
    if( options::conjectureGenPerRound()>0 ){
      options::conjectureGen.set( true );
    }else{
      options::conjectureGen.set( false );
    }
  }
  //can't pre-skolemize nested quantifiers without UF theory
  if( !d_logic.isTheoryEnabled(THEORY_UF) && options::preSkolemQuant() ){
    if( !options::preSkolemQuantNested.wasSetByUser() ){
      options::preSkolemQuantNested.set( false );
    }
  }
  if( !d_logic.isTheoryEnabled(THEORY_DATATYPES) ){
    options::quantDynamicSplit.set( quantifiers::QUANT_DSPLIT_MODE_NONE );
  }

  //until bugs 371,431 are fixed
  if( ! options::minisatUseElim.wasSetByUser()){
    //AJR: cannot use minisat elim for new implementation of sets TODO: why?
    if( d_logic.isTheoryEnabled(THEORY_SETS) || d_logic.isQuantified() || options::produceModels() || options::produceAssignments() || options::checkModels() ){
      options::minisatUseElim.set( false );
    }
  }
  else if (options::minisatUseElim()) {
    if (options::produceModels()) {
      Notice() << "SmtEngine: turning off produce-models to support minisatUseElim" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      Notice() << "SmtEngine: turning off produce-assignments to support minisatUseElim" << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      Notice() << "SmtEngine: turning off check-models to support minisatUseElim" << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::produceAssignments() || options::checkModels()) {
    options::arraysOptimizeLinear.set(false);
    options::arraysLazyRIntro1.set(false);
  }

  // Non-linear arithmetic does not support models unless nlExt is enabled
  if ((d_logic.isTheoryEnabled(THEORY_ARITH) && !d_logic.isLinear()
       && !options::nlExt())
      || options::globalNegate())
  {
    std::string reason =
        options::globalNegate() ? "--global-negate" : "nonlinear arithmetic";
    if (options::produceModels()) {
      if(options::produceModels.wasSetByUser()) {
        throw OptionException(
            std::string("produce-model not supported with " + reason));
      }
      Warning()
          << "SmtEngine: turning off produce-models because unsupported for "
          << reason << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::produceAssignments()) {
      if(options::produceAssignments.wasSetByUser()) {
        throw OptionException(
            std::string("produce-assignments not supported with " + reason));
      }
      Warning() << "SmtEngine: turning off produce-assignments because "
                   "unsupported for "
                << reason << endl;
      setOption("produce-assignments", SExpr("false"));
    }
    if (options::checkModels()) {
      if(options::checkModels.wasSetByUser()) {
        throw OptionException(
            std::string("check-models not supported with " + reason));
      }
      Warning()
          << "SmtEngine: turning off check-models because unsupported for "
          << reason << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  if(options::incrementalSolving() && options::proof()) {
    Warning() << "SmtEngine: turning off incremental solving mode (not yet supported with --proof, try --tear-down-incremental instead)" << endl;
    setOption("incremental", SExpr("false"));
  }
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

  // Check for CVC4-specific info keys (prefixed with "cvc4-" or "cvc4_")
  if(key.length() > 5) {
    string prefix = key.substr(0, 5);
    if(prefix == "cvc4-" || prefix == "cvc4_") {
      string cvc4key = key.substr(5);
      if(cvc4key == "logic") {
        if(! value.isAtom()) {
          throw OptionException("argument to (set-info :cvc4-logic ..) must be a string");
        }
        SmtScope smts(this);
        d_logic = value.getValue();
        setLogicInternal();
        return;
      } else {
        throw UnrecognizedOptionException();
      }
    }
  }

  // Check for standard info keys (SMT-LIB v1, SMT-LIB v2, ...)
  if(key == "source" ||
     key == "category" ||
     key == "difficulty" ||
     key == "notes") {
    // ignore these
    return;
  } else if(key == "name") {
    d_filename = value.getValue();
    return;
  } else if(key == "smt-lib-version") {
    if( (value.isInteger() && value.getIntegerValue() == Integer(2)) ||
        (value.isRational() && value.getRationalValue() == Rational(2)) ||
        value.getValue() == "2" ||
        value.getValue() == "2.0" ) {
      options::inputLanguage.set(language::input::LANG_SMTLIB_V2_0);

      // supported SMT-LIB version
      if(!options::outputLanguage.wasSetByUser() &&
         ( options::outputLanguage() == language::output::LANG_SMTLIB_V2_5 || options::outputLanguage() == language::output::LANG_SMTLIB_V2_6 )) {
        options::outputLanguage.set(language::output::LANG_SMTLIB_V2_0);
        *options::out() << language::SetLanguage(language::output::LANG_SMTLIB_V2_0);
      }
      return;
    } else if( (value.isRational() && value.getRationalValue() == Rational(5, 2)) ||
               value.getValue() == "2.5" ) {
      options::inputLanguage.set(language::input::LANG_SMTLIB_V2_5);

      // supported SMT-LIB version
      if(!options::outputLanguage.wasSetByUser() &&
         options::outputLanguage() == language::output::LANG_SMTLIB_V2_0) {
        options::outputLanguage.set(language::output::LANG_SMTLIB_V2_5);
        *options::out() << language::SetLanguage(language::output::LANG_SMTLIB_V2_5);
      }
      return;
    } else if( (value.isRational() && value.getRationalValue() == Rational(13, 5)) ||
               value.getValue() == "2.6" ) {
      options::inputLanguage.set(language::input::LANG_SMTLIB_V2_6);

      // supported SMT-LIB version
      if(!options::outputLanguage.wasSetByUser() &&
         options::outputLanguage() == language::output::LANG_SMTLIB_V2_0) {
        options::outputLanguage.set(language::output::LANG_SMTLIB_V2_6);
        *options::out() << language::SetLanguage(language::output::LANG_SMTLIB_V2_6);
      }
      return;
    }
    Warning() << "Warning: unsupported smt-lib-version: " << value << endl;
    throw UnrecognizedOptionException();
  } else if(key == "status") {
    string s;
    if(value.isAtom()) {
      s = value.getValue();
    }
    if(s != "sat" && s != "unsat" && s != "unknown") {
      throw OptionException("argument to (set-info :status ..) must be "
                            "`sat' or `unsat' or `unknown'");
    }
    d_status = Result(s, d_filename);
    return;
  }
  throw UnrecognizedOptionException();
}

CVC4::SExpr SmtEngine::getInfo(const std::string& key) const {

  SmtScope smts(this);

  Trace("smt") << "SMT getInfo(" << key << ")" << endl;
  if(key == "all-statistics") {
    vector<SExpr> stats;
    for(StatisticsRegistry::const_iterator i = NodeManager::fromExprManager(d_exprManager)->getStatisticsRegistry()->begin();
        i != NodeManager::fromExprManager(d_exprManager)->getStatisticsRegistry()->end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    for(StatisticsRegistry::const_iterator i = d_statisticsRegistry->begin();
        i != d_statisticsRegistry->end();
        ++i) {
      vector<SExpr> v;
      v.push_back((*i).first);
      v.push_back((*i).second);
      stats.push_back(v);
    }
    return SExpr(stats);
  } else if(key == "error-behavior") {
    // immediate-exit | continued-execution
    if( options::continuedExecution() || options::interactive() ) {
      return SExpr(SExpr::Keyword("continued-execution"));
    } else {
      return SExpr(SExpr::Keyword("immediate-exit"));
    }
  } else if(key == "name") {
    return SExpr(Configuration::getName());
  } else if(key == "version") {
    return SExpr(Configuration::getVersionString());
  } else if(key == "authors") {
    return SExpr(Configuration::about());
  } else if(key == "status") {
    // sat | unsat | unknown
    switch(d_status.asSatisfiabilityResult().isSat()) {
    case Result::SAT:
      return SExpr(SExpr::Keyword("sat"));
    case Result::UNSAT:
      return SExpr(SExpr::Keyword("unsat"));
    default:
      return SExpr(SExpr::Keyword("unknown"));
    }
  } else if(key == "reason-unknown") {
    if(!d_status.isNull() && d_status.isUnknown()) {
      stringstream ss;
      ss << d_status.whyUnknown();
      string s = ss.str();
      transform(s.begin(), s.end(), s.begin(), ::tolower);
      return SExpr(SExpr::Keyword(s));
    } else {
      throw ModalException("Can't get-info :reason-unknown when the "
                           "last result wasn't unknown!");
    }
  } else if(key == "assertion-stack-levels") {
    AlwaysAssert(d_userLevels.size() <=
                 std::numeric_limits<unsigned long int>::max());
    return SExpr(static_cast<unsigned long int>(d_userLevels.size()));
  } else if(key == "all-options") {
    // get the options, like all-statistics
    std::vector< std::vector<std::string> > current_options =
      Options::current()->getOptions();
    return SExpr::parseListOfListOfAtoms(current_options);
  } else {
    throw UnrecognizedOptionException();
  }
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
                               Expr formula)
{
  SmtScope smts(this);
  doPendingPops();
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
  debugCheckFormals(formals, func);

  stringstream ss;
  ss << language::SetLanguage(
            language::SetLanguage::getLanguage(Dump.getStream()))
     << func;
  DefineFunctionCommand c(ss.str(), func, formals, formula);
  addToModelCommandAndDump(
      c, ExprManager::VAR_FLAG_DEFINED, true, "declarations");

  PROOF(if (options::checkUnsatCores()) {
    d_defineCommands.push_back(c.clone());
  });

  // type check body
  debugCheckFunctionBody(formula, formals, func);

  // Substitute out any abstract values in formula
  Expr form =
      d_private->substituteAbstractValues(Node::fromExpr(formula)).toExpr();

  TNode funcNode = func.getTNode();
  vector<Node> formalsNodes;
  for(vector<Expr>::const_iterator i = formals.begin(),
        iend = formals.end();
      i != iend;
      ++i) {
    formalsNodes.push_back((*i).getNode());
  }
  TNode formNode = form.getTNode();
  DefinedFunction def(funcNode, formalsNodes, formNode);
  // Permit (check-sat) (define-fun ...) (get-value ...) sequences.
  // Otherwise, (check-sat) (get-value ((! foo :named bar))) breaks
  // d_haveAdditions = true;
  Debug("smt") << "definedFunctions insert " << funcNode << " " << formNode << endl;
  d_definedFunctions->insert(funcNode, def);
}

void SmtEngine::defineFunctionsRec(
    const std::vector<Expr>& funcs,
    const std::vector<std::vector<Expr> >& formals,
    const std::vector<Expr>& formulas)
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
    Dump("raw-benchmark") << DefineFunctionRecCommand(funcs, formals, formulas);
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
    Expr e = d_private->substituteAbstractValues(Node::fromExpr(lem)).toExpr();
    if (d_assertionList != NULL)
    {
      d_assertionList->push_back(e);
    }
    d_private->addFormula(e.getNode(), false);
  }
}

void SmtEngine::defineFunctionRec(Expr func,
                                  const std::vector<Expr>& formals,
                                  Expr formula)
{
  std::vector<Expr> funcs;
  funcs.push_back(func);
  std::vector<std::vector<Expr> > formals_multi;
  formals_multi.push_back(formals);
  std::vector<Expr> formulas;
  formulas.push_back(formula);
  defineFunctionsRec(funcs, formals_multi, formulas);
}

bool SmtEngine::isDefinedFunction( Expr func ){
  Node nf = Node::fromExpr( func );
  Debug("smt") << "isDefined function " << nf << "?" << std::endl;
  return d_definedFunctions->find(nf) != d_definedFunctions->end();
}

void SmtEnginePrivate::finishInit() {
  d_preprocessingPassContext.reset(new PreprocessingPassContext(&d_smt));
  //TODO: register passes here
}

Node SmtEnginePrivate::expandDefinitions(TNode n, unordered_map<Node, Node, NodeHashFunction>& cache, bool expandOnly)
{
  stack< triple<Node, Node, bool> > worklist;
  stack<Node> result;
  worklist.push(make_triple(Node(n), Node(n), false));
  // The worklist is made of triples, each is input / original node then the output / rewritten node
  // and finally a flag tracking whether the children have been explored (i.e. if this is a downward
  // or upward pass).

  do {
    spendResource(options::preprocessStep());
    n = worklist.top().first;                      // n is the input / original
    Node node = worklist.top().second;             // node is the output / result
    bool childrenPushed = worklist.top().third;
    worklist.pop();

    // Working downwards
    if(!childrenPushed) {
      Kind k = n.getKind();

      // we can short circuit (variable) leaves
      if(n.isVar()) {
        SmtEngine::DefinedFunctionMap::const_iterator i = d_smt.d_definedFunctions->find(n);
        if(i != d_smt.d_definedFunctions->end()) {
          // replacement must be closed
          if((*i).second.getFormals().size() > 0) {
            result.push(d_smt.d_nodeManager->mkNode(kind::LAMBDA, d_smt.d_nodeManager->mkNode(kind::BOUND_VAR_LIST, (*i).second.getFormals()), (*i).second.getFormula()));
            continue;
          }
          // don't bother putting in the cache
          result.push((*i).second.getFormula());
          continue;
        }
        // don't bother putting in the cache
        result.push(n);
        continue;
      }

      // maybe it's in the cache
      unordered_map<Node, Node, NodeHashFunction>::iterator cacheHit = cache.find(n);
      if(cacheHit != cache.end()) {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it
      bool doExpand = k == kind::APPLY;
      if( !doExpand ){
        if( options::macrosQuant() ){
          //expand if we have inferred an operator corresponds to a defined function
          doExpand = k==kind::APPLY_UF && d_smt.isDefinedFunction( n.getOperator().toExpr() );
        }
      }
      if (doExpand) {
        vector<Node> formals;
        TNode fm;
        if( n.getOperator().getKind() == kind::LAMBDA ){
          TNode op = n.getOperator();
          // lambda
          for( unsigned i=0; i<op[0].getNumChildren(); i++ ){
            formals.push_back( op[0][i] );
          }
          fm = op[1];
        }else{
          // application of a user-defined symbol
          TNode func = n.getOperator();
          SmtEngine::DefinedFunctionMap::const_iterator i = d_smt.d_definedFunctions->find(func);
          if(i == d_smt.d_definedFunctions->end()) {
            throw TypeCheckingException(n.toExpr(), string("Undefined function: `") + func.toString() + "'");
          }
          DefinedFunction def = (*i).second;
          formals = def.getFormals();

          if(Debug.isOn("expand")) {
            Debug("expand") << "found: " << n << endl;
            Debug("expand") << " func: " << func << endl;
            string name = func.getAttribute(expr::VarNameAttr());
            Debug("expand") << "     : \"" << name << "\"" << endl;
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

          fm = def.getFormula();
        }

        Node instance = fm.substitute(formals.begin(),
                                      formals.end(),
                                      n.begin(),
                                      n.begin() + formals.size());
        Debug("expand") << "made : " << instance << endl;

        Node expanded = expandDefinitions(instance, cache, expandOnly);
        cache[n] = (n == expanded ? Node::null() : expanded);
        result.push(expanded);
        continue;

      } else if(! expandOnly) {
        // do not do any theory stuff if expandOnly is true

        theory::Theory* t = d_smt.d_theoryEngine->theoryOf(node);

        Assert(t != NULL);
        LogicRequest req(d_smt);
        node = t->expandDefinition(req, n);
      }

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(make_triple(Node(n), node, true));            // Original and rewritten result

      for(size_t i = 0; i < node.getNumChildren(); ++i) {
        worklist.push(make_triple(node[i], node[i], false));      // Rewrite the children of the result only
      }

    } else {
      // Working upwards
      // Reconstruct the node from it's (now rewritten) children on the stack

      Debug("expand") << "cons : " << node << endl;
      if(node.getNumChildren()>0) {
        //cout << "cons : " << node << endl;
        NodeBuilder<> nb(node.getKind());
        if(node.getMetaKind() == kind::metakind::PARAMETERIZED) {
          Debug("expand") << "op   : " << node.getOperator() << endl;
          //cout << "op   : " << node.getOperator() << endl;
          nb << node.getOperator();
        }
        for(size_t i = 0; i < node.getNumChildren(); ++i) {
          Assert(!result.empty());
          Node expanded = result.top();
          result.pop();
          //cout << "exchld : " << expanded << endl;
          Debug("expand") << "exchld : " << expanded << endl;
          nb << expanded;
        }
        node = nb;
      }
      cache[n] = n == node ? Node::null() : node;           // Only cache once all subterms are expanded
      result.push(node);
    }
  } while(!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}

//TODO: clean this up
struct intToBV_stack_element {
  TNode node;
  bool children_added;
  intToBV_stack_element(TNode node)
  : node(node), children_added(false) {}
};/* struct intToBV_stack_element */

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;

Node SmtEnginePrivate::intToBVMakeBinary(TNode n, NodeMap& cache) {
  // Do a topological sort of the subexpressions and substitute them
  vector<intToBV_stack_element> toVisit;
  toVisit.push_back(n);

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    NodeMap::iterator find = cache.find(current);
    if (find != cache.end()) {
      toVisit.pop_back();
      continue;
    }
    if (stackHead.children_added) {
      // Children have been processed, so rebuild this node
      Node result;
      NodeManager* nm = NodeManager::currentNM();
      if (current.getNumChildren() > 2 && (current.getKind() == kind::PLUS || current.getKind() == kind::MULT)) {
        Assert(cache.find(current[0]) != cache.end());
        result = cache[current[0]];
        for (unsigned i = 1; i < current.getNumChildren(); ++ i) {
          Assert(cache.find(current[i]) != cache.end());
          Node child = current[i];
          Node childRes = cache[current[i]];
          result = nm->mkNode(current.getKind(), result, childRes);
        }
      }
      else {
        NodeBuilder<> builder(current.getKind());
        for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
          Assert(cache.find(current[i]) != cache.end());
          builder << cache[current[i]];
        }
        result = builder;
      }
      cache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        cache[current] = current;
        toVisit.pop_back();
      }
    }
  }
  return cache[n];
}

Node SmtEnginePrivate::intToBV(TNode n, NodeMap& cache) {
  int size = options::solveIntAsBV();
  AlwaysAssert(size > 0);
  AlwaysAssert(!options::incrementalSolving());

  vector<intToBV_stack_element> toVisit;
  NodeMap binaryCache;
  Node n_binary = intToBVMakeBinary(n, binaryCache);
  toVisit.push_back(TNode(n_binary));

  while (!toVisit.empty())
  {
    // The current node we are processing
    intToBV_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.node;

    // If node is already in the cache we're done, pop from the stack
    NodeMap::iterator find = cache.find(current);
    if (find != cache.end()) {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    NodeManager* nm = NodeManager::currentNM();
    if (stackHead.children_added) {
      // Children have been processed, so rebuild this node
      vector<Node> children;
      unsigned max = 0;
      for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
        Assert(cache.find(current[i]) != cache.end());
        TNode childRes = cache[current[i]];
        TypeNode type = childRes.getType();
        if (type.isBitVector()) {
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize > max) {
            max = bvsize;
          }
        }
        children.push_back(childRes);
      }

      kind::Kind_t newKind = current.getKind();
      if (max > 0) {
        switch (newKind) {
          case kind::PLUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_PLUS;
            max = max + 1;
            break;
          case kind::MULT:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_MULT;
            max = max * 2;
            break;
          case kind::MINUS:
            Assert(children.size() == 2);
            newKind = kind::BITVECTOR_SUB;
            max = max + 1;
            break;
          case kind::UMINUS:
            Assert(children.size() == 1);
            newKind = kind::BITVECTOR_NEG;
            max = max + 1;
            break;
          case kind::LT:
            newKind = kind::BITVECTOR_SLT;
            break;
          case kind::LEQ:
            newKind = kind::BITVECTOR_SLE;
            break;
          case kind::GT:
            newKind = kind::BITVECTOR_SGT;
            break;
          case kind::GEQ:
            newKind = kind::BITVECTOR_SGE;
            break;
          case kind::EQUAL:
          case kind::ITE:
            break;
          default:
            if (Theory::theoryOf(current) == THEORY_BOOL) {
              break;
            }
            throw TypeCheckingException(current.toExpr(), string("Cannot translate to BV: ") + current.toString());
        }
        for (unsigned i = 0; i < children.size(); ++i) {
          TypeNode type = children[i].getType();
          if (!type.isBitVector()) {
            continue;
          }
          unsigned bvsize = type.getBitVectorSize();
          if (bvsize < max) {
            // sign extend
            Node signExtendOp = nm->mkConst<BitVectorSignExtend>(BitVectorSignExtend(max - bvsize));
            children[i] = nm->mkNode(signExtendOp, children[i]);
          }
        }
      }
      NodeBuilder<> builder(newKind);
      for (unsigned i = 0; i < children.size(); ++i) {
        builder << children[i];
      }
      // Mark the substitution and continue
      Node result = builder;

      result = Rewriter::rewrite(result);
      cache[current] = result;
      toVisit.pop_back();
    } else {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0) {
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = cache.find(childNode);
          if (childFind == cache.end()) {
            toVisit.push_back(childNode);
          }
        }
      } else {
        // It's a leaf: could be a variable or a numeral
        Node result = current;
        if (current.isVar()) {
          if (current.getType() == nm->integerType()) {
            result = nm->mkSkolem("__intToBV_var", nm->mkBitVectorType(size),
                                  "Variable introduced in intToBV pass");
          }
          else {
            AlwaysAssert(current.getType() == nm->booleanType());
          }
        }
        else if (current.isConst()) {
          switch (current.getKind()) {
            case kind::CONST_RATIONAL: {
              Rational constant = current.getConst<Rational>();
              AlwaysAssert(constant.isIntegral());
              AlwaysAssert(constant >= 0);
              BitVector bv(size, constant.getNumerator());
              if (bv.toSignedInteger() != constant.getNumerator())
              {
                throw TypeCheckingException(
                    current.toExpr(),
                    string("Not enough bits for constant in intToBV: ")
                        + current.toString());
              }
              result = nm->mkConst(bv);
              break;
            }
            case kind::CONST_BOOLEAN:
              break;
            default:
              throw TypeCheckingException(current.toExpr(), string("Cannot translate const to BV: ") + current.toString());
          }
        }
        else {
          throw TypeCheckingException(current.toExpr(), string("Cannot translate to BV: ") + current.toString());
        }
        cache[current] = result;
        toVisit.pop_back();
      }
    }
  }
  return cache[n_binary];
}

Node SmtEnginePrivate::realToInt(TNode n, NodeMap& cache, std::vector< Node >& var_eq) {
  Trace("real-as-int-debug") << "Convert : " << n << std::endl;
  NodeMap::iterator find = cache.find(n);
  if (find != cache.end()) {
    return (*find).second;
  }else{
    Node ret = n;
    if( n.getNumChildren()>0 ){
      if( n.getKind()==kind::EQUAL || n.getKind()==kind::GEQ || n.getKind()==kind::LT || n.getKind()==kind::GT || n.getKind()==kind::LEQ ){
        ret = Rewriter::rewrite( n );
        Trace("real-as-int-debug") << "Now looking at : " << ret << std::endl;
        if( !ret.isConst() ){
          Node ret_lit = ret.getKind()==kind::NOT ? ret[0] : ret;
          bool ret_pol = ret.getKind()!=kind::NOT;
          std::map< Node, Node > msum;
          if (ArithMSum::getMonomialSumLit(ret_lit, msum))
          {
            //get common coefficient
            std::vector< Node > coeffs;
            for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
              Node v = itm->first;
              Node c = itm->second;
              if( !c.isNull() ){
                Assert( c.isConst() );
                coeffs.push_back( NodeManager::currentNM()->mkConst( Rational( c.getConst<Rational>().getDenominator() ) ) );
              }
            }
            Node cc = coeffs.empty() ? Node::null() : ( coeffs.size()==1 ? coeffs[0] : Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, coeffs ) ) );
            std::vector< Node > sum;
            for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
              Node v = itm->first;
              Node c = itm->second;
              Node s;
              if( c.isNull() ){
                c = cc.isNull() ? NodeManager::currentNM()->mkConst( Rational( 1 ) ) : cc;
              }else{
                if( !cc.isNull() ){
                  c = Rewriter::rewrite( NodeManager::currentNM()->mkNode( kind::MULT, c, cc ) );
                }
              }
              Assert( c.getType().isInteger() );
              if( v.isNull() ){
                sum.push_back( c );
              }else{
                Node vv = realToInt( v, cache, var_eq );
                if( vv.getType().isInteger() ){
                  sum.push_back( NodeManager::currentNM()->mkNode( kind::MULT, c, vv ) );
                }else{
                  throw TypeCheckingException(v.toExpr(), string("Cannot translate to Int: ") + v.toString());
                }
              }
            }
            Node sumt = sum.empty() ? NodeManager::currentNM()->mkConst( Rational( 0 ) ) : ( sum.size()==1 ? sum[0] : NodeManager::currentNM()->mkNode( kind::PLUS, sum ) );
            ret = NodeManager::currentNM()->mkNode( ret_lit.getKind(), sumt, NodeManager::currentNM()->mkConst( Rational( 0 ) ) );
            if( !ret_pol ){
              ret = ret.negate();
            }
            Trace("real-as-int") << "Convert : " << std::endl;
            Trace("real-as-int") << "   " << n << std::endl;
            Trace("real-as-int") << "   " << ret << std::endl;
          }else{
            throw TypeCheckingException(n.toExpr(), string("Cannot translate to Int: ") + n.toString());
          }
        }
      }else{
        bool childChanged = false;
        std::vector< Node > children;
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          Node nc = realToInt( n[i], cache, var_eq );
          childChanged = childChanged || nc!=n[i];
          children.push_back( nc );
        }
        if( childChanged ){
          ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
        }
      }
    }else{
      if( n.isVar() ){
        if( !n.getType().isInteger() ){
          ret = NodeManager::currentNM()->mkSkolem("__realToInt_var", NodeManager::currentNM()->integerType(), "Variable introduced in realToInt pass");
          var_eq.push_back( n.eqNode( ret ) );
          TheoryModel* m = d_smt.d_theoryEngine->getModel();
          m->addSubstitution(n,ret);
        }
      }
    }
    cache[n] = ret;
    return ret;
  }
}

Node SmtEnginePrivate::purifyNlTerms(TNode n, NodeMap& cache, NodeMap& bcache, std::vector< Node >& var_eq, bool beneathMult) {
  if( beneathMult ){
    NodeMap::iterator find = bcache.find(n);
    if (find != bcache.end()) {
      return (*find).second;
    }
  }else{
    NodeMap::iterator find = cache.find(n);
    if (find != cache.end()) {
      return (*find).second;
    }
  }
  Node ret = n;
  if( n.getNumChildren()>0 ){
    if( beneathMult && n.getKind()!=kind::MULT ){
      //new variable
      ret = NodeManager::currentNM()->mkSkolem("__purifyNl_var", n.getType(), "Variable introduced in purifyNl pass");
      Node np = purifyNlTerms( n, cache, bcache, var_eq, false );
      var_eq.push_back( np.eqNode( ret ) );
    }else{
      bool beneathMultNew = beneathMult || n.getKind()==kind::MULT;
      bool childChanged = false;
      std::vector< Node > children;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node nc = purifyNlTerms( n[i], cache, bcache, var_eq, beneathMultNew );
        childChanged = childChanged || nc!=n[i];
        children.push_back( nc );
      }
      if( childChanged ){
        ret = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
  }
  if( beneathMult ){
    bcache[n] = ret;
  }else{
    cache[n] = ret;
  }
  return ret;
}

void SmtEnginePrivate::removeITEs() {
  d_smt.finalOptionsAreSet();
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::removeITEs()" << endl;

  // Remove all of the ITE occurrences and normalize
  d_iteRemover.run(d_assertions.ref(), d_iteSkolemMap, true);
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    d_assertions.replace(i, Rewriter::rewrite(d_assertions[i]));
  }
}

void SmtEnginePrivate::staticLearning() {
  d_smt.finalOptionsAreSet();
  spendResource(options::preprocessStep());

  TimerStat::CodeTimer staticLearningTimer(d_smt.d_stats->d_staticLearningTime);

  Trace("simplify") << "SmtEnginePrivate::staticLearning()" << endl;

  for (unsigned i = 0; i < d_assertions.size(); ++ i) {

    NodeBuilder<> learned(kind::AND);
    learned << d_assertions[i];
    d_smt.d_theoryEngine->ppStaticLearn(d_assertions[i], learned);
    if(learned.getNumChildren() == 1) {
      learned.clear();
    } else {
      d_assertions.replace(i, learned);
    }
  }
}

// do dumping (before/after any preprocessing pass)
static void dumpAssertions(const char* key,
                           const AssertionPipeline& assertionList) {
  if( Dump.isOn("assertions") &&
      Dump.isOn(string("assertions:") + key) ) {
    // Push the simplified assertions to the dump output stream
    for(unsigned i = 0; i < assertionList.size(); ++ i) {
      TNode n = assertionList[i];
      Dump("assertions") << AssertCommand(Expr(n.toExpr()));
    }
  }
}

// returns false if it learns a conflict
bool SmtEnginePrivate::nonClausalSimplify() {
  spendResource(options::preprocessStep());
  d_smt.finalOptionsAreSet();

  if(options::unsatCores() || options::fewerPreprocessingHoles()) {
    return true;
  }

  TimerStat::CodeTimer nonclausalTimer(d_smt.d_stats->d_nonclausalSimplificationTime);

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify()" << endl;
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Trace("simplify") << "Assertion #" << i << " : " << d_assertions[i] << std::endl;
  }

  if(d_propagatorNeedsFinish) {
    d_propagator.finish();
    d_propagatorNeedsFinish = false;
  }
  d_propagator.initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
    // Don't reprocess substitutions
    if (d_substitutionsIndex > 0 && i == d_substitutionsIndex) {
      continue;
    }
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting " << d_assertions[i] << endl;
    Debug("cores") << "d_propagator assertTrue: " << d_assertions[i] << std::endl;
    d_propagator.assertTrue(d_assertions[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (d_propagator.propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    Node falseNode = NodeManager::currentNM()->mkConst<bool>(false);
    Assert(!options::unsatCores() && !options::fewerPreprocessingHoles());
    d_assertions.clear();
    addFormula(falseNode, false, false);
    d_propagatorNeedsFinish = true;
    return false;
  }


  Trace("simplify") << "Iterate through " << d_nonClausalLearnedLiterals.size() << " learned literals." << std::endl;
  // No conflict, go through the literals and solve them
  SubstitutionMap constantPropagations(d_smt.d_context);
  SubstitutionMap newSubstitutions(d_smt.d_context);
  SubstitutionMap::iterator pos;
  unsigned j = 0;
  for(unsigned i = 0, i_end = d_nonClausalLearnedLiterals.size(); i < i_end; ++ i) {
    // Simplify the literal we learned wrt previous substitutions
    Node learnedLiteral = d_nonClausalLearnedLiterals[i];
    Assert(Rewriter::rewrite(learnedLiteral) == learnedLiteral);
    Assert(d_topLevelSubstitutions.apply(learnedLiteral) == learnedLiteral);
    Trace("simplify") << "Process learnedLiteral : " << learnedLiteral << std::endl;
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew) {
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after newSubs : " << learnedLiteral << std::endl;
    for (;;) {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral) {
        break;
      }
      ++d_smt.d_stats->d_numConstantProps;
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    Trace("simplify") << "Process learnedLiteral, after constProp : " << learnedLiteral << std::endl;
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
        Assert(!options::unsatCores());
        d_assertions.clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false);
        d_propagatorNeedsFinish = true;
        return false;
      }
    }

    // Solve it with the corresponding theory, possibly adding new
    // substitutions to newSubstitutions
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "solving " << learnedLiteral << endl;

    Theory::PPAssertStatus solveStatus =
      d_smt.d_theoryEngine->solve(learnedLiteral, newSubstitutions);

    switch (solveStatus) {
      case Theory::PP_ASSERT_STATUS_SOLVED: {
        // The literal should rewrite to true
        Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                          << "solved " << learnedLiteral << endl;
        Assert(Rewriter::rewrite(newSubstitutions.apply(learnedLiteral)).isConst());
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
        Assert(!options::unsatCores());
        d_assertions.clear();
        addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false);
        d_propagatorNeedsFinish = true;
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
          Assert(newSubstitutions.apply(t) == t);
          constantPropagations.addSubstitution(t, c);
          // vector<pair<Node,Node> > equations;
          // constantPropagations.simplifyLHS(t, c, equations, true);
          // if (!equations.empty()) {
          //   Assert(equations[0].first.isConst() && equations[0].second.isConst() && equations[0].first != equations[0].second);
          //   d_assertions.clear();
          //   addFormula(NodeManager::currentNM()->mkConst<bool>(false), false, false);
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
  }

#ifdef CVC4_ASSERTIONS
  // NOTE: When debugging this code, consider moving this check inside of the
  // loop over d_nonClausalLearnedLiterals. This check has been moved outside
  // because it is costly for certain inputs (see bug 508).
  //
  // Check data structure invariants:
  // 1. for each lhs of d_topLevelSubstitutions, does not appear anywhere in rhs of d_topLevelSubstitutions or anywhere in constantPropagations
  // 2. each lhs of constantPropagations rewrites to itself
  // 3. if l -> r is a constant propagation and l is a subterm of l' with l' -> r' another constant propagation, then l'[l/r] -> r' should be a
  //    constant propagation too
  // 4. each lhs of constantPropagations is different from each rhs
  for (pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos) {
    Assert((*pos).first.isVar());
    Assert(d_topLevelSubstitutions.apply((*pos).first) == (*pos).first);
    Assert(d_topLevelSubstitutions.apply((*pos).second) == (*pos).second);
    Assert(newSubstitutions.apply(newSubstitutions.apply((*pos).second)) == newSubstitutions.apply((*pos).second));
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
#endif /* CVC4_ASSERTIONS */

  // Resize the learnt
  Trace("simplify") << "Resize non-clausal learned literals to " << j << std::endl;
  d_nonClausalLearnedLiterals.resize(j);

  unordered_set<TNode, TNodeHashFunction> s;
  Trace("debugging") << "NonClausal simplify pre-preprocess\n";
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    Node assertion = d_assertions[i];
    Node assertionNew = newSubstitutions.apply(assertion);
    Trace("debugging") << "assertion = " << assertion << endl;
    Trace("debugging") << "assertionNew = " << assertionNew << endl;
    if (assertion != assertionNew) {
      assertion = Rewriter::rewrite(assertionNew);
      Trace("debugging") << "rewrite(assertion) = " << assertion << endl;
    }
    Assert(Rewriter::rewrite(assertion) == assertion);
    for (;;) {
      assertionNew = constantPropagations.apply(assertion);
      if (assertionNew == assertion) {
        break;
      }
      ++d_smt.d_stats->d_numConstantProps;
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
      assertion = Rewriter::rewrite(assertionNew);
      Trace("debugging") << "assertionNew = " << assertionNew << endl;
    }
    Trace("debugging") << "\n";
    s.insert(assertion);
    d_assertions.replace(i, assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: "
                      << assertion << endl;
  }

  // If in incremental mode, add substitutions to the list of assertions
  if (d_substitutionsIndex > 0) {
    NodeBuilder<> substitutionsBuilder(kind::AND);
    substitutionsBuilder << d_assertions[d_substitutionsIndex];
    pos = newSubstitutions.begin();
    for (; pos != newSubstitutions.end(); ++pos) {
      // Add back this substitution as an assertion
      TNode lhs = (*pos).first, rhs = newSubstitutions.apply((*pos).second);
      Node n = NodeManager::currentNM()->mkNode(kind::EQUAL, lhs, rhs);
      substitutionsBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will notify SAT layer of substitution: " << n << endl;
    }
    if (substitutionsBuilder.getNumChildren() > 1) {
      d_assertions.replace(d_substitutionsIndex,
        Rewriter::rewrite(Node(substitutionsBuilder)));
    }
  } else {
    // If not in incremental mode, must add substitutions to model
    TheoryModel* m = d_smt.d_theoryEngine->getModel();
    if(m != NULL) {
      for(pos = newSubstitutions.begin(); pos != newSubstitutions.end(); ++pos) {
        Node n = (*pos).first;
        Node v = newSubstitutions.apply((*pos).second);
        Trace("model") << "Add substitution : " << n << " " << v << endl;
        m->addSubstitution( n, v );
      }
    }
  }

  NodeBuilder<> learnedBuilder(kind::AND);
  Assert(d_realAssertionsEnd <= d_assertions.size());
  learnedBuilder << d_assertions[d_realAssertionsEnd - 1];

  for (unsigned i = 0; i < d_nonClausalLearnedLiterals.size(); ++ i) {
    Node learned = d_nonClausalLearnedLiterals[i];
    Assert(d_topLevelSubstitutions.apply(learned) == learned);
    Node learnedNew = newSubstitutions.apply(learned);
    if (learned != learnedNew) {
      learned = Rewriter::rewrite(learnedNew);
    }
    Assert(Rewriter::rewrite(learned) == learned);
    for (;;) {
      learnedNew = constantPropagations.apply(learned);
      if (learnedNew == learned) {
        break;
      }
      ++d_smt.d_stats->d_numConstantProps;
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

  for (pos = constantPropagations.begin(); pos != constantPropagations.end(); ++pos) {
    Node cProp = (*pos).first.eqNode((*pos).second);
    Assert(d_topLevelSubstitutions.apply(cProp) == cProp);
    Node cPropNew = newSubstitutions.apply(cProp);
    if (cProp != cPropNew) {
      cProp = Rewriter::rewrite(cPropNew);
      Assert(Rewriter::rewrite(cProp) == cProp);
    }
    if (s.find(cProp) != s.end()) {
      continue;
    }
    s.insert(cProp);
    learnedBuilder << cProp;
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal constant propagation : "
                      << cProp << endl;
  }

  // Add new substitutions to topLevelSubstitutions
  // Note that we don't have to keep rhs's in full solved form
  // because SubstitutionMap::apply does a fixed-point iteration when substituting
  d_topLevelSubstitutions.addSubstitutions(newSubstitutions);

  if(learnedBuilder.getNumChildren() > 1) {
    d_assertions.replace(d_realAssertionsEnd - 1,
      Rewriter::rewrite(Node(learnedBuilder)));
  }

  d_propagatorNeedsFinish = true;
  return true;
}

void SmtEnginePrivate::bvAbstraction() {
  Trace("bv-abstraction") << "SmtEnginePrivate::bvAbstraction()" << endl;
  std::vector<Node> new_assertions;
  bool changed = d_smt.d_theoryEngine->ppBvAbstraction(d_assertions.ref(), new_assertions);
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    d_assertions.replace(i, Rewriter::rewrite(new_assertions[i]));
  }
  // if we are using the lazy solver and the abstraction
  // applies, then UF symbols were introduced
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY &&
      changed) {
    LogicRequest req(d_smt);
    req.widenLogic(THEORY_UF);
  }
}


void SmtEnginePrivate::bvToBool() {
  Trace("bv-to-bool") << "SmtEnginePrivate::bvToBool()" << endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_smt.d_theoryEngine->ppBvToBool(d_assertions.ref(), new_assertions);
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    d_assertions.replace(i, Rewriter::rewrite(new_assertions[i]));
  }
}

void SmtEnginePrivate::boolToBv() {
  Trace("bool-to-bv") << "SmtEnginePrivate::boolToBv()" << endl;
  spendResource(options::preprocessStep());
  std::vector<Node> new_assertions;
  d_smt.d_theoryEngine->ppBoolToBv(d_assertions.ref(), new_assertions);
  for (unsigned i = 0; i < d_assertions.size(); ++ i) {
    d_assertions.replace(i, Rewriter::rewrite(new_assertions[i]));
  }
}

bool SmtEnginePrivate::simpITE() {
  TimerStat::CodeTimer simpITETimer(d_smt.d_stats->d_simpITETime);

  spendResource(options::preprocessStep());

  Trace("simplify") << "SmtEnginePrivate::simpITE()" << endl;

  unsigned numAssertionOnEntry = d_assertions.size();
  for (unsigned i = 0; i < d_assertions.size(); ++i) {
    spendResource(options::preprocessStep());
    Node result = d_smt.d_theoryEngine->ppSimpITE(d_assertions[i]);
    d_assertions.replace(i, result);
    if(result.isConst() && !result.getConst<bool>()){
      return false;
    }
  }
  bool result = d_smt.d_theoryEngine->donePPSimpITE(d_assertions.ref());
  if(numAssertionOnEntry < d_assertions.size()){
    compressBeforeRealAssertions(numAssertionOnEntry);
  }
  return result;
}

void SmtEnginePrivate::compressBeforeRealAssertions(size_t before){
  size_t curr = d_assertions.size();
  if(before >= curr ||
     d_realAssertionsEnd <= 0 ||
     d_realAssertionsEnd >= curr){
    return;
  }

  // assertions
  // original: [0 ... d_realAssertionsEnd)
  //  can be modified
  // ites skolems [d_realAssertionsEnd, before)
  //  cannot be moved
  // added [before, curr)
  //  can be modified
  Assert(0 < d_realAssertionsEnd);
  Assert(d_realAssertionsEnd <= before);
  Assert(before < curr);

  std::vector<Node> intoConjunction;
  for(size_t i = before; i<curr; ++i){
    intoConjunction.push_back(d_assertions[i]);
  }
  d_assertions.resize(before);
  size_t lastBeforeItes = d_realAssertionsEnd - 1;
  intoConjunction.push_back(d_assertions[lastBeforeItes]);
  Node newLast = util::NaryBuilder::mkAssoc(kind::AND, intoConjunction);
  d_assertions.replace(lastBeforeItes, newLast);
  Assert(d_assertions.size() == before);
}

void SmtEnginePrivate::unconstrainedSimp() {
  TimerStat::CodeTimer unconstrainedSimpTimer(d_smt.d_stats->d_unconstrainedSimpTime);
  spendResource(options::preprocessStep());
  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << endl;
  d_smt.d_theoryEngine->ppUnconstrainedSimp(d_assertions.ref());
}

void SmtEnginePrivate::traceBackToAssertions(const std::vector<Node>& nodes, std::vector<TNode>& assertions) {
  const booleans::CircuitPropagator::BackEdgesMap& backEdges = d_propagator.getBackEdges();
  for(vector<Node>::const_iterator i = nodes.begin(); i != nodes.end(); ++i) {
    booleans::CircuitPropagator::BackEdgesMap::const_iterator j = backEdges.find(*i);
    // term must appear in map, otherwise how did we get here?!
    Assert(j != backEdges.end());
    // if term maps to empty, that means it's a top-level assertion
    if(!(*j).second.empty()) {
      traceBackToAssertions((*j).second, assertions);
    } else {
      assertions.push_back(*i);
    }
  }
}

size_t SmtEnginePrivate::removeFromConjunction(Node& n, const std::unordered_set<unsigned long>& toRemove) {
  Assert(n.getKind() == kind::AND);
  size_t removals = 0;
  for(Node::iterator j = n.begin(); j != n.end(); ++j) {
    size_t subremovals = 0;
    Node sub = *j;
    if(toRemove.find(sub.getId()) != toRemove.end() ||
       (sub.getKind() == kind::AND && (subremovals = removeFromConjunction(sub, toRemove)) > 0)) {
      NodeBuilder<> b(kind::AND);
      b.append(n.begin(), j);
      if(subremovals > 0) {
        removals += subremovals;
        b << sub;
      } else {
        ++removals;
      }
      for(++j; j != n.end(); ++j) {
        if(toRemove.find((*j).getId()) != toRemove.end()) {
          ++removals;
        } else if((*j).getKind() == kind::AND) {
          sub = *j;
          if((subremovals = removeFromConjunction(sub, toRemove)) > 0) {
            removals += subremovals;
            b << sub;
          } else {
            b << *j;
          }
        } else {
          b << *j;
        }
      }
      if(b.getNumChildren() == 0) {
        n = d_true;
        b.clear();
      } else if(b.getNumChildren() == 1) {
        n = b[0];
        b.clear();
      } else {
        n = b;
      }
      n = Rewriter::rewrite(n);
      return removals;
    }
  }

  Assert(removals == 0);
  return 0;
}

void SmtEnginePrivate::doMiplibTrick() {
  Assert(d_realAssertionsEnd == d_assertions.size());
  Assert(!options::incrementalSolving());

  const booleans::CircuitPropagator::BackEdgesMap& backEdges = d_propagator.getBackEdges();
  unordered_set<unsigned long> removeAssertions;

  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(Rational(0)), one = nm->mkConst(Rational(1));

  unordered_map<TNode, Node, TNodeHashFunction> intVars;
  for(vector<Node>::const_iterator i = d_boolVars.begin(); i != d_boolVars.end(); ++i) {
    if(d_propagator.isAssigned(*i)) {
      Debug("miplib") << "ineligible: " << *i << " because assigned " << d_propagator.getAssignment(*i) << endl;
      continue;
    }

    vector<TNode> assertions;
    booleans::CircuitPropagator::BackEdgesMap::const_iterator j = backEdges.find(*i);
    // if not in back edges map, the bool var is unconstrained, showing up in no assertions.
    // if maps to an empty vector, that means the bool var was asserted itself.
    if(j != backEdges.end()) {
      if(!(*j).second.empty()) {
        traceBackToAssertions((*j).second, assertions);
      } else {
        assertions.push_back(*i);
      }
    }
    Debug("miplib") << "for " << *i << endl;
    bool eligible = true;
    map<pair<Node, Node>, uint64_t> marks;
    map<pair<Node, Node>, vector<Rational> > coef;
    map<pair<Node, Node>, vector<Rational> > checks;
    map<pair<Node, Node>, vector<TNode> > asserts;
    for(vector<TNode>::const_iterator j = assertions.begin(); j != assertions.end(); ++j) {
      Debug("miplib") << "  found: " << *j << endl;
      if((*j).getKind() != kind::IMPLIES) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not =>)" << endl;
        break;
      }
      Node conj = BooleanSimplification::simplify((*j)[0]);
      if(conj.getKind() == kind::AND && conj.getNumChildren() > 6) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (N-ary /\\ too big)" << endl;
        break;
      }
      if(conj.getKind() != kind::AND && !conj.isVar() && !(conj.getKind() == kind::NOT && conj[0].isVar())) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (not /\\ or literal)" << endl;
        break;
      }
      if((*j)[1].getKind() != kind::EQUAL ||
         !( ( (*j)[1][0].isVar() &&
              (*j)[1][1].getKind() == kind::CONST_RATIONAL ) ||
            ( (*j)[1][0].getKind() == kind::CONST_RATIONAL &&
              (*j)[1][1].isVar() ) )) {
        eligible = false;
        Debug("miplib") << "  -- INELIGIBLE -- (=> (and X X) X)" << endl;
        break;
      }
      if(conj.getKind() == kind::AND) {
        vector<Node> posv;
        bool found_x = false;
        map<TNode, bool> neg;
        for(Node::iterator ii = conj.begin(); ii != conj.end(); ++ii) {
          if((*ii).isVar()) {
            posv.push_back(*ii);
            neg[*ii] = false;
            found_x = found_x || *i == *ii;
          } else if((*ii).getKind() == kind::NOT && (*ii)[0].isVar()) {
            posv.push_back((*ii)[0]);
            neg[(*ii)[0]] = true;
            found_x = found_x || *i == (*ii)[0];
          } else {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (non-var: " << *ii << ")" << endl;
            break;
          }
          if(d_propagator.isAssigned(posv.back())) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (" << posv.back() << " asserted)" << endl;
            break;
          }
        }
        if(!eligible) {
          break;
        }
        if(!found_x) {
          eligible = false;
          Debug("miplib") << "  --INELIGIBLE -- (couldn't find " << *i << " in conjunction)" << endl;
          break;
        }
        sort(posv.begin(), posv.end());
        const Node pos = NodeManager::currentNM()->mkNode(kind::AND, posv);
        const TNode var = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][1] : (*j)[1][0];
        const pair<Node, Node> pos_var(pos, var);
        const Rational& constant = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][0].getConst<Rational>() : (*j)[1][1].getConst<Rational>();
        uint64_t mark = 0;
        unsigned countneg = 0, thepos = 0;
        for(unsigned ii = 0; ii < pos.getNumChildren(); ++ii) {
          if(neg[pos[ii]]) {
            ++countneg;
          } else {
            thepos = ii;
            mark |= (0x1 << ii);
          }
        }
        if((marks[pos_var] & (1lu << mark)) != 0) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        Debug("miplib") << "mark is " << mark << " -- " << (1lu << mark) << endl;
        marks[pos_var] |= (1lu << mark);
        Debug("miplib") << "marks[" << pos << "," << var << "] now " << marks[pos_var] << endl;
        if(countneg == pos.getNumChildren()) {
          if(constant != 0) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        } else if(countneg == pos.getNumChildren() - 1) {
          Assert(coef[pos_var].size() <= 6 && thepos < 6);
          if(coef[pos_var].size() <= thepos) {
            coef[pos_var].resize(thepos + 1);
          }
          coef[pos_var][thepos] = constant;
        } else {
          if(checks[pos_var].size() <= mark) {
            checks[pos_var].resize(mark + 1);
          }
          checks[pos_var][mark] = constant;
        }
        asserts[pos_var].push_back(*j);
      } else {
        TNode x = conj;
        if(x != *i && x != (*i).notNode()) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (x not present where I expect it)" << endl;
          break;
        }
        const bool xneg = (x.getKind() == kind::NOT);
        x = xneg ? x[0] : x;
        Debug("miplib") << "  x:" << x << "  " << xneg << endl;
        const TNode var = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][1] : (*j)[1][0];
        const pair<Node, Node> x_var(x, var);
        const Rational& constant = ((*j)[1][0].getKind() == kind::CONST_RATIONAL) ? (*j)[1][0].getConst<Rational>() : (*j)[1][1].getConst<Rational>();
        unsigned mark = (xneg ? 0 : 1);
        if((marks[x_var] & (1u << mark)) != 0) {
          eligible = false;
          Debug("miplib") << "  -- INELIGIBLE -- (remarked)" << endl;
          break;
        }
        marks[x_var] |= (1u << mark);
        if(xneg) {
          if(constant != 0) {
            eligible = false;
            Debug("miplib") << "  -- INELIGIBLE -- (nonzero constant)" << endl;
            break;
          }
        } else {
          Assert(coef[x_var].size() <= 6);
          coef[x_var].resize(6);
          coef[x_var][0] = constant;
        }
        asserts[x_var].push_back(*j);
      }
    }
    if(eligible) {
      for(map<pair<Node, Node>, uint64_t>::const_iterator j = marks.begin(); j != marks.end(); ++j) {
        const TNode pos = (*j).first.first;
        const TNode var = (*j).first.second;
        const pair<Node, Node>& pos_var = (*j).first;
        const uint64_t mark = (*j).second;
        const unsigned numVars = pos.getKind() == kind::AND ? pos.getNumChildren() : 1;
        uint64_t expected = (uint64_t(1) << (1 << numVars)) - 1;
        expected = (expected == 0) ? -1 : expected; // fix for overflow
        Debug("miplib") << "[" << pos << "] => " << hex << mark << " expect " << expected << dec << endl;
        Assert(pos.getKind() == kind::AND || pos.isVar());
        if(mark != expected) {
          Debug("miplib") << "  -- INELIGIBLE " << pos << " -- (insufficiently marked, got " << mark << " for " << numVars << " vars, expected " << expected << endl;
        } else {
          if(mark != 3) { // exclude single-var case; nothing to check there
            uint64_t sz = (uint64_t(1) << checks[pos_var].size()) - 1;
            sz = (sz == 0) ? -1 : sz; // fix for overflow
            Assert(sz == mark, "expected size %u == mark %u", sz, mark);
            for(size_t k = 0; k < checks[pos_var].size(); ++k) {
              if((k & (k - 1)) != 0) {
                Rational sum = 0;
                Debug("miplib") << k << " => " << checks[pos_var][k] << endl;
                for(size_t v = 1, kk = k; kk != 0; ++v, kk >>= 1) {
                  if((kk & 0x1) == 1) {
                    Assert(pos.getKind() == kind::AND);
                    Debug("miplib") << "var " << v << " : " << pos[v - 1] << " coef:" << coef[pos_var][v - 1] << endl;
                    sum += coef[pos_var][v - 1];
                  }
                }
                Debug("miplib") << "checkSum is " << sum << " input says " << checks[pos_var][k] << endl;
                if(sum != checks[pos_var][k]) {
                  eligible = false;
                  Debug("miplib") << "  -- INELIGIBLE " << pos << " -- (nonlinear combination)" << endl;
                  break;
                }
              } else {
                Assert(checks[pos_var][k] == 0, "checks[(%s,%s)][%u] should be 0, but it's %s", pos.toString().c_str(), var.toString().c_str(), k, checks[pos_var][k].toString().c_str()); // we never set for single-positive-var
              }
            }
          }
          if(!eligible) {
            eligible = true; // next is still eligible
            continue;
          }

          Debug("miplib") << "  -- ELIGIBLE " << *i << " , " << pos << " --" << endl;
          vector<Node> newVars;
          expr::NodeSelfIterator ii, iiend;
          if(pos.getKind() == kind::AND) {
            ii = pos.begin();
            iiend = pos.end();
          } else {
            ii = expr::NodeSelfIterator::self(pos);
            iiend = expr::NodeSelfIterator::selfEnd(pos);
          }
          for(; ii != iiend; ++ii) {
            Node& varRef = intVars[*ii];
            if(varRef.isNull()) {
              stringstream ss;
              ss << "mipvar_" << *ii;
              Node newVar = nm->mkSkolem(ss.str(), nm->integerType(), "a variable introduced due to scrubbing a miplib encoding", NodeManager::SKOLEM_EXACT_NAME);
              Node geq = Rewriter::rewrite(nm->mkNode(kind::GEQ, newVar, zero));
              Node leq = Rewriter::rewrite(nm->mkNode(kind::LEQ, newVar, one));
              addFormula(Rewriter::rewrite(geq.andNode(leq)), false, false);
              SubstitutionMap nullMap(&d_fakeContext);
              Theory::PPAssertStatus status CVC4_UNUSED; // just for assertions
              status = d_smt.d_theoryEngine->solve(geq, nullMap);
              Assert(status == Theory::PP_ASSERT_STATUS_UNSOLVED,
                     "unexpected solution from arith's ppAssert()");
              Assert(nullMap.empty(),
                     "unexpected substitution from arith's ppAssert()");
              status = d_smt.d_theoryEngine->solve(leq, nullMap);
              Assert(status == Theory::PP_ASSERT_STATUS_UNSOLVED,
                     "unexpected solution from arith's ppAssert()");
              Assert(nullMap.empty(),
                     "unexpected substitution from arith's ppAssert()");
              d_smt.d_theoryEngine->getModel()->addSubstitution(*ii, newVar.eqNode(one));
              newVars.push_back(newVar);
              varRef = newVar;
            } else {
              newVars.push_back(varRef);
            }
            if(!d_smt.d_logic.areIntegersUsed()) {
              d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
              d_smt.d_logic.enableIntegers();
              d_smt.d_logic.lock();
            }
          }
          Node sum;
          if(pos.getKind() == kind::AND) {
            NodeBuilder<> sumb(kind::PLUS);
            for(size_t ii = 0; ii < pos.getNumChildren(); ++ii) {
              sumb << nm->mkNode(kind::MULT, nm->mkConst(coef[pos_var][ii]), newVars[ii]);
            }
            sum = sumb;
          } else {
            sum = nm->mkNode(kind::MULT, nm->mkConst(coef[pos_var][0]), newVars[0]);
          }
          Debug("miplib") << "vars[] " << var << endl
                          << "    eq " << Rewriter::rewrite(sum) << endl;
          Node newAssertion = var.eqNode(Rewriter::rewrite(sum));
          if(d_topLevelSubstitutions.hasSubstitution(newAssertion[0])) {
            //Warning() << "RE-SUBSTITUTION " << newAssertion[0] << endl;
            //Warning() << "REPLACE         " << newAssertion[1] << endl;
            //Warning() << "ORIG            " << d_topLevelSubstitutions.getSubstitution(newAssertion[0]) << endl;
            Assert(d_topLevelSubstitutions.getSubstitution(newAssertion[0]) == newAssertion[1]);
          } else if(pos.getNumChildren() <= options::arithMLTrickSubstitutions()) {
            d_topLevelSubstitutions.addSubstitution(newAssertion[0], newAssertion[1]);
            Debug("miplib") << "addSubs: " << newAssertion[0] << " to " << newAssertion[1] << endl;
          } else {
            Debug("miplib") << "skipSubs: " << newAssertion[0] << " to " << newAssertion[1] << " (threshold is " << options::arithMLTrickSubstitutions() << ")" << endl;
          }
          newAssertion = Rewriter::rewrite(newAssertion);
          Debug("miplib") << "  " << newAssertion << endl;
          addFormula(newAssertion, false, false);
          Debug("miplib") << "  assertions to remove: " << endl;
          for(vector<TNode>::const_iterator k = asserts[pos_var].begin(), k_end = asserts[pos_var].end(); k != k_end; ++k) {
            Debug("miplib") << "    " << *k << endl;
            removeAssertions.insert((*k).getId());
          }
        }
      }
    }
  }
  if(!removeAssertions.empty()) {
    Debug("miplib") << "SmtEnginePrivate::simplify(): scrubbing miplib encoding..." << endl;
    for(size_t i = 0; i < d_realAssertionsEnd; ++i) {
      if(removeAssertions.find(d_assertions[i].getId()) != removeAssertions.end()) {
        Debug("miplib") << "SmtEnginePrivate::simplify(): - removing " << d_assertions[i] << endl;
        d_assertions[i] = d_true;
        ++d_smt.d_stats->d_numMiplibAssertionsRemoved;
      } else if(d_assertions[i].getKind() == kind::AND) {
        size_t removals = removeFromConjunction(d_assertions[i], removeAssertions);
        if(removals > 0) {
          Debug("miplib") << "SmtEnginePrivate::simplify(): - reduced " << d_assertions[i] << endl;
          Debug("miplib") << "SmtEnginePrivate::simplify(): -      by " << removals << " conjuncts" << endl;
          d_smt.d_stats->d_numMiplibAssertionsRemoved += removals;
        }
      }
      Debug("miplib") << "had: " << d_assertions[i] << endl;
      d_assertions[i] = Rewriter::rewrite(d_topLevelSubstitutions.apply(d_assertions[i]));
      Debug("miplib") << "now: " << d_assertions[i] << endl;
    }
  } else {
    Debug("miplib") << "SmtEnginePrivate::simplify(): miplib pass found nothing." << endl;
  }
  d_realAssertionsEnd = d_assertions.size();
}


// returns false if simplification led to "false"
bool SmtEnginePrivate::simplifyAssertions()
{
  spendResource(options::preprocessStep());
  Assert(d_smt.d_pendingPops == 0);
  try {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

    dumpAssertions("pre-nonclausal", d_assertions);

    if(options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      // Perform non-clausal simplification
      Chat() << "...performing nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << "performing non-clausal simplification" << endl;
      bool noConflict = nonClausalSimplify();
      if(!noConflict) {
        return false;
      }

      // We piggy-back off of the BackEdgesMap in the CircuitPropagator to
      // do the miplib trick.
      if( // check that option is on
          options::arithMLTrick() &&
          // miplib rewrites aren't safe in incremental mode
          ! options::incrementalSolving() &&
          // only useful in arith
          d_smt.d_logic.isTheoryEnabled(THEORY_ARITH) &&
          // we add new assertions and need this (in practice, this
          // restriction only disables miplib processing during
          // re-simplification, which we don't expect to be useful anyway)
          d_realAssertionsEnd == d_assertions.size() ) {
        Chat() << "...fixing miplib encodings..." << endl;
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "looking for miplib pseudobooleans..." << endl;

        TimerStat::CodeTimer miplibTimer(d_smt.d_stats->d_miplibPassTime);

        doMiplibTrick();
      } else {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass (either incrementalSolving is on, or miplib pbs are turned off)..." << endl;
      }
    }

    dumpAssertions("post-nonclausal", d_assertions);
    Trace("smt") << "POST nonClausalSimplify" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // before ppRewrite check if only core theory for BV theory
    d_smt.d_theoryEngine->staticInitializeBVOptions(d_assertions.ref());

    dumpAssertions("pre-theorypp", d_assertions);

    // Theory preprocessing
    if (d_smt.d_earlyTheoryPP) {
      Chat() << "...doing early theory preprocessing..." << endl;
      TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
      // Call the theory preprocessors
      d_smt.d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < d_assertions.size(); ++ i) {
        Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
        d_assertions.replace(i, d_smt.d_theoryEngine->preprocess(d_assertions[i]));
        Assert(Rewriter::rewrite(d_assertions[i]) == d_assertions[i]);
      }
    }

    dumpAssertions("post-theorypp", d_assertions);
    Trace("smt") << "POST theoryPP" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // ITE simplification
    if(options::doITESimp() &&
       (d_simplifyAssertionsDepth <= 1 || options::doITESimpOnRepeat())) {
      Chat() << "...doing ITE simplification..." << endl;
      bool noConflict = simpITE();
      if(!noConflict){
        Chat() << "...ITE simplification found unsat..." << endl;
        return false;
      }
    }

    dumpAssertions("post-itesimp", d_assertions);
    Trace("smt") << "POST iteSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    // Unconstrained simplification
    if(options::unconstrainedSimp()) {
      Chat() << "...doing unconstrained simplification..." << endl;
      unconstrainedSimp();
    }

    dumpAssertions("post-unconstrained", d_assertions);
    Trace("smt") << "POST unconstrainedSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

    if(options::repeatSimp() && options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      Chat() << "...doing another round of nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << " doing repeated simplification" << endl;
      bool noConflict = nonClausalSimplify();
      if(!noConflict) {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", d_assertions);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  } catch(TypeCheckingExceptionPrivate& tcep) {
    // Calls to this function should have already weeded out any
    // typechecking exceptions via (e.g.) ensureBoolean().  But a
    // theory could still create a new expression that isn't
    // well-typed, and we don't want the C++ runtime to abort our
    // process without any error notice.
    stringstream ss;
    ss << "A bad expression was produced.  Original exception follows:\n"
       << tcep;
    InternalError(ss.str().c_str());
  }
  return true;
}

Result SmtEngine::check() {
  Assert(d_fullyInited);
  Assert(d_pendingPops == 0);

  Trace("smt") << "SmtEngine::check()" << endl;

  ResourceManager* resourceManager = d_private->getResourceManager();

  resourceManager->beginCall();

  // Only way we can be out of resource is if cumulative budget is on
  if (resourceManager->cumulativeLimitOn() &&
      resourceManager->out()) {
    Result::UnknownExplanation why = resourceManager->outOfResources() ?
                             Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::VALIDITY_UNKNOWN, why, d_filename);
  }

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  d_private->processAssertions();
  Trace("smt") << "SmtEngine::check(): done processing assertions" << endl;

  // Turn off stop only for QF_LRA
  // TODO: Bring up in a meeting where to put this
  if(options::decisionStopOnly() && !options::decisionMode.wasSetByUser() ){
    if( // QF_LRA
       (not d_logic.isQuantified() &&
        d_logic.isPure(THEORY_ARITH) && d_logic.isLinear() && !d_logic.isDifferenceLogic() &&  !d_logic.areIntegersUsed()
        )){
      if(d_private->d_iteSkolemMap.empty()){
        options::decisionStopOnly.set(false);
        d_decisionEngine->clearStrategies();
        Trace("smt") << "SmtEngine::check(): turning off stop only" << endl;
      }
    }
  }

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat();

  resourceManager->endCall();
  Trace("limit") << "SmtEngine::check(): cumulative millis " << resourceManager->getTimeUsage()
                 << ", resources " << resourceManager->getResourceUsage() << endl;


  return Result(result, d_filename);
}

Result SmtEngine::quickCheck() {
  Assert(d_fullyInited);
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN, Result::REQUIRES_FULL_CHECK, d_filename);
}


void SmtEnginePrivate::collectSkolems(TNode n, set<TNode>& skolemSet, unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = d_iteSkolemMap.find(n);
    if (it != d_iteSkolemMap.end()) {
      skolemSet.insert(n);
    }
    cache[n] = true;
    return;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    collectSkolems(n[k], skolemSet, cache);
  }
  cache[n] = true;
}


bool SmtEnginePrivate::checkForBadSkolems(TNode n, TNode skolem, unordered_map<Node, bool, NodeHashFunction>& cache)
{
  unordered_map<Node, bool, NodeHashFunction>::iterator it;
  it = cache.find(n);
  if (it != cache.end()) {
    return (*it).second;
  }

  size_t sz = n.getNumChildren();
  if (sz == 0) {
    IteSkolemMap::iterator it = d_iteSkolemMap.find(n);
    bool bad = false;
    if (it != d_iteSkolemMap.end()) {
      if (!((*it).first < n)) {
        bad = true;
      }
    }
    cache[n] = bad;
    return bad;
  }

  size_t k = 0;
  for (; k < sz; ++k) {
    if (checkForBadSkolems(n[k], skolem, cache)) {
      cache[n] = true;
      return true;
    }
  }

  cache[n] = false;
  return false;
}

void SmtEnginePrivate::applySubstitutionsToAssertions() {
  if(!options::unsatCores()) {
    Chat() << "applying substitutions..." << endl;
    Trace("simplify") << "SmtEnginePrivate::processAssertions(): "
                      << "applying substitutions" << endl;
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    // When solving incrementally, all substitutions are piled into the
    // assertion at d_substitutionsIndex: we don't want to apply substitutions
    // to this assertion or information will be lost.
    unsigned substitutionAssertion = d_substitutionsIndex > 0 ? d_substitutionsIndex : d_assertions.size();
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      if (i == substitutionAssertion) {
        continue;
      }
      Trace("simplify") << "applying to " << d_assertions[i] << endl;
      spendResource(options::preprocessStep());
      d_assertions.replace(i, Rewriter::rewrite(d_topLevelSubstitutions.apply(d_assertions[i])));
      Trace("simplify") << "  got " << d_assertions[i] << endl;
    }
  }
}

void SmtEnginePrivate::processAssertions() {
  TimerStat::CodeTimer paTimer(d_smt.d_stats->d_processAssertionsTime);
  spendResource(options::preprocessStep());
  Assert(d_smt.d_fullyInited);
  Assert(d_smt.d_pendingPops == 0);

  // Dump the assertions
  dumpAssertions("pre-everything", d_assertions);

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() begin" << endl;
  Trace("smt") << "SmtEnginePrivate::processAssertions()" << endl;

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  if (d_assertions.size() == 0) {
    // nothing to do
    return;
  }

  if(options::bvGaussElim())
  {
    TimerStat::CodeTimer gaussElimTimer(d_smt.d_stats->d_gaussElimTime);
    theory::bv::BVGaussElim::gaussElimRewrite(d_assertions.ref());
  }

  if (d_assertionsProcessed && options::incrementalSolving()) {
    // TODO(b/1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    // Placeholder for storing substitutions
    d_substitutionsIndex = d_assertions.size();
    d_assertions.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  d_assertions.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  // any assertions added beyond realAssertionsEnd must NOT affect the
  // equisatisfiability
  d_realAssertionsEnd = d_assertions.size();

  // Assertions are NOT guaranteed to be rewritten by this point

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-definition-expansion" << endl;
  dumpAssertions("pre-definition-expansion", d_assertions);
  {
    Chat() << "expanding definitions..." << endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_definitionExpansionTime);
    unordered_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, expandDefinitions(d_assertions[i], cache));
    }
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-definition-expansion" << endl;
  dumpAssertions("post-definition-expansion", d_assertions);

  // save the assertions now
  THEORY_PROOF
    (
     for (unsigned i = 0; i < d_assertions.size(); ++i) {
       ProofManager::currentPM()->addAssertion(d_assertions[i].toExpr());
     }
     );

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  // global negation of the formula
  if (options::globalNegate())
  {
    quantifiers::GlobalNegate gn;
    gn.simplify(d_assertions.ref());
    d_smt.d_globalNegation = !d_smt.d_globalNegation;
  }

  if( options::nlExtPurify() ){
    unordered_map<Node, Node, NodeHashFunction> cache;
    unordered_map<Node, Node, NodeHashFunction> bcache;
    std::vector< Node > var_eq;
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, purifyNlTerms(d_assertions[i], cache, bcache, var_eq));
    }
    if( !var_eq.empty() ){
      unsigned lastIndex = d_assertions.size()-1;
      var_eq.insert( var_eq.begin(), d_assertions[lastIndex] );
      d_assertions.replace(lastIndex, NodeManager::currentNM()->mkNode( kind::AND, var_eq ) );
    }
  }

  if( options::ceGuidedInst() ){
    //register sygus conjecture pre-rewrite (motivated by solution reconstruction)
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_smt.d_theoryEngine->getQuantifiersEngine()->getCegInstantiation()->preregisterAssertion( d_assertions[i] );
    }
  }

  if (options::solveRealAsInt()) {
    Chat() << "converting reals to ints..." << endl;
    unordered_map<Node, Node, NodeHashFunction> cache;
    std::vector< Node > var_eq;
    for(unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, realToInt(d_assertions[i], cache, var_eq));
    }
   /*
    if( !var_eq.empty() ){
      unsigned lastIndex = d_assertions.size()-1;
      var_eq.insert( var_eq.begin(), d_assertions[lastIndex] );
      d_assertions.replace(last_index, NodeManager::currentNM()->mkNode( kind::AND, var_eq ) );
    }
    */
  }

  if (options::solveIntAsBV() > 0) {
    Chat() << "converting ints to bit-vectors..." << endl;
    unordered_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, intToBV(d_assertions[i], cache));
    }
  }

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER &&
      !d_smt.d_logic.isPure(THEORY_BV) &&
      d_smt.d_logic.getLogicString() != "QF_UFBV" &&
      d_smt.d_logic.getLogicString() != "QF_ABV") {
    throw ModalException("Eager bit-blasting does not currently support theory combination. "
                         "Note that in a QF_BV problem UF symbols can be introduced for division. "
                         "Try --bv-div-zero-const to interpret division by zero as a constant.");
  }

  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    d_smt.d_theoryEngine->mkAckermanizationAssertions(d_assertions.ref());
  }

  if ( options::bvAbstraction() &&
      !options::incrementalSolving()) {
    dumpAssertions("pre-bv-abstraction", d_assertions);
    bvAbstraction();
    dumpAssertions("post-bv-abstraction", d_assertions);
  }

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  bool noConflict = true;

  if (options::extRewPrep())
  {
    theory::quantifiers::ExtendedRewriter extr(options::extRewPrepAgg());
    for (unsigned i = 0; i < d_assertions.size(); ++i)
    {
      Node a = d_assertions[i];
      d_assertions.replace(i, extr.extendedRewrite(a));
    }
  }

  // Unconstrained simplification
  if(options::unconstrainedSimp()) {
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-unconstrained-simp" << endl;
    dumpAssertions("pre-unconstrained-simp", d_assertions);
    Chat() << "...doing unconstrained simplification..." << endl;
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, Rewriter::rewrite(d_assertions[i]));
    }
    unconstrainedSimp();
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-unconstrained-simp" << endl;
    dumpAssertions("post-unconstrained-simp", d_assertions);
  }

  if(options::bvIntroducePow2()){
    theory::bv::BVIntroducePow2::pow2Rewrite(d_assertions.ref());
  }

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-substitution" << endl;
  dumpAssertions("pre-substitution", d_assertions);

  if(options::unsatCores()) {
    // special rewriting pass for unsat cores, since many of the passes below are skipped
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, Rewriter::rewrite(d_assertions[i]));
    }
  } else {
    applySubstitutionsToAssertions();
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-substitution" << endl;
  dumpAssertions("post-substitution", d_assertions);

  // Assertions ARE guaranteed to be rewritten by this point

  // Lift bit-vectors of size 1 to bool
  if(options::bitvectorToBool()) {
    dumpAssertions("pre-bv-to-bool", d_assertions);
    Chat() << "...doing bvToBool..." << endl;
    bvToBool();
    dumpAssertions("post-bv-to-bool", d_assertions);
    Trace("smt") << "POST bvToBool" << endl;
  }
  // Convert non-top-level Booleans to bit-vectors of size 1
  if(options::boolToBitvector()) {
    dumpAssertions("pre-bool-to-bv", d_assertions);
    Chat() << "...doing boolToBv..." << endl;
    boolToBv();
    dumpAssertions("post-bool-to-bv", d_assertions);
    Trace("smt") << "POST boolToBv" << endl;
  }
  if(options::sepPreSkolemEmp()) {
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      Node prev = d_assertions[i];
      Node next = sep::TheorySepRewriter::preprocess( prev );
      if( next!=prev ){
        d_assertions.replace( i, Rewriter::rewrite( next ) );
        Trace("sep-preprocess") << "*** Preprocess sep " << prev << endl;
        Trace("sep-preprocess") << "   ...got " << d_assertions[i] << endl;
      }
    }
  }

  if( d_smt.d_logic.isQuantified() ){
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-quant-preprocess" << endl;

    dumpAssertions("pre-skolem-quant", d_assertions);
    //remove rewrite rules, apply pre-skolemization to existential quantifiers
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      Node prev = d_assertions[i];
      Node next = quantifiers::QuantifiersRewriter::preprocess( prev );
      if( next!=prev ){
        d_assertions.replace( i, Rewriter::rewrite( next ) );
        Trace("quantifiers-preprocess") << "*** Pre-skolemize " << prev << endl;
        Trace("quantifiers-preprocess") << "   ...got " << d_assertions[i] << endl;
      }
    }
    dumpAssertions("post-skolem-quant", d_assertions);
    if( options::macrosQuant() ){
      //quantifiers macro expansion
      quantifiers::QuantifierMacros qm( d_smt.d_theoryEngine->getQuantifiersEngine() );
      bool success;
      do{
        success = qm.simplify( d_assertions.ref(), true );
      }while( success );
      //finalize the definitions
      qm.finalizeDefinitions();
    }

    //fmf-fun : assume admissible functions, applying preprocessing reduction to FMF
    if( options::fmfFunWellDefined() ){
      quantifiers::FunDefFmf fdf;
      Assert( d_smt.d_fmfRecFunctionsDefined!=NULL );
      //must carry over current definitions (for incremental)
      for( context::CDList<Node>::const_iterator fit = d_smt.d_fmfRecFunctionsDefined->begin();
           fit != d_smt.d_fmfRecFunctionsDefined->end(); ++fit ) {
        Node f = (*fit);
        Assert( d_smt.d_fmfRecFunctionsAbs.find( f )!=d_smt.d_fmfRecFunctionsAbs.end() );
        TypeNode ft = d_smt.d_fmfRecFunctionsAbs[f];
        fdf.d_sorts[f] = ft;
        std::map< Node, std::vector< Node > >::iterator fcit = d_smt.d_fmfRecFunctionsConcrete.find( f );
        Assert( fcit!=d_smt.d_fmfRecFunctionsConcrete.end() );
        for( unsigned j=0; j<fcit->second.size(); j++ ){
          fdf.d_input_arg_inj[f].push_back( fcit->second[j] );
        }
      }
      fdf.simplify( d_assertions.ref() );
      //must store new definitions (for incremental)
      for( unsigned i=0; i<fdf.d_funcs.size(); i++ ){
        Node f = fdf.d_funcs[i];
        d_smt.d_fmfRecFunctionsAbs[f] = fdf.d_sorts[f];
        d_smt.d_fmfRecFunctionsConcrete[f].clear();
        for( unsigned j=0; j<fdf.d_input_arg_inj[f].size(); j++ ){
          d_smt.d_fmfRecFunctionsConcrete[f].push_back( fdf.d_input_arg_inj[f][j] );
        }
        d_smt.d_fmfRecFunctionsDefined->push_back( f );
      }
    }
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-quant-preprocess" << endl;
  }

  if( options::sortInference() || options::ufssFairnessMonotone() ){
    //sort inference technique
    SortInference * si = d_smt.d_theoryEngine->getSortInference();
    si->simplify( d_assertions.ref(), options::sortInference(), options::ufssFairnessMonotone() );
    for( std::map< Node, Node >::iterator it = si->d_model_replace_f.begin(); it != si->d_model_replace_f.end(); ++it ){
      d_smt.setPrintFuncInModel( it->first.toExpr(), false );
      d_smt.setPrintFuncInModel( it->second.toExpr(), true );
    }
  }

  if( options::pbRewrites() ){
    d_pbsProcessor.learn(d_assertions.ref());
    if(d_pbsProcessor.likelyToHelp()){
      d_pbsProcessor.applyReplacements(d_assertions.ref());
    }
  }

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-simplify" << endl;
  dumpAssertions("pre-simplify", d_assertions);
  Chat() << "simplifying assertions..." << endl;
  noConflict = simplifyAssertions();
  if(!noConflict){
    ++(d_smt.d_stats->d_simplifiedToFalse);
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-simplify" << endl;
  dumpAssertions("post-simplify", d_assertions);

  dumpAssertions("pre-static-learning", d_assertions);
  if(options::doStaticLearning()) {
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-static-learning" << endl;
    // Perform static learning
    Chat() << "doing static learning..." << endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): "
                      << "performing static learning" << endl;
    staticLearning();
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-static-learning" << endl;
  }
  dumpAssertions("post-static-learning", d_assertions);

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;


  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-ite-removal" << endl;
  dumpAssertions("pre-ite-removal", d_assertions);
  {
    Chat() << "removing term ITEs..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_iteRemovalTime);
    // Remove ITEs, updating d_iteSkolemMap
    d_smt.d_stats->d_numAssertionsPre += d_assertions.size();
    removeITEs();
    // This is needed because when solving incrementally, removeITEs may introduce
    // skolems that were solved for earlier and thus appear in the substitution
    // map.
    applySubstitutionsToAssertions();
    d_smt.d_stats->d_numAssertionsPost += d_assertions.size();
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-ite-removal" << endl;
  dumpAssertions("post-ite-removal", d_assertions);

  dumpAssertions("pre-repeat-simplify", d_assertions);
  if(options::repeatSimp()) {
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-repeat-simplify" << endl;
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions();
    if (noConflict) {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the order in which these variables were introduced
      // during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr mapped to by sk.

      // cache for expression traversal
      unordered_map<Node, bool, NodeHashFunction> cache;

      // First, find all skolems that appear in the substitution map - their associated iteExpr will need
      // to be moved to the main assertion set
      set<TNode> skolemSet;
      SubstitutionMap::iterator pos = d_topLevelSubstitutions.begin();
      for (; pos != d_topLevelSubstitutions.end(); ++pos) {
        collectSkolems((*pos).first, skolemSet, cache);
        collectSkolems((*pos).second, skolemSet, cache);
      }

      // We need to ensure:
      // 1. iteExpr has the form (ite cond (sk = t) (sk = e))
      // 2. if some sk' in Sk appears in cond, t, or e, then sk' <_sk sk
      // If either of these is violated, we must add iteExpr as a proper assertion
      IteSkolemMap::iterator it = d_iteSkolemMap.begin();
      IteSkolemMap::iterator iend = d_iteSkolemMap.end();
      NodeBuilder<> builder(kind::AND);
      builder << d_assertions[d_realAssertionsEnd - 1];
      vector<TNode> toErase;
      for (; it != iend; ++it) {
        if (skolemSet.find((*it).first) == skolemSet.end()) {
          TNode iteExpr = d_assertions[(*it).second];
          if (iteExpr.getKind() == kind::ITE &&
              iteExpr[1].getKind() == kind::EQUAL &&
              iteExpr[1][0] == (*it).first &&
              iteExpr[2].getKind() == kind::EQUAL &&
              iteExpr[2][0] == (*it).first) {
            cache.clear();
            bool bad = checkForBadSkolems(iteExpr[0], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[1][1], (*it).first, cache);
            bad = bad || checkForBadSkolems(iteExpr[2][1], (*it).first, cache);
            if (!bad) {
              continue;
            }
          }
        }
        // Move this iteExpr into the main assertions
        builder << d_assertions[(*it).second];
        d_assertions[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
        toErase.push_back((*it).first);
      }
      if(builder.getNumChildren() > 1) {
        while (!toErase.empty()) {
          d_iteSkolemMap.erase(toErase.back());
          toErase.pop_back();
        }
        d_assertions[d_realAssertionsEnd - 1] = Rewriter::rewrite(Node(builder));
      }
      // TODO(b/1256): For some reason this is needed for some benchmarks, such as
      // http://cvc4.cs.nyu.edu/benchmarks/smtlib2/QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      removeITEs();
      applySubstitutionsToAssertions();
      //      Assert(iteRewriteAssertionsEnd == d_assertions.size());
    }
    Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-repeat-simplify" << endl;
  }
  dumpAssertions("post-repeat-simplify", d_assertions);

  dumpAssertions("pre-rewrite-apply-to-const", d_assertions);
  if(options::rewriteApplyToConst()) {
    Chat() << "Rewriting applies to constants..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_rewriteApplyToConstTime);
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions[i] = Rewriter::rewrite(rewriteApplyToConst(d_assertions[i]));
    }
  }
  dumpAssertions("post-rewrite-apply-to-const", d_assertions);

  // begin: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones
#ifdef CVC4_ASSERTIONS
  unsigned iteRewriteAssertionsEnd = d_assertions.size();
#endif

  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  Debug("smt") << "SmtEnginePrivate::processAssertions() POST SIMPLIFICATION" << endl;
  Debug("smt") << " d_assertions     : " << d_assertions.size() << endl;

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : pre-theory-preprocessing" << endl;
  dumpAssertions("pre-theory-preprocessing", d_assertions);
  {
    Chat() << "theory preprocessing..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
    // Call the theory preprocessors
    d_smt.d_theoryEngine->preprocessStart();
    for (unsigned i = 0; i < d_assertions.size(); ++ i) {
      d_assertions.replace(i, d_smt.d_theoryEngine->preprocess(d_assertions[i]));
    }
  }
  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() : post-theory-preprocessing" << endl;
  dumpAssertions("post-theory-preprocessing", d_assertions);

  // If we are using eager bit-blasting wrap assertions in fake atom so that
  // everything gets bit-blasted to internal SAT solver
  if (options::bitblastMode() == theory::bv::BITBLAST_MODE_EAGER) {
    for (unsigned i = 0; i < d_assertions.size(); ++i) {
      TNode atom = d_assertions[i];
      Node eager_atom = NodeManager::currentNM()->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
      d_assertions.replace(i, eager_atom);
      TheoryModel* m = d_smt.d_theoryEngine->getModel();
      m->addSubstitution(eager_atom, atom);
    }
  }

  //notify theory engine new preprocessed assertions
  d_smt.d_theoryEngine->notifyPreprocessedAssertions( d_assertions.ref() );

  // Push the formula to decision engine
  if(noConflict) {
    Chat() << "pushing to decision engine..." << endl;
    Assert(iteRewriteAssertionsEnd == d_assertions.size());
    d_smt.d_decisionEngine->addAssertions
      (d_assertions.ref(), d_realAssertionsEnd, d_iteSkolemMap);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  Trace("smt-proc") << "SmtEnginePrivate::processAssertions() end" << endl;
  dumpAssertions("post-everything", d_assertions);

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
  d_iteSkolemMap.clear();
}

void SmtEnginePrivate::addFormula(TNode n, bool inUnsatCore, bool inInput)
{
  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << "), inUnsatCore = " << inUnsatCore << ", inInput = " << inInput << endl;

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
    // rewrite rules are by default in the unsat core because
    // they need to be applied until saturation
    if(options::unsatCores() &&
       n.getKind() == kind::REWRITE_RULE ){
      ProofManager::currentPM()->addUnsatCore(n.toExpr());
    }
  );

  // Add the normalized formula to the queue
  d_assertions.push_back(n);
  //d_assertions.push_back(Rewriter::rewrite(n));
}

void SmtEngine::ensureBoolean(const Expr& e)
{
  Type type = e.getType(options::typeChecking());
  Type boolType = d_exprManager->booleanType();
  if(type != boolType) {
    stringstream ss;
    ss << "Expected " << boolType << "\n"
       << "The assertion : " << e << "\n"
       << "Its type      : " << type;
    throw TypeCheckingException(e, ss.str());
  }
}

Result SmtEngine::checkSat(const Expr& ex, bool inUnsatCore)
{
  return checkSatisfiability(ex, inUnsatCore, false);
} /* SmtEngine::checkSat() */

Result SmtEngine::query(const Expr& ex, bool inUnsatCore)
{
  Assert(!ex.isNull());
  return checkSatisfiability(ex, inUnsatCore, true);
} /* SmtEngine::query() */

Result SmtEngine::checkSatisfiability(const Expr& ex, bool inUnsatCore, bool isQuery) {
  try {
    Assert(ex.isNull() || ex.getExprManager() == d_exprManager);
    SmtScope smts(this);
    finalOptionsAreSet();
    doPendingPops();

    Trace("smt") << "SmtEngine::" << (isQuery ? "query" : "checkSat") << "(" << ex << ")" << endl;

    if(d_queryMade && !options::incrementalSolving()) {
      throw ModalException("Cannot make multiple queries unless "
                           "incremental solving is enabled "
                           "(try --incremental)");
    }

    Expr e;
    if(!ex.isNull()) {
      // Substitute out any abstract values in ex.
      e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
      // Ensure expr is type-checked at this point.
      ensureBoolean(e);
    }

    // check to see if a postsolve() is pending
    if(d_needPostsolve) {
      d_theoryEngine->postsolve();
      d_needPostsolve = false;
    }

    // Note that a query has been made
    d_queryMade = true;

    // reset global negation
    d_globalNegation = false;

    bool didInternalPush = false;
    // Add the formula
    if(!e.isNull()) {
      // Push the context
      internalPush();
      didInternalPush = true;

      d_problemExtended = true;
      Expr ea = isQuery ? e.notExpr() : e;
      if(d_assertionList != NULL) {
        d_assertionList->push_back(ea);
      }
      d_private->addFormula(ea.getNode(), inUnsatCore);
    }

    Result r(Result::SAT_UNKNOWN, Result::UNKNOWN_REASON);
    r = isQuery ? check().asValidityResult() : check().asSatisfiabilityResult();

    if ( ( options::solveRealAsInt() || options::solveIntAsBV() > 0 ) && r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
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

    // Dump the query if requested
    if(Dump.isOn("benchmark")) {
      // the expr already got dumped out if assertion-dumping is on
      if( isQuery ){
        Dump("benchmark") << QueryCommand(ex);
      }else{
        Dump("benchmark") << CheckSatCommand(ex);
      }
    }

    // Pop the context
    if (didInternalPush)
    {
      internalPop();
    }

    // Remember the status
    d_status = r;

    d_problemExtended = false;

    Trace("smt") << "SmtEngine::" << (isQuery ? "query" : "checkSat") << "(" << e << ") => " << r << endl;

    // Check that SAT results generate a model correctly.
    if(options::checkModels()) {
      if(r.asSatisfiabilityResult().isSat() == Result::SAT ||
         (r.isUnknown() && r.whyUnknown() == Result::INCOMPLETE) ){
        checkModel(/* hard failure iff */ ! r.isUnknown());
      }
    }
    // Check that UNSAT results generate a proof correctly.
    if(options::checkProofs()) {
      if(r.asSatisfiabilityResult().isSat() == Result::UNSAT) {
        TimerStat::CodeTimer checkProofTimer(d_stats->d_checkProofTime);
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
    // Check that synthesis solutions satisfy the conjecture
    if (options::checkSynthSol()
        && r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      checkSynthSolution();
    }

    return r;
  } catch (UnsafeInterruptException& e) {
    AlwaysAssert(d_private->getResourceManager()->out());
    Result::UnknownExplanation why = d_private->getResourceManager()->outOfResources() ?
      Result::RESOURCEOUT : Result::TIMEOUT;
    return Result(Result::SAT_UNKNOWN, why, d_filename);
  }
}

Result SmtEngine::checkSynth(const Expr& e)
{
  SmtScope smts(this);
  Trace("smt") << "Check synth: " << e << std::endl;
  Trace("smt-synth") << "Check synthesis conjecture: " << e << std::endl;
  Expr e_check = e;
  if (options::sygusQePreproc())
  {
    // the following does quantifier elimination as a preprocess step
    // for "non-ground single invocation synthesis conjectures":
    //   exists f. forall xy. P[ f(x), x, y ]
    // We run quantifier elimination:
    //   exists y. P[ z, x, y ] ----> Q[ z, x ]
    // Where we replace the original conjecture with:
    //   exists f. forall x. Q[ f(x), x ]
    // For more details, see Example 6 of Reynolds et al. SYNT 2017.
    Node conj = Node::fromExpr(e);
    if (conj.getKind() == kind::FORALL && conj[1].getKind() == kind::EXISTS)
    {
      Node conj_se = Node::fromExpr(expandDefinitions(conj[1][1].toExpr()));

      Trace("smt-synth") << "Compute single invocation for " << conj_se << "..."
                         << std::endl;
      quantifiers::SingleInvocationPartition sip;
      std::vector<Node> funcs;
      funcs.insert(funcs.end(), conj[0].begin(), conj[0].end());
      sip.init(funcs, conj_se.negate());
      Trace("smt-synth") << "...finished, got:" << std::endl;
      sip.debugPrint("smt-synth");

      if (!sip.isPurelySingleInvocation() && sip.isNonGroundSingleInvocation())
      {
        // create new smt engine to do quantifier elimination
        SmtEngine smt_qe(d_exprManager);
        smt_qe.setLogic(getLogicInfo());
        Trace("smt-synth") << "Property is non-ground single invocation, run "
                              "QE to obtain single invocation."
                           << std::endl;
        NodeManager* nm = NodeManager::currentNM();
        // partition variables
        std::vector<Node> all_vars;
        sip.getAllVariables(all_vars);
        std::vector<Node> si_vars;
        sip.getSingleInvocationVariables(si_vars);
        std::vector<Node> qe_vars;
        std::vector<Node> nqe_vars;
        for (unsigned i = 0, size = all_vars.size(); i < size; i++)
        {
          Node v = all_vars[i];
          if (std::find(si_vars.begin(), si_vars.end(), v) == si_vars.end())
          {
            qe_vars.push_back(v);
          }
          else
          {
            nqe_vars.push_back(v);
          }
        }
        std::vector<Node> orig;
        std::vector<Node> subs;
        // skolemize non-qe variables
        for (unsigned i = 0; i < nqe_vars.size(); i++)
        {
          Node k = nm->mkSkolem("k",
                                nqe_vars[i].getType(),
                                "qe for non-ground single invocation");
          orig.push_back(nqe_vars[i]);
          subs.push_back(k);
          Trace("smt-synth") << "  subs : " << nqe_vars[i] << " -> " << k
                             << std::endl;
        }
        std::vector<Node> funcs;
        sip.getFunctions(funcs);
        for (unsigned i = 0, size = funcs.size(); i < size; i++)
        {
          Node f = funcs[i];
          Node fi = sip.getFunctionInvocationFor(f);
          Node fv = sip.getFirstOrderVariableForFunction(f);
          Assert(!fi.isNull());
          orig.push_back(fi);
          Node k =
              nm->mkSkolem("k",
                           fv.getType(),
                           "qe for function in non-ground single invocation");
          subs.push_back(k);
          Trace("smt-synth") << "  subs : " << fi << " -> " << k << std::endl;
        }
        Node conj_se_ngsi = sip.getFullSpecification();
        Trace("smt-synth") << "Full specification is " << conj_se_ngsi
                           << std::endl;
        Node conj_se_ngsi_subs = conj_se_ngsi.substitute(
            orig.begin(), orig.end(), subs.begin(), subs.end());
        Assert(!qe_vars.empty());
        conj_se_ngsi_subs =
            nm->mkNode(kind::EXISTS,
                       nm->mkNode(kind::BOUND_VAR_LIST, qe_vars),
                       conj_se_ngsi_subs.negate());

        Trace("smt-synth") << "Run quantifier elimination on "
                           << conj_se_ngsi_subs << std::endl;
        Expr qe_res = smt_qe.doQuantifierElimination(
            conj_se_ngsi_subs.toExpr(), true, false);
        Trace("smt-synth") << "Result : " << qe_res << std::endl;

        // create single invocation conjecture
        Node qe_res_n = Node::fromExpr(qe_res);
        qe_res_n = qe_res_n.substitute(
            subs.begin(), subs.end(), orig.begin(), orig.end());
        if (!nqe_vars.empty())
        {
          qe_res_n = nm->mkNode(kind::EXISTS,
                                nm->mkNode(kind::BOUND_VAR_LIST, nqe_vars),
                                qe_res_n);
        }
        Assert(conj.getNumChildren() == 3);
        qe_res_n = nm->mkNode(kind::FORALL, conj[0], qe_res_n, conj[2]);
        Trace("smt-synth") << "Converted conjecture after QE : " << qe_res_n
                           << std::endl;
        e_check = qe_res_n.toExpr();
      }
    }
  }

  return checkSatisfiability( e_check, true, false );
}

Result SmtEngine::assertFormula(const Expr& ex, bool inUnsatCore)
{
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();

  Trace("smt") << "SmtEngine::assertFormula(" << ex << ")" << endl;

  if (Dump.isOn("raw-benchmark")) {
    Dump("raw-benchmark") << AssertCommand(ex);
  }

  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  ensureBoolean(e);
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e);
  }
  d_private->addFormula(e.getNode(), inUnsatCore);
  return quickCheck().asValidityResult();
}/* SmtEngine::assertFormula() */

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

  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  if( options::typeChecking() ) {
    e.getType(true); // ensure expr is type-checked at this point
  }

  // Make sure all preprocessing is done
  d_private->processAssertions();
  Node n = d_private->simplify(Node::fromExpr(e));
  n = postprocess(n, TypeNode::fromType(e.getType()));
  return n.toExpr();
}

Expr SmtEngine::expandDefinitions(const Expr& ex)
{
  d_private->spendResource(options::preprocessStep());

  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT expandDefinitions(" << ex << ")" << endl;

  // Substitute out any abstract values in ex.
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  if(options::typeChecking()) {
    // Ensure expr is type-checked at this point.
    e.getType(true);
  }
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ExpandDefinitionsCommand(e);
  }
  unordered_map<Node, Node, NodeHashFunction> cache;
  Node n = d_private->expandDefinitions(Node::fromExpr(e), cache, /* expandOnly = */ true);
  n = postprocess(n, TypeNode::fromType(e.getType()));

  return n.toExpr();
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

  if(!options::produceModels()) {
    const char* msg =
      "Cannot get value when produce-models options is off.";
    throw ModalException(msg);
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get value unless immediately preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }

  // Substitute out any abstract values in ex.
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  // Ensure expr is type-checked at this point.
  e.getType(options::typeChecking());

  // do not need to apply preprocessing substitutions (should be recorded
  // in model already)

  Node n = Node::fromExpr(e);
  Trace("smt") << "--- getting value of " << n << endl;
  TypeNode expectedType = n.getType();

  // Expand, then normalize
  unordered_map<Node, Node, NodeHashFunction> cache;
  n = d_private->expandDefinitions(n, cache);
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
  TheoryModel* m = d_theoryEngine->getModel();
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
  Assert(resultNode.isNull() || resultNode.getType().isSubtypeOf(expectedType),
         "Run with -t smt for details.");

  // ensure it's a constant
  Assert(resultNode.getKind() == kind::LAMBDA || resultNode.isConst());

  if(options::abstractValues() && resultNode.getType().isArray()) {
    resultNode = d_private->mkAbstractValue(resultNode);
    Trace("smt") << "--- abstract value >> " << resultNode << endl;
  }

  return resultNode.toExpr();
}

bool SmtEngine::addToAssignment(const Expr& ex) {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  Type type = e.getType(options::typeChecking());
  // must be Boolean
  PrettyCheckArgument(
      type.isBoolean(), e,
      "expected Boolean-typed variable or function application "
      "in addToAssignment()" );
  Node n = e.getNode();
  // must be an APPLY of a zero-ary defined function, or a variable
  PrettyCheckArgument(
      ( ( n.getKind() == kind::APPLY &&
          ( d_definedFunctions->find(n.getOperator()) !=
            d_definedFunctions->end() ) &&
          n.getNumChildren() == 0 ) ||
        n.isVar() ), e,
      "expected variable or defined-function application "
      "in addToAssignment(),\ngot %s", e.toString().c_str() );
  if(!options::produceAssignments()) {
    return false;
  }
  if(d_assignments == NULL) {
    d_assignments = new(true) AssignmentSet(d_context);
  }
  d_assignments->insert(n);

  return true;
}

// TODO(#1108): Simplify the error reporting of this method.
CVC4::SExpr SmtEngine::getAssignment() {
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
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT  ||
     d_problemExtended) {
    const char* msg =
      "Cannot get the current assignment unless immediately "
      "preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }

  if(d_assignments == NULL) {
    return SExpr(vector<SExpr>());
  }

  vector<SExpr> sexprs;
  TypeNode boolType = d_nodeManager->booleanType();
  TheoryModel* m = d_theoryEngine->getModel();
  for(AssignmentSet::key_iterator i = d_assignments->key_begin(),
        iend = d_assignments->key_end();
      i != iend;
      ++i) {
    Assert((*i).getType() == boolType);

    Trace("smt") << "--- getting value of " << *i << endl;

    // Expand, then normalize
    unordered_map<Node, Node, NodeHashFunction> cache;
    Node n = d_private->expandDefinitions(*i, cache);
    n = Rewriter::rewrite(n);

    Trace("smt") << "--- getting value of " << n << endl;
    Node resultNode;
    if(m != NULL) {
      resultNode = m->getValue(n);
    }

    // type-check the result we got
    Assert(resultNode.isNull() || resultNode.getType() == boolType);

    // ensure it's a constant
    Assert(resultNode.isConst());

    vector<SExpr> v;
    if((*i).getKind() == kind::APPLY) {
      Assert((*i).getNumChildren() == 0);
      v.push_back(SExpr(SExpr::Keyword((*i).getOperator().toString())));
    } else {
      Assert((*i).isVar());
      v.push_back(SExpr(SExpr::Keyword((*i).toString())));
    }
    v.push_back(SExpr(SExpr::Keyword(resultNode.toString())));
    sexprs.push_back(SExpr(v));
  }
  return SExpr(sexprs);
}

void SmtEngine::addToModelCommandAndDump(const Command& c, uint32_t flags, bool userVisible, const char* dumpTag) {
  Trace("smt") << "SMT addToModelCommandAndDump(" << c << ")" << endl;
  SmtScope smts(this);
  // If we aren't yet fully inited, the user might still turn on
  // produce-models.  So let's keep any commands around just in
  // case.  This is useful in two cases: (1) SMT-LIBv1 auto-declares
  // sort "U" in QF_UF before setLogic() is run and we still want to
  // support finding card(U) with --finite-model-find, and (2) to
  // decouple SmtEngine and ExprManager if the user does a few
  // ExprManager::mkSort() before SmtEngine::setOption("produce-models")
  // and expects to find their cardinalities in the model.
  if(/* userVisible && */
     (!d_fullyInited || options::produceModels()) &&
     (flags & ExprManager::VAR_FLAG_DEFINED) == 0) {
    doPendingPops();
    if(flags & ExprManager::VAR_FLAG_GLOBAL) {
      d_modelGlobalCommands.push_back(c.clone());
    } else {
      d_modelCommands->push_back(c.clone());
    }
  }
  if(Dump.isOn(dumpTag)) {
    if(d_fullyInited) {
      Dump(dumpTag) << c;
    } else {
      d_dumpCommands.push_back(c.clone());
    }
  }
}

// TODO(#1108): Simplify the error reporting of this method.
Model* SmtEngine::getModel() {
  Trace("smt") << "SMT getModel()" << endl;
  SmtScope smts(this);

  finalOptionsAreSet();

  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetModelCommand();
  }

  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() == Result::UNSAT ||
     d_problemExtended) {
    const char* msg =
      "Cannot get the current model unless immediately "
      "preceded by SAT/INVALID or UNKNOWN response.";
    throw RecoverableModalException(msg);
  }
  if(!options::produceModels()) {
    const char* msg =
      "Cannot get model when produce-models options is off.";
    throw ModalException(msg);
  }
  TheoryModel* m = d_theoryEngine->getModel();
  m->d_inputName = d_filename;
  return m;
}

void SmtEngine::checkUnsatCore() {
  Assert(options::unsatCores(), "cannot check unsat core if unsat cores are turned off");

  Notice() << "SmtEngine::checkUnsatCore(): generating unsat core" << endl;
  UnsatCore core = getUnsatCore();

  SmtEngine coreChecker(d_exprManager);
  coreChecker.setLogic(getLogicInfo());

  PROOF(
  std::vector<Command*>::const_iterator itg = d_defineCommands.begin();
  for (; itg != d_defineCommands.end();  ++itg) {
    (*itg)->invoke(&coreChecker);
  }
  );

  Notice() << "SmtEngine::checkUnsatCore(): pushing core assertions (size == " << core.size() << ")" << endl;
  for(UnsatCore::iterator i = core.begin(); i != core.end(); ++i) {
    Notice() << "SmtEngine::checkUnsatCore(): pushing core member " << *i << endl;
    coreChecker.assertFormula(*i);
  }
  const bool checkUnsatCores = options::checkUnsatCores();
  Result r;
  try {
    options::checkUnsatCores.set(false);
    options::checkProofs.set(false);
    r = coreChecker.checkSat();
  } catch(...) {
    options::checkUnsatCores.set(checkUnsatCores);
    throw;
  }
  Notice() << "SmtEngine::checkUnsatCore(): result is " << r << endl;
  if(r.asSatisfiabilityResult().isUnknown()) {
    InternalError("SmtEngine::checkUnsatCore(): could not check core result unknown.");
  }

  if(r.asSatisfiabilityResult().isSat()) {
    InternalError("SmtEngine::checkUnsatCore(): produced core was satisfiable.");
  }
}

void SmtEngine::checkModel(bool hardFailure) {
  // --check-model implies --produce-assertions, which enables the
  // assertion list, so we should be ok.
  Assert(d_assertionList != NULL, "don't have an assertion list to check in SmtEngine::checkModel()");

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  Notice() << "SmtEngine::checkModel(): generating model" << endl;
  TheoryModel* m = d_theoryEngine->getModel();

  // Check individual theory assertions
  d_theoryEngine->checkTheoryAssertionsWithModel(hardFailure);

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
          InternalError(ss.str());
        }
      }

      // (2) check that the value is actually a value
      else if (!val.isConst()) {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT A CONSTANT ***" << endl;
        stringstream ss;
        ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
           << "model value for " << func << endl
           << "             is " << val << endl
           << "and that is not a constant (.isConst() == false)." << endl
           << "Run with `--check-models -v' for additional diagnostics.";
        InternalError(ss.str());
      }

      // (3) check that it's the correct (sub)type
      // This was intended to be a more general check, but for now we can't do that because
      // e.g. "1" is an INT, which isn't a subrange type [1..10] (etc.).
      else if(func.getType().isInteger() && !val.getType().isInteger()) {
        Notice() << "SmtEngine::checkModel(): *** PROBLEM: MODEL VALUE NOT CORRECT TYPE ***" << endl;
        stringstream ss;
        ss << "SmtEngine::checkModel(): ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
           << "model value for " << func << endl
           << "             is " << val << endl
           << "value type is     " << val.getType() << endl
           << "should be of type " << func.getType() << endl
           << "Run with `--check-models -v' for additional diagnostics.";
        InternalError(ss.str());
      }

      // (4) checks complete, add the substitution
      Debug("boolean-terms") << "cm: adding subs " << func << " :=> " << val << endl;
      substitutions.addSubstitution(func, val);
    }
  }

  // Now go through all our user assertions checking if they're satisfied.
  for(AssertionList::const_iterator i = d_assertionList->begin(); i != d_assertionList->end(); ++i) {
    Notice() << "SmtEngine::checkModel(): checking assertion " << *i << endl;
    Node n = Node::fromExpr(*i);

    // Apply any define-funs from the problem.
    {
      unordered_map<Node, Node, NodeHashFunction> cache;
      n = d_private->expandDefinitions(n, cache);
    }
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << endl;

    // Apply our model value substitutions.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << endl;

    if( n.getKind() != kind::REWRITE_RULE ){
      // In case it's a quantifier (or contains one), look up its value before
      // simplifying, or the quantifier might be irreparably altered.
      n = m->getValue(n);
      Notice() << "SmtEngine::checkModel(): -- get value : " << n << std::endl;
    } else {
      // Note this "skip" is done here, rather than above.  This is
      // because (1) the quantifier could in principle simplify to false,
      // which should be reported, and (2) checking for the quantifier
      // above, before simplification, doesn't catch buried quantifiers
      // anyway (those not at the top-level).
      Notice() << "SmtEngine::checkModel(): -- skipping rewrite-rules assertion"
               << endl;
      continue;
    }

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

    if( d_logic.isQuantified() ){
      // AJR: since quantified formulas are not checkable, we assign them to true/false based on the satisfying assignment.
      // however, quantified formulas can be modified during preprocess, so they may not correspond to those in the satisfying assignment.
      // hence we use a relaxed version of check model here.
      // this is necessary until preprocessing passes explicitly record how they rewrite quantified formulas
      if( hardFailure && !n.isConst() && n.getKind() != kind::LAMBDA ){
        Notice() << "SmtEngine::checkModel(): -- relax check model wrt quantified formulas..." << endl;
        AlwaysAssert( quantifiers::QuantifiersRewriter::containsQuantifiers( n ) );
        Warning() << "Warning : SmtEngine::checkModel(): cannot check simplified assertion : " << n << endl;
        continue;
      }
    }else{
      AlwaysAssert(!hardFailure || n.isConst() || n.getKind() == kind::LAMBDA);
    }
    // The result should be == true.
    if(n != NodeManager::currentNM()->mkConst(true)) {
      Notice() << "SmtEngine::checkModel(): *** PROBLEM: EXPECTED `TRUE' ***"
               << endl;
      stringstream ss;
      ss << "SmtEngine::checkModel(): "
         << "ERRORS SATISFYING ASSERTIONS WITH MODEL:" << endl
         << "assertion:     " << *i << endl
         << "simplifies to: " << n << endl
         << "expected `true'." << endl
         << "Run with `--check-models -v' for additional diagnostics.";
      if(hardFailure) {
        InternalError(ss.str());
      } else {
        Warning() << ss.str() << endl;
      }
    }
  }
  Notice() << "SmtEngine::checkModel(): all assertions checked out OK !" << endl;
}

void SmtEngine::checkSynthSolution()
{
  NodeManager* nm = NodeManager::currentNM();
  Notice() << "SmtEngine::checkSynthSolution(): checking synthesis solution" << endl;
  map<Node, Node> sol_map;
  /* Get solutions and build auxiliary vectors for substituting */
  d_theoryEngine->getSynthSolutions(sol_map);
  Trace("check-synth-sol") << "Got solution map:\n";
  std::vector<Node> function_vars, function_sols;
  for (const auto& pair : sol_map)
  {
    Trace("check-synth-sol") << pair.first << " --> " << pair.second << "\n";
    function_vars.push_back(pair.first);
    function_sols.push_back(pair.second);
  }
  Trace("check-synth-sol") << "Starting new SMT Engine\n";
  /* Start new SMT engine to check solutions */
  SmtEngine solChecker(d_exprManager);
  solChecker.setLogic(getLogicInfo());
  setOption("check-synth-sol", SExpr("false"));

  Trace("check-synth-sol") << "Retrieving assertions\n";
  // Build conjecture from original assertions
  if (d_assertionList == NULL)
  {
    Trace("check-synth-sol") << "No assertions to check\n";
    return;
  }
  for (AssertionList::const_iterator i = d_assertionList->begin();
       i != d_assertionList->end();
       ++i)
  {
    Notice() << "SmtEngine::checkSynthSolution(): checking assertion " << *i << endl;
    Trace("check-synth-sol") << "Retrieving assertion " << *i << "\n";
    Node conj = Node::fromExpr(*i);
    // Apply any define-funs from the problem.
    {
      unordered_map<Node, Node, NodeHashFunction> cache;
      conj = d_private->expandDefinitions(conj, cache);
    }
    Notice() << "SmtEngine::checkSynthSolution(): -- expands to " << conj << endl;
    Trace("check-synth-sol") << "Expanded assertion " << conj << "\n";

    // Apply solution map to conjecture body
    Node conjBody;
    /* Whether property is quantifier free */
    if (conj[1].getKind() != kind::EXISTS)
    {
      conjBody = conj[1].substitute(function_vars.begin(),
                                    function_vars.end(),
                                    function_sols.begin(),
                                    function_sols.end());
    }
    else
    {
      conjBody = conj[1][1].substitute(function_vars.begin(),
                                       function_vars.end(),
                                       function_sols.begin(),
                                       function_sols.end());

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
    solChecker.assertFormula(conjBody.toExpr());
    Result r = solChecker.checkSat();
    Notice() << "SmtEngine::checkSynthSolution(): result is " << r << endl;
    Trace("check-synth-sol") << "Satsifiability check: " << r << "\n";
    if (r.asSatisfiabilityResult().isUnknown())
    {
      InternalError(
          "SmtEngine::checkSynthSolution(): could not check solution, result "
          "unknown.");
    }
    else if (r.asSatisfiabilityResult().isSat())
    {
      InternalError(
          "SmtEngine::checkSynhtSol(): produced solution allows satisfiable "
          "negated conjecture.");
    }
    solChecker.resetAssertions();
  }
}

// TODO(#1108): Simplify the error reporting of this method.
UnsatCore SmtEngine::getUnsatCore() {
  Trace("smt") << "SMT getUnsatCore()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetUnsatCoreCommand();
  }
#if IS_PROOFS_BUILD
  if(!options::unsatCores()) {
    throw ModalException("Cannot get an unsat core when produce-unsat-cores option is off.");
  }
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::UNSAT ||
     d_problemExtended) {
    throw RecoverableModalException(
        "Cannot get an unsat core unless immediately preceded by UNSAT/VALID "
        "response.");
  }

  d_proofManager->traceUnsatCore();// just to trigger core creation
  return UnsatCore(this, d_proofManager->extractUnsatCore());
#else /* IS_PROOFS_BUILD */
  throw ModalException("This build of CVC4 doesn't have proof support (required for unsat cores).");
#endif /* IS_PROOFS_BUILD */
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
  if(d_status.isNull() ||
     d_status.asSatisfiabilityResult() != Result::UNSAT ||
     d_problemExtended) {
    throw RecoverableModalException(
        "Cannot get a proof unless immediately preceded by UNSAT/VALID "
        "response.");
  }

  return ProofManager::getProof(this);
#else /* IS_PROOFS_BUILD */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* IS_PROOFS_BUILD */
}

void SmtEngine::printInstantiations( std::ostream& out ) {
  SmtScope smts(this);
  if( options::instFormatMode()==INST_FORMAT_MODE_SZS ){
    out << "% SZS output start Proof for " << d_filename.c_str() << std::endl;
  }
  if( d_theoryEngine ){
    d_theoryEngine->printInstantiations( out );
  }else{
    Assert( false );
  }
  if( options::instFormatMode()==INST_FORMAT_MODE_SZS ){
    out << "% SZS output end Proof for " << d_filename.c_str() << std::endl;
  }
}

void SmtEngine::printSynthSolution( std::ostream& out ) {
  SmtScope smts(this);
  if( d_theoryEngine ){
    d_theoryEngine->printSynthSolution( out );
  }else{
    Assert( false );
  }
}

Expr SmtEngine::doQuantifierElimination(const Expr& e, bool doFull, bool strict)
{
  SmtScope smts(this);
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
  Assert( nn_e.getNumChildren()==3 );
  Result r = checkSatisfiability(nn_e.toExpr(), true, true);
  Trace("smt-qe") << "Query returned " << r << std::endl;
  if(r.asSatisfiabilityResult().isSat() != Result::UNSAT ) {
    if( r.asSatisfiabilityResult().isSat() != Result::SAT && doFull ){
      stringstream ss;
      ss << "While performing quantifier elimination, unexpected result : " << r << " for query.";
      InternalError(ss.str().c_str());
    }
    std::vector< Node > inst_qs;
    d_theoryEngine->getInstantiatedQuantifiedFormulas( inst_qs );
    Assert( inst_qs.size()<=1 );
    Node ret_n;
    if( inst_qs.size()==1 ){
      Node top_q = inst_qs[0]; 
      //Node top_q = Rewriter::rewrite( nn_e ).negate();
      Assert( top_q.getKind()==kind::FORALL );
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
    return ret_n.toExpr();
  }else {
    return NodeManager::currentNM()
        ->mkConst(n_e.getKind() == kind::EXISTS)
        .toExpr();
  }
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
    Assert( false );
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
    Assert( false );
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
    Assert( false );
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
  // copy the result out
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
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

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // The problem isn't really "extended" yet, but this disallows
  // get-model after a push, simplifying our lives somewhat and
  // staying symmtric with pop.
  d_problemExtended = true;

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

  // check to see if a postsolve() is pending
  if(d_needPostsolve) {
    d_theoryEngine->postsolve();
    d_needPostsolve = false;
  }

  // The problem isn't really "extended" yet, but this disallows
  // get-model after a pop, simplifying our lives somewhat.  It might
  // not be strictly necessary to do so, since the pops occur lazily,
  // but also it would be weird to have a legally-executed (get-model)
  // that only returns a subset of the assignment (because the rest
  // is no longer in scope!).
  d_problemExtended = true;

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
  Assert(d_pendingPops == 0 || options::incrementalSolving());
  while(d_pendingPops > 0) {
    TimerStat::CodeTimer pushPopTimer(d_stats->d_pushPopTime);
    d_propEngine->pop();
    // the d_context pop is done inside of the SAT solver
    d_userContext->pop();
    --d_pendingPops;
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
  NodeManager::fromExprManager(em)->getOptions().copyValues(opts);
  new(this) SmtEngine(em);
}

void SmtEngine::resetAssertions()
{
  SmtScope smts(this);
  doPendingPops();

  Trace("smt") << "SMT resetAssertions()" << endl;
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << ResetAssertionsCommand();
  }

  while(!d_userLevels.empty()) {
    pop();
  }

  // Also remember the global push/pop around everything.
  Assert(d_userLevels.size() == 0 && d_userContext->getLevel() == 1);
  d_context->popto(0);
  d_userContext->popto(0);
  DeleteAndClearCommandVector(d_modelGlobalCommands);
  d_userContext->push();
  d_context->push();
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
  d_private->getResourceManager()->setResourceLimit(units, cumulative);
}
void SmtEngine::setTimeLimit(unsigned long milis, bool cumulative) {
  d_private->getResourceManager()->setTimeLimit(milis, cumulative);
}

unsigned long SmtEngine::getResourceUsage() const {
  return d_private->getResourceManager()->getResourceUsage();
}

unsigned long SmtEngine::getTimeUsage() const {
  return d_private->getResourceManager()->getTimeUsage();
}

unsigned long SmtEngine::getResourceRemaining() const
{
  return d_private->getResourceManager()->getResourceRemaining();
}

unsigned long SmtEngine::getTimeRemaining() const
{
  return d_private->getResourceManager()->getTimeRemaining();
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
  std::vector<Node> node_values;
  for( unsigned i=0; i<expr_values.size(); i++ ){
    node_values.push_back( expr_values[i].getNode() );
  }
  d_theoryEngine->setUserAttribute(attr, expr.getNode(), node_values, str_value);
}

void SmtEngine::setPrintFuncInModel(Expr f, bool p) {
  Trace("setp-model") << "Set printInModel " << f << " to " << p << std::endl;
  for( unsigned i=0; i<d_modelGlobalCommands.size(); i++ ){
    Command * c = d_modelGlobalCommands[i];
    DeclareFunctionCommand* dfc = dynamic_cast<DeclareFunctionCommand*>(c);
    if(dfc != NULL) {
      if( dfc->getFunction()==f ){
        dfc->setPrintInModel( p );
      }
    }
  }
  for( unsigned i=0; i<d_modelCommands->size(); i++ ){
    Command * c = (*d_modelCommands)[i];
    DeclareFunctionCommand* dfc = dynamic_cast<DeclareFunctionCommand*>(c);
    if(dfc != NULL) {
      if( dfc->getFunction()==f ){
        dfc->setPrintInModel( p );
      }
    }
  }
}

void SmtEngine::beforeSearch()
{
  if(d_fullyInited) {
    throw ModalException(
        "SmtEngine::beforeSearch called after initialization.");
  }
}


void SmtEngine::setOption(const std::string& key, const CVC4::SExpr& value)
{
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
  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  nodeManagerOptions.setOption(key, optionarg);
}

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

  Options& nodeManagerOptions = NodeManager::currentNM()->getOptions();
  return SExpr::parseAtom(nodeManagerOptions.getOption(key));
}

void SmtEngine::setReplayStream(ExprStream* replayStream) {
  AlwaysAssert(!d_fullyInited,
               "Cannot set replay stream once fully initialized");
  d_replayStream = replayStream;
}  

bool SmtEngine::getExpressionName(Expr e, std::string& name) const {
  return d_private->getExpressionName(e, name);
}

void SmtEngine::setExpressionName(Expr e, const std::string& name) {
  Trace("smt-debug") << "Set expression name " << e << " to " << name << std::endl;
  d_private->setExpressionName(e,name);
}

}/* CVC4 namespace */
