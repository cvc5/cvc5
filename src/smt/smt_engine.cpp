/*********************                                                        */
/*! \file smt_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Clark Barrett
 ** Minor contributors (to current version): Tianyi Liang, Christopher L. Conway, Kshitij Bansal, Liana Hadarean, Dejan Jovanovic, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include <cctype>
#include <algorithm>
#include <ext/hash_map>

#include "context/cdlist.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "decision/decision_engine.h"
#include "decision/decision_mode.h"
#include "decision/options.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_builder.h"
#include "expr/node.h"
#include "expr/node_self_iterator.h"
#include "prop/prop_engine.h"
#include "proof/theory_proof.h"
#include "smt/modal_exception.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/model_postprocessor.h"
#include "theory/theory_engine.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "proof/proof_manager.h"
#include "main/options.h"
#include "util/proof.h"
#include "proof/proof.h"
#include "proof/proof_manager.h"
#include "util/boolean_simplification.h"
#include "util/node_visitor.h"
#include "util/configuration.h"
#include "util/exception.h"
#include "util/nary_builder.h"
#include "smt/command_list.h"
#include "smt/boolean_terms.h"
#include "smt/options.h"
#include "options/option_exception.h"
#include "util/output.h"
#include "util/hash.h"
#include "theory/substitutions.h"
#include "theory/uf/options.h"
#include "theory/arith/options.h"
#include "theory/strings/options.h"
#include "theory/bv/options.h"
#include "theory/theory_traits.h"
#include "theory/logic_info.h"
#include "theory/options.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/booleans/boolean_term_conversion_mode.h"
#include "theory/booleans/options.h"
#include "util/ite_removal.h"
#include "theory/theory_model.h"
#include "printer/printer.h"
#include "prop/options.h"
#include "theory/arrays/options.h"
#include "util/sort_inference.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/macros.h"
#include "theory/datatypes/options.h"
#include "theory/quantifiers/first_order_reasoning.h"
#include "theory/strings/theory_strings_preprocess.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::prop;
using namespace CVC4::context;
using namespace CVC4::theory;

namespace CVC4 {

namespace smt {

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
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** time spent in Boolean term rewriting */
  TimerStat d_rewriteBooleanTermsTime;
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
  /** time spent in PropEngine::checkSat() */
  TimerStat d_solveTime;
  /** time spent in pushing/popping */
  TimerStat d_pushPopTime;
  /** time spent in processAssertions() */
  TimerStat d_processAssertionsTime;

  /** Has something simplified to false? */
  IntStat d_simplifiedToFalse;

  SmtEngineStatistics() :
    d_definitionExpansionTime("smt::SmtEngine::definitionExpansionTime"),
    d_rewriteBooleanTermsTime("smt::SmtEngine::rewriteBooleanTermsTime"),
    d_nonclausalSimplificationTime("smt::SmtEngine::nonclausalSimplificationTime"),
    d_miplibPassTime("smt::SmtEngine::miplibPassTime"),
    d_numMiplibAssertionsRemoved("smt::SmtEngine::numMiplibAssertionsRemoved", 0),
    d_numConstantProps("smt::SmtEngine::numConstantProps", 0),
    d_staticLearningTime("smt::SmtEngine::staticLearningTime"),
    d_simpITETime("smt::SmtEngine::simpITETime"),
    d_unconstrainedSimpTime("smt::SmtEngine::unconstrainedSimpTime"),
    d_iteRemovalTime("smt::SmtEngine::iteRemovalTime"),
    d_theoryPreprocessTime("smt::SmtEngine::theoryPreprocessTime"),
    d_cnfConversionTime("smt::SmtEngine::cnfConversionTime"),
    d_numAssertionsPre("smt::SmtEngine::numAssertionsPreITERemoval", 0),
    d_numAssertionsPost("smt::SmtEngine::numAssertionsPostITERemoval", 0),
    d_checkModelTime("smt::SmtEngine::checkModelTime"),
    d_checkProofTime("smt::SmtEngine::checkProofTime"),
    d_solveTime("smt::SmtEngine::solveTime"),
    d_pushPopTime("smt::SmtEngine::pushPopTime"),
    d_processAssertionsTime("smt::SmtEngine::processAssertionsTime"),
    d_simplifiedToFalse("smt::SmtEngine::simplifiedToFalse", 0)
 {

    StatisticsRegistry::registerStat(&d_definitionExpansionTime);
    StatisticsRegistry::registerStat(&d_rewriteBooleanTermsTime);
    StatisticsRegistry::registerStat(&d_nonclausalSimplificationTime);
    StatisticsRegistry::registerStat(&d_miplibPassTime);
    StatisticsRegistry::registerStat(&d_numMiplibAssertionsRemoved);
    StatisticsRegistry::registerStat(&d_numConstantProps);
    StatisticsRegistry::registerStat(&d_staticLearningTime);
    StatisticsRegistry::registerStat(&d_simpITETime);
    StatisticsRegistry::registerStat(&d_unconstrainedSimpTime);
    StatisticsRegistry::registerStat(&d_iteRemovalTime);
    StatisticsRegistry::registerStat(&d_theoryPreprocessTime);
    StatisticsRegistry::registerStat(&d_cnfConversionTime);
    StatisticsRegistry::registerStat(&d_numAssertionsPre);
    StatisticsRegistry::registerStat(&d_numAssertionsPost);
    StatisticsRegistry::registerStat(&d_checkModelTime);
    StatisticsRegistry::registerStat(&d_solveTime);
    StatisticsRegistry::registerStat(&d_pushPopTime);
    StatisticsRegistry::registerStat(&d_processAssertionsTime);
    StatisticsRegistry::registerStat(&d_simplifiedToFalse);
  }

  ~SmtEngineStatistics() {
    StatisticsRegistry::unregisterStat(&d_definitionExpansionTime);
    StatisticsRegistry::unregisterStat(&d_rewriteBooleanTermsTime);
    StatisticsRegistry::unregisterStat(&d_nonclausalSimplificationTime);
    StatisticsRegistry::unregisterStat(&d_miplibPassTime);
    StatisticsRegistry::unregisterStat(&d_numMiplibAssertionsRemoved);
    StatisticsRegistry::unregisterStat(&d_numConstantProps);
    StatisticsRegistry::unregisterStat(&d_staticLearningTime);
    StatisticsRegistry::unregisterStat(&d_simpITETime);
    StatisticsRegistry::unregisterStat(&d_unconstrainedSimpTime);
    StatisticsRegistry::unregisterStat(&d_iteRemovalTime);
    StatisticsRegistry::unregisterStat(&d_theoryPreprocessTime);
    StatisticsRegistry::unregisterStat(&d_cnfConversionTime);
    StatisticsRegistry::unregisterStat(&d_numAssertionsPre);
    StatisticsRegistry::unregisterStat(&d_numAssertionsPost);
    StatisticsRegistry::unregisterStat(&d_checkModelTime);
    StatisticsRegistry::unregisterStat(&d_solveTime);
    StatisticsRegistry::unregisterStat(&d_pushPopTime);
    StatisticsRegistry::unregisterStat(&d_processAssertionsTime);
    StatisticsRegistry::unregisterStat(&d_simplifiedToFalse);
  }
};/* struct SmtEngineStatistics */

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

  /** The assertions yet to be preprocessed */
  vector<Node> d_assertionsToPreprocess;

  /** Learned literals */
  vector<Node> d_nonClausalLearnedLiterals;

  /** Size of assertions array when preprocessing starts */
  unsigned d_realAssertionsEnd;

  /** The converter for Boolean terms -> BITVECTOR(1). */
  BooleanTermConverter* d_booleanTermConverter;

  /** A circuit propagator for non-clausal propositional deduction */
  booleans::CircuitPropagator d_propagator;
  bool d_propagatorNeedsFinish;
  std::vector<Node> d_boolVars;

  /** Assertions to push to sat */
  vector<Node> d_assertionsToCheck;

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
  hash_map<Node, Node, NodeHashFunction> d_abstractValues;

  /**
   * Function symbol used to implement uninterpreted undefined string
   * semantics.  Needed to deal with partial charat/substr function.
   */
  //Node d_substrUndef;

  /**
   * Function symbol used to implement uninterpreted division-by-zero
   * semantics.  Needed to deal with partial division function ("/").
   */
  Node d_divByZero;

  /**
   * Maps from bit-vector width to divison-by-zero uninterpreted
   * function symbols.
   */
  hash_map<unsigned, Node> d_BVDivByZero;
  hash_map<unsigned, Node> d_BVRemByZero;

  /**
   * Function symbol used to implement uninterpreted
   * int-division-by-zero semantics.  Needed to deal with partial
   * function "div".
   */
  Node d_intDivByZero;

  /**
   * Function symbol used to implement uninterpreted mod-zero
   * semantics.  Needed to deal with partial function "mod".
   */
  Node d_modZero;

  /** Number of calls of simplify assertions active.
   */
  unsigned d_simplifyAssertionsDepth;

public:
  /**
   * Map from skolem variables to index in d_assertionsToCheck containing
   * corresponding introduced Boolean ite
   */
  IteSkolemMap d_iteSkolemMap;

  /** Instance of the ITE remover */
  RemoveITE d_iteRemover;

private:
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

  /**
   * Helper function to fix up assertion list to restore invariants needed after ite removal
   */
  void collectSkolems(TNode n, set<TNode>& skolemSet, hash_map<Node, bool, NodeHashFunction>& cache);

  /**
   * Helper function to fix up assertion list to restore invariants needed after ite removal
   */
  bool checkForBadSkolems(TNode n, TNode skolem, hash_map<Node, bool, NodeHashFunction>& cache);

  // Lift bit-vectors of size 1 to booleans
  void bvToBool();

  // Simplify ITE structure
  bool simpITE();

  // Simplify based on unconstrained values
  void unconstrainedSimp();

  // Ensures the assertions asserted after before now
  // effectively come before d_realAssertionsEnd
  void compressBeforeRealAssertions(size_t before);

  /**
   * Any variable in an assertion that is declared as a subtype type
   * (predicate subtype or integer subrange type) must be constrained
   * to be in that type.
   */
  void constrainSubtypes(TNode n, std::vector<Node>& assertions)
    throw();

  // trace nodes back to their assertions using CircuitPropagator's BackEdgesMap
  void traceBackToAssertions(const std::vector<Node>& nodes, std::vector<TNode>& assertions);
  // remove conjuncts in toRemove from conjunction n; return # of removed conjuncts
  size_t removeFromConjunction(Node& n, const std::hash_set<unsigned long>& toRemove);

  // scrub miplib encodings
  void doMiplibTrick();

  /**
   * Perform non-clausal simplification of a Node.  This involves
   * Theory implementations, but does NOT involve the SAT solver in
   * any way.
   *
   * Returns false if the formula simplifies to "false"
   */
  bool simplifyAssertions() throw(TypeCheckingException, LogicException);

public:

  SmtEnginePrivate(SmtEngine& smt) :
    d_smt(smt),
    d_assertionsToPreprocess(),
    d_nonClausalLearnedLiterals(),
    d_realAssertionsEnd(0),
    d_booleanTermConverter(NULL),
    d_propagator(d_nonClausalLearnedLiterals, true, true),
    d_propagatorNeedsFinish(false),
    d_assertionsToCheck(),
    d_assertionsProcessed(smt.d_userContext, false),
    d_substitutionsIndex(smt.d_userContext, 0),
    d_fakeContext(),
    d_abstractValueMap(&d_fakeContext),
    d_abstractValues(),
    d_divByZero(),
    d_intDivByZero(),
    d_modZero(),
    d_simplifyAssertionsDepth(0),
    d_iteSkolemMap(),
    d_iteRemover(smt.d_userContext),
    d_topLevelSubstitutions(smt.d_userContext)
  {
    d_smt.d_nodeManager->subscribeEvents(this);
    d_true = NodeManager::currentNM()->mkConst(true);
  }

  ~SmtEnginePrivate() {
    if(d_propagatorNeedsFinish) {
      d_propagator.finish();
      d_propagatorNeedsFinish = false;
    }
    if(d_booleanTermConverter != NULL) {
      delete d_booleanTermConverter;
      d_booleanTermConverter = NULL;
    }
    d_smt.d_nodeManager->unsubscribeEvents(this);
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
    d_realAssertionsEnd = 0;
    d_iteSkolemMap.clear();
  }

  /**
   * Adds a formula to the current context.  Action here depends on
   * the SimplificationMode (in the current Options scope); the
   * formula might be pushed out to the propositional layer
   * immediately, or it might be simplified and kept, or it might not
   * even be simplified.
   */
  void addFormula(TNode n)
    throw(TypeCheckingException, LogicException);

  /**
   * Return the uinterpreted function symbol corresponding to division-by-zero
   * for this particular bit-width
   * @param k should be UREM or UDIV
   * @param width
   *
   * @return
   */
  Node getBVDivByZero(Kind k, unsigned width);

  /**
   * Returns the node modeling the division-by-zero semantics of node n.
   *
   * @param n
   *
   * @return
   */
  Node expandBVDivByZero(TNode n);

  /**
   * Expand definitions in n.
   */
  Node expandDefinitions(TNode n, hash_map<Node, Node, NodeHashFunction>& cache)
    throw(TypeCheckingException, LogicException);

  /**
   * Rewrite Boolean terms in a Node.
   */
  Node rewriteBooleanTerms(TNode n);

  /**
   * Simplify node "in" by expanding definitions and applying any
   * substitutions learned from preprocessing.
   */
  Node simplify(TNode in) {
    // Substitute out any abstract values in ex.
    // Expand definitions.
    hash_map<Node, Node, NodeHashFunction> cache;
    Node n = expandDefinitions(in, cache).toExpr();
    // Make sure we've done all preprocessing, etc.
    Assert(d_assertionsToCheck.size() == 0 && d_assertionsToPreprocess.size() == 0);
    return applySubstitutions(n).toExpr();
  }

  /**
   * Pre-skolemize quantifiers.
   */
  Node preSkolemizeQuantifiers(Node n, bool polarity, std::vector<Node>& fvs);

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
    return val;
  }

  std::hash_map<Node, Node, NodeHashFunction> rewriteApplyToConstCache;
  Node rewriteApplyToConst(TNode n) {
    Trace("rewriteApplyToConst") << "rewriteApplyToConst :: " << n << std::endl;

    if(n.getMetaKind() == kind::metakind::CONSTANT || n.getMetaKind() == kind::metakind::VARIABLE) {
      return n;
    }

    if(rewriteApplyToConstCache.find(n) != rewriteApplyToConstCache.end()) {
      Trace("rewriteApplyToConst") << "in cache :: " << rewriteApplyToConstCache[n] << std::endl;
      return rewriteApplyToConstCache[n];
    }
    if(n.getKind() == kind::APPLY_UF) {
      if(n.getNumChildren() == 1 && n[0].isConst() && n[0].getType().isInteger()) {
        stringstream ss;
        ss << n.getOperator() << "_";
        if(n[0].getConst<Rational>() < 0) {
          ss << "m" << -n[0].getConst<Rational>();
        } else {
          ss << n[0];
        }
        Node newvar = NodeManager::currentNM()->mkSkolem(ss.str(), n.getType(), "rewriteApplyToConst skolem", NodeManager::SKOLEM_EXACT_NAME);
        rewriteApplyToConstCache[n] = newvar;
        Trace("rewriteApplyToConst") << "made :: " << newvar << std::endl;
        return newvar;
      } else {
        stringstream ss;
        ss << "The rewrite-apply-to-const preprocessor is currently limited;\n"
           << "it only works if all function symbols are unary and with Integer\n"
           << "domain, and all applications are to integer values.\n"
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
    rewriteApplyToConstCache[n] = rewr;
    Trace("rewriteApplyToConst") << "built :: " << rewr << std::endl;
    return rewr;
  }

};/* class SmtEnginePrivate */

}/* namespace CVC4::smt */

SmtEngine::SmtEngine(ExprManager* em) throw() :
  d_context(em->getContext()),
  d_userLevels(),
  d_userContext(new UserContext()),
  d_exprManager(em),
  d_nodeManager(d_exprManager->getNodeManager()),
  d_decisionEngine(NULL),
  d_theoryEngine(NULL),
  d_propEngine(NULL),
  d_proofManager(NULL),
  d_definedFunctions(NULL),
  d_assertionList(NULL),
  d_assignments(NULL),
  d_modelGlobalCommands(),
  d_modelCommands(NULL),
  d_dumpCommands(),
  d_logic(),
  d_pendingPops(0),
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
  d_private(NULL),
  d_statisticsRegistry(NULL),
  d_stats(NULL) {

  SmtScope smts(this);
  d_private = new smt::SmtEnginePrivate(*this);
  d_statisticsRegistry = new StatisticsRegistry();
  d_stats = new SmtEngineStatistics();

  PROOF( d_proofManager = new ProofManager(); );

  // We have mutual dependency here, so we add the prop engine to the theory
  // engine later (it is non-essential there)
  d_theoryEngine = new TheoryEngine(d_context, d_userContext, d_private->d_iteRemover, const_cast<const LogicInfo&>(d_logic));

  // Add the theories
  for(TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    TheoryConstructor::addTheory(d_theoryEngine, id);
  }

  // global push/pop around everything, to ensure proper destruction
  // of context-dependent data structures
  d_userContext->push();
  d_context->push();

  d_definedFunctions = new(true) DefinedFunctionMap(d_userContext);
  d_modelCommands = new(true) smt::CommandList(d_userContext);
}

void SmtEngine::finishInit() {
  d_decisionEngine = new DecisionEngine(d_context, d_userContext);
  d_decisionEngine->init();   // enable appropriate strategies

  d_propEngine = new PropEngine(d_theoryEngine, d_decisionEngine, d_context, d_userContext);

  d_theoryEngine->setPropEngine(d_propEngine);
  d_theoryEngine->setDecisionEngine(d_decisionEngine);
  d_theoryEngine->finishInit();

  // [MGD 10/20/2011] keep around in incremental mode, due to a
  // cleanup ordering issue and Nodes/TNodes.  If SAT is popped
  // first, some user-context-dependent TNodes might still exist
  // with rc == 0.
  if(options::interactive() ||
     options::incrementalSolving()) {
    // In the case of incremental solving, we appear to need these to
    // ensure the relevant Nodes remain live.
    d_assertionList = new(true) AssertionList(d_userContext);
  }

  // dump out a set-logic command
  if(Dump.isOn("benchmark")) {
    // Dump("benchmark") << SetBenchmarkLogicCommand(logic.getLogicString());
    LogicInfo everything;
    everything.lock();
    Dump("benchmark") << CommentCommand("CVC4 always dumps the most general, \"all-supported\" logic (below), as some internals might require the use of a logic more general than the input.")
                      << SetBenchmarkLogicCommand(everything.getLogicString());
  }

  // dump out any pending declaration commands
  for(unsigned i = 0; i < d_dumpCommands.size(); ++i) {
    Dump("declarations") << *d_dumpCommands[i];
    delete d_dumpCommands[i];
  }
  d_dumpCommands.clear();

  if(options::perCallResourceLimit() != 0) {
    setResourceLimit(options::perCallResourceLimit(), false);
  }
  if(options::cumulativeResourceLimit() != 0) {
    setResourceLimit(options::cumulativeResourceLimit(), true);
  }
  if(options::perCallMillisecondLimit() != 0) {
    setTimeLimit(options::perCallMillisecondLimit(), false);
  }
  if(options::cumulativeMillisecondLimit() != 0) {
    setTimeLimit(options::cumulativeMillisecondLimit(), true);
  }

  PROOF( ProofManager::currentPM()->setLogic(d_logic.getLogicString()); );
}

void SmtEngine::finalOptionsAreSet() {
  if(d_fullyInited) {
    return;
  }

  if(options::bitvectorEagerBitblast()) {
    // Eager solver should use the internal decision strategy
    options::decisionMode.set(DECISION_STRATEGY_INTERNAL);
  }

  if(options::checkModels()) {
    if(! options::interactive()) {
      Notice() << "SmtEngine: turning on interactive-mode to support check-models" << endl;
      setOption("interactive-mode", SExpr("true"));
    }
  }
  if(options::produceAssignments() && !options::produceModels()) {
    Notice() << "SmtEngine: turning on produce-models to support produce-assignments" << endl;
    setOption("produce-models", SExpr("true"));
  }

  if(! d_logic.isLocked()) {
    // ensure that our heuristics are properly set up
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

SmtEngine::~SmtEngine() throw() {
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
    }
    d_dumpCommands.clear();

    if(d_modelCommands != NULL) {
      d_modelCommands->deleteSelf();
    }

    d_definedFunctions->deleteSelf();

    delete d_theoryEngine;
    delete d_propEngine;
    delete d_decisionEngine;

    delete d_stats;
    delete d_statisticsRegistry;

    delete d_private;

    delete d_userContext;

  } catch(Exception& e) {
    Warning() << "CVC4 threw an exception during cleanup." << endl
              << e << endl;
  }
}

void SmtEngine::setLogic(const LogicInfo& logic) throw(ModalException) {
  SmtScope smts(this);
  if(d_fullyInited) {
    throw ModalException("Cannot set logic in SmtEngine after the engine has finished initializing");
  }
  d_logic = logic;
  setLogicInternal();
}

void SmtEngine::setLogic(const std::string& s) throw(ModalException, LogicException) {
  SmtScope smts(this);
  try {
    setLogic(LogicInfo(s));
  } catch(IllegalArgumentException& e) {
    throw LogicException(e.what());
  }
}

void SmtEngine::setLogic(const char* logic) throw(ModalException, LogicException) {
  setLogic(string(logic));
}

LogicInfo SmtEngine::getLogicInfo() const {
  return d_logic;
}

// This function is called when d_logic has just been changed.
// The LogicInfo isn't passed in explicitly, because that might
// tempt people in the code to use the (potentially unlocked)
// version that's passed in, leading to assert-fails in certain
// uses of the CVC4 library.
void SmtEngine::setLogicInternal() throw() {
  Assert(!d_fullyInited, "setting logic in SmtEngine but the engine has already finished initializing for this run");

  d_logic.lock();

  // Set the options for the theoryOf
  if(!options::theoryOfMode.wasSetByUser()) {
    if(d_logic.isSharingEnabled() && !d_logic.isTheoryEnabled(THEORY_BV) && !d_logic.isTheoryEnabled(THEORY_STRINGS)) {
      Trace("smt") << "setting theoryof-mode to term-based" << endl;
      options::theoryOfMode.set(THEORY_OF_TERM_BASED);
    }
  }


  // for strings
  if(options::stringExp()) {
    if( !d_logic.isQuantified() ) {
      d_logic = d_logic.getUnlockedCopy();
      d_logic.enableQuantifiers();
      d_logic.lock();
      Trace("smt") << "turning on quantifier logic, for strings-exp" << std::endl;
    }
    if(! options::finiteModelFind.wasSetByUser()) {
      options::finiteModelFind.set( true );
      Trace("smt") << "turning on finite-model-find, for strings-exp" << std::endl;
    }
    if(! options::fmfBoundInt.wasSetByUser()) {
      options::fmfBoundInt.set( true );
      Trace("smt") << "turning on fmf-bound-int, for strings-exp" << std::endl;
    }
    if(! options::stringFMF.wasSetByUser()) {
      options::stringFMF.set( true );
      Trace("smt") << "turning on strings-fmf, for strings-exp" << std::endl;
    }
  }

  // by default, symmetry breaker is on only for QF_UF
  if(! options::ufSymmetryBreaker.wasSetByUser()) {
    bool qf_uf = d_logic.isPure(THEORY_UF) && !d_logic.isQuantified();
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
  if(d_logic.isTheoryEnabled(THEORY_ARRAY) && !d_logic.isQuantified()) {
    Theory::setUninterpretedSortOwner(THEORY_ARRAY);
  } else {
    Theory::setUninterpretedSortOwner(THEORY_UF);
  }
  // Turn on ite simplification for QF_LIA and QF_AUFBV
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
      (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_UF) && d_logic.isTheoryEnabled(THEORY_BV));
    Trace("smt") << "setting repeat simplification to " << repeatSimp << endl;
    options::repeatSimp.set(repeatSimp);
  }
  // Turn on unconstrained simplification for QF_AUFBV
  if(! options::unconstrainedSimp.wasSetByUser() || options::incrementalSolving()) {
    //    bool qf_sat = d_logic.isPure(THEORY_BOOL) && !d_logic.isQuantified();
    //    bool uncSimp = false && !qf_sat && !options::incrementalSolving();
    bool uncSimp = !options::incrementalSolving() && !d_logic.isQuantified() && !options::produceModels() && !options::checkModels() &&
      (d_logic.isTheoryEnabled(THEORY_ARRAY) && d_logic.isTheoryEnabled(THEORY_BV));
    Trace("smt") << "setting unconstrained simplification to " << uncSimp << endl;
    options::unconstrainedSimp.set(uncSimp);
  }
  // Unconstrained simp currently does *not* support model generation
  if (options::unconstrainedSimp.wasSetByUser() && options::unconstrainedSimp()) {
    if (options::produceModels()) {
      Notice() << "SmtEngine: turning off produce-models to support unconstrainedSimp" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::checkModels()) {
      Notice() << "SmtEngine: turning off check-models to support unconstrainedSimp" << endl;
      setOption("check-models", SExpr("false"));
    }
  }
  // Turn on arith rewrite equalities only for pure arithmetic
  if(! options::arithRewriteEq.wasSetByUser()) {
    bool arithRewriteEq = d_logic.isPure(THEORY_ARITH) && !d_logic.isQuantified();
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
  // Turn on justification heuristic of the decision engine for QF_BV and QF_AUFBV
  // and also use it in stop-only mode for QF_AUFLIA, QF_LRA and Quantifiers
  // BUT use neither in ALL_SUPPORTED mode (since it doesn't yet work well
  // with incrementality)
  if(!options::decisionMode.wasSetByUser()) {
    decision::DecisionMode decMode =
      // ALL_SUPPORTED
      d_logic.hasEverything() ? decision::DECISION_STRATEGY_INTERNAL :
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
      // ALL_SUPPORTED
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
         ) ||
        // Quantifiers
        d_logic.isQuantified()
        ? true : false
      );

    Trace("smt") << "setting decision mode to " << decMode << endl;
    options::decisionMode.set(decMode);
    options::decisionStopOnly.set(stoponly);
  }

  //for finite model finding
  if( ! options::instWhenMode.wasSetByUser()){
    //instantiate only on last call
    if( options::fmfInstEngine() ){
      Trace("smt") << "setting inst when mode to LAST_CALL" << endl;
      options::instWhenMode.set( INST_WHEN_LAST_CALL );
    }
  }
  if ( options::fmfBoundInt() ){
    if( options::mbqiMode()!=quantifiers::MBQI_NONE &&
        options::mbqiMode()!=quantifiers::MBQI_FMC_INTERVAL ){
      //if bounded integers are set, must use full model check for MBQI
      options::mbqiMode.set( quantifiers::MBQI_FMC );
    }
  }
  if( options::mbqiMode()==quantifiers::MBQI_INTERVAL ){
    //must do pre-skolemization
    options::preSkolemQuant.set( true );
  }
  if( options::ufssSymBreak() ){
    options::sortInference.set( true );
  }

  //until bugs 371,431 are fixed
  if( ! options::minisatUseElim.wasSetByUser()){
    if( d_logic.isQuantified() || options::produceModels() || options::checkModels() ){
      options::minisatUseElim.set( false );
    }
  }
  else if (options::minisatUseElim()) {
    if (options::produceModels()) {
      Notice() << "SmtEngine: turning off produce-models to support minisatUseElim" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::checkModels()) {
      Notice() << "SmtEngine: turning off check-models to support minisatUseElim" << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  // For now, these array theory optimizations do not support model-building
  if (options::produceModels() || options::checkModels()) {
    options::arraysOptimizeLinear.set(false);
    options::arraysLazyRIntro1.set(false);
  }

  // Non-linear arithmetic does not support models
  if (d_logic.isTheoryEnabled(THEORY_ARITH) &&
      !d_logic.isLinear()) {
    if (options::produceModels()) {
      Warning() << "SmtEngine: turning off produce-models because unsupported for nonlinear arith" << endl;
      setOption("produce-models", SExpr("false"));
    }
    if (options::checkModels()) {
      Warning() << "SmtEngine: turning off check-models because unsupported for nonlinear arith" << endl;
      setOption("check-models", SExpr("false"));
    }
  }

  if (options::incrementalSolving() && options::proof()) {
    Warning() << "SmtEngine: turning off incremental solving mode (not yet supported with --proof" << endl;
    setOption("incremental", SExpr("false"));
  }

  // datatypes theory should assign values to all datatypes terms if logic is quantified
  if (d_logic.isQuantified() && d_logic.isTheoryEnabled(THEORY_DATATYPES)) {
    if( !options::dtForceAssignment.wasSetByUser() ){
      options::dtForceAssignment.set(true);
    }
  }
}

void SmtEngine::setInfo(const std::string& key, const CVC4::SExpr& value)
  throw(OptionException, ModalException) {

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
        (value.getValue() == "2") ) {
      // supported SMT-LIB version
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

CVC4::SExpr SmtEngine::getInfo(const std::string& key) const
  throw(OptionException, ModalException) {

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
    return stats;
  } else if(key == "error-behavior") {
    // immediate-exit | continued-execution
    return SExpr::Keyword("continued-execution");
  } else if(key == "name") {
    return Configuration::getName();
  } else if(key == "version") {
    return Configuration::getVersionString();
  } else if(key == "authors") {
    return Configuration::about();
  } else if(key == "status") {
    // sat | unsat | unknown
    switch(d_status.asSatisfiabilityResult().isSat()) {
    case Result::SAT:
      return SExpr::Keyword("sat");
    case Result::UNSAT:
      return SExpr::Keyword("unsat");
    default:
      return SExpr::Keyword("unknown");
    }
  } else if(key == "reason-unknown") {
    if(!d_status.isNull() && d_status.isUnknown()) {
      stringstream ss;
      ss << d_status.whyUnknown();
      string s = ss.str();
      transform(s.begin(), s.end(), s.begin(), ::tolower);
      return SExpr::Keyword(s);
    } else {
      throw ModalException("Can't get-info :reason-unknown when the "
                           "last result wasn't unknown!");
    }
  } else if(key == "all-options") {
    // get the options, like all-statistics
    return Options::current().getOptions();
  } else {
    throw UnrecognizedOptionException();
  }
}

void SmtEngine::defineFunction(Expr func,
                               const std::vector<Expr>& formals,
                               Expr formula) {
  Trace("smt") << "SMT defineFunction(" << func << ")" << endl;
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

  stringstream ss;
  ss << Expr::setlanguage(Expr::setlanguage::getLanguage(Dump.getStream()))
     << func;
  DefineFunctionCommand c(ss.str(), func, formals, formula);
  addToModelCommandAndDump(c, ExprManager::VAR_FLAG_DEFINED, true, "declarations");

  SmtScope smts(this);

  // Substitute out any abstract values in formula
  Expr form = d_private->substituteAbstractValues(Node::fromExpr(formula)).toExpr();

  // type check body
  Type formulaType = form.getType(options::typeChecking());

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
         << "Declared type  : " << funcType << "\n"
         << "The definition : " << formula << "\n"
         << "Definition type: " << formulaType;
      throw TypeCheckingException(func, ss.str());
    }
  }
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


Node SmtEnginePrivate::getBVDivByZero(Kind k, unsigned width) {
  NodeManager* nm = d_smt.d_nodeManager;
  if (k == kind::BITVECTOR_UDIV) {
    if (d_BVDivByZero.find(width) == d_BVDivByZero.end()) {
      // lazily create the function symbols
      ostringstream os;
      os << "BVUDivByZero_" << width;
      Node divByZero = nm->mkSkolem(os.str(),
                                    nm->mkFunctionType(nm->mkBitVectorType(width), nm->mkBitVectorType(width)),
                                    "partial bvudiv", NodeManager::SKOLEM_EXACT_NAME);
      d_BVDivByZero[width] = divByZero;
    }
    return d_BVDivByZero[width];
  }
  else if (k == kind::BITVECTOR_UREM) {
    if (d_BVRemByZero.find(width) == d_BVRemByZero.end()) {
      ostringstream os;
      os << "BVURemByZero_" << width;
      Node divByZero = nm->mkSkolem(os.str(),
                                    nm->mkFunctionType(nm->mkBitVectorType(width), nm->mkBitVectorType(width)),
                                    "partial bvurem", NodeManager::SKOLEM_EXACT_NAME);
      d_BVRemByZero[width] = divByZero;
    }
    return d_BVRemByZero[width];
  }

  Unreachable();
}


Node SmtEnginePrivate::expandBVDivByZero(TNode n) {
  // we only deal wioth the unsigned division operators as the signed ones should have been
  // expanded in terms of the unsigned operators
  NodeManager* nm = d_smt.d_nodeManager;
  unsigned width = n.getType().getBitVectorSize();
  Node divByZero = getBVDivByZero(n.getKind(), width);
  TNode num = n[0], den = n[1];
  Node den_eq_0 = nm->mkNode(kind::EQUAL, den, nm->mkConst(BitVector(width, Integer(0))));
  Node divByZeroNum = nm->mkNode(kind::APPLY_UF, divByZero, num);
  Node divTotalNumDen = nm->mkNode(n.getKind() == kind::BITVECTOR_UDIV ? kind::BITVECTOR_UDIV_TOTAL :
                                   kind::BITVECTOR_UREM_TOTAL, num, den);
  Node node = nm->mkNode(kind::ITE, den_eq_0, divByZeroNum, divTotalNumDen);
  if(!d_smt.d_logic.isTheoryEnabled(THEORY_UF)) {
    d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
    d_smt.d_logic.enableTheory(THEORY_UF);
    d_smt.d_logic.lock();
  }
  return node;
}


Node SmtEnginePrivate::expandDefinitions(TNode n, hash_map<Node, Node, NodeHashFunction>& cache)
  throw(TypeCheckingException, LogicException) {

  stack< triple<Node, Node, bool> > worklist;
  stack<Node> result;
  worklist.push(make_triple(Node(n), Node(n), false));

  do {
    n = worklist.top().first;
    Node node = worklist.top().second;
    bool childrenPushed = worklist.top().third;
    worklist.pop();

    if(!childrenPushed) {
      Kind k = n.getKind();

      if(k != kind::APPLY && n.getNumChildren() == 0) {
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
      hash_map<Node, Node, NodeHashFunction>::iterator cacheHit = cache.find(n);
      if(cacheHit != cache.end()) {
        TNode ret = (*cacheHit).second;
        result.push(ret.isNull() ? n : ret);
        continue;
      }

      // otherwise expand it

      NodeManager* nm = d_smt.d_nodeManager;
      // FIXME: this theory-specific code should be factored out of the
      // SmtEngine, somehow
      switch(k) {
      case kind::BITVECTOR_SDIV:
      case kind::BITVECTOR_SREM:
      case kind::BITVECTOR_SMOD:
        node = bv::TheoryBVRewriter::eliminateBVSDiv(node);
        break;

      case kind::BITVECTOR_UDIV:
      case kind::BITVECTOR_UREM:
        node = expandBVDivByZero(node);
        break;

	  //case kind::STRING_CHARAT:
	  //case kind::STRING_SUBSTR:

      case kind::DIVISION: {
        // partial function: division
        if(d_divByZero.isNull()) {
          d_divByZero = nm->mkSkolem("divByZero", nm->mkFunctionType(nm->realType(), nm->realType()),
                                     "partial real division", NodeManager::SKOLEM_EXACT_NAME);
          if(!d_smt.d_logic.isTheoryEnabled(THEORY_UF)) {
            d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
            d_smt.d_logic.enableTheory(THEORY_UF);
            d_smt.d_logic.lock();
          }
        }
        TNode num = n[0], den = n[1];
        Node den_eq_0 = nm->mkNode(kind::EQUAL, den, nm->mkConst(Rational(0)));
        Node divByZeroNum = nm->mkNode(kind::APPLY_UF, d_divByZero, num);
        Node divTotalNumDen = nm->mkNode(kind::DIVISION_TOTAL, num, den);
        node = nm->mkNode(kind::ITE, den_eq_0, divByZeroNum, divTotalNumDen);
        break;
      }

      case kind::INTS_DIVISION: {
        // partial function: integer div
        if(d_intDivByZero.isNull()) {
          d_intDivByZero = nm->mkSkolem("intDivByZero", nm->mkFunctionType(nm->integerType(), nm->integerType()),
                                        "partial integer division", NodeManager::SKOLEM_EXACT_NAME);
          if(!d_smt.d_logic.isTheoryEnabled(THEORY_UF)) {
            d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
            d_smt.d_logic.enableTheory(THEORY_UF);
            d_smt.d_logic.lock();
          }
        }
        TNode num = n[0], den = n[1];
        Node den_eq_0 = nm->mkNode(kind::EQUAL, den, nm->mkConst(Rational(0)));
        Node intDivByZeroNum = nm->mkNode(kind::APPLY_UF, d_intDivByZero, num);
        Node intDivTotalNumDen = nm->mkNode(kind::INTS_DIVISION_TOTAL, num, den);
        node = nm->mkNode(kind::ITE, den_eq_0, intDivByZeroNum, intDivTotalNumDen);
        break;
      }

      case kind::INTS_MODULUS: {
        // partial function: mod
        if(d_modZero.isNull()) {
          d_modZero = nm->mkSkolem("modZero", nm->mkFunctionType(nm->integerType(), nm->integerType()),
                                   "partial modulus", NodeManager::SKOLEM_EXACT_NAME);
          if(!d_smt.d_logic.isTheoryEnabled(THEORY_UF)) {
            d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
            d_smt.d_logic.enableTheory(THEORY_UF);
            d_smt.d_logic.lock();
          }
        }
        TNode num = n[0], den = n[1];
        Node den_eq_0 = nm->mkNode(kind::EQUAL, den, nm->mkConst(Rational(0)));
        Node modZeroNum = nm->mkNode(kind::APPLY_UF, d_modZero, num);
        Node modTotalNumDen = nm->mkNode(kind::INTS_MODULUS_TOTAL, num, den);
        node = nm->mkNode(kind::ITE, den_eq_0, modZeroNum, modTotalNumDen);
        break;
      }

      case kind::ABS: {
        Node out = nm->mkNode(kind::ITE, nm->mkNode(kind::LT, node[0], nm->mkConst(Rational(0))), nm->mkNode(kind::UMINUS, node[0]), node[0]);
        cache[n] = out;
        result.push(out);
        continue;
      }

      case kind::APPLY: {
        // application of a user-defined symbol
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
          throw TypeCheckingException(n.toExpr(), string("Undefined function: `") + func.toString() + "'");
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
        result.push(expanded);
        continue;
      }

      default:
        // unknown kind for expansion, just iterate over the children
        node = n;
      }

      // there should be children here, otherwise we short-circuited a result-push/continue, above
      Assert(node.getNumChildren() > 0);

      // the partial functions can fall through, in which case we still
      // consider their children
      worklist.push(make_triple(Node(n), node, true));

      for(size_t i = 0; i < node.getNumChildren(); ++i) {
        worklist.push(make_triple(node[i], node[i], false));
      }

    } else {

      Debug("expand") << "cons : " << node << endl;
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
      cache[n] = n == node ? Node::null() : node;
      result.push(node);
    }
  } while(!worklist.empty());

  AlwaysAssert(result.size() == 1);

  return result.top();
}


struct ContainsQuantAttributeId {};
typedef expr::Attribute<ContainsQuantAttributeId, uint64_t> ContainsQuantAttribute;

// check if the given node contains a universal quantifier
static bool containsQuantifiers(Node n) {
  if( n.hasAttribute(ContainsQuantAttribute()) ){
    return n.getAttribute(ContainsQuantAttribute())==1;
  } else if(n.getKind() == kind::FORALL) {
    return true;
  } else {
    bool cq = false;
    for( unsigned i = 0; i < n.getNumChildren(); ++i ){
      if( containsQuantifiers(n[i]) ){
        cq = true;
        break;
      }
    }
    ContainsQuantAttribute cqa;
    n.setAttribute(cqa, cq ? 1 : 0);
    return cq;
  }
}

Node SmtEnginePrivate::preSkolemizeQuantifiers( Node n, bool polarity, std::vector< Node >& fvs ){
  Trace("pre-sk") << "Pre-skolem " << n << " " << polarity << " " << fvs.size() << endl;
  if( n.getKind()==kind::NOT ){
    Node nn = preSkolemizeQuantifiers( n[0], !polarity, fvs );
    return nn.negate();
  }else if( n.getKind()==kind::FORALL ){
    if( polarity ){
      vector< Node > children;
      children.push_back( n[0] );
      //add children to current scope
      vector< Node > fvss;
      fvss.insert( fvss.begin(), fvs.begin(), fvs.end() );
      for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
        fvss.push_back( n[0][i] );
      }
      //process body
      children.push_back( preSkolemizeQuantifiers( n[1], polarity, fvss ) );
      if( n.getNumChildren()==3 ){
        children.push_back( n[2] );
      }
      //return processed quantifier
      return NodeManager::currentNM()->mkNode( kind::FORALL, children );
    }else{
      //process body
      Node nn = preSkolemizeQuantifiers( n[1], polarity, fvs );
      //now, substitute skolems for the variables
      vector< TypeNode > argTypes;
      for( int i=0; i<(int)fvs.size(); i++ ){
        argTypes.push_back( fvs[i].getType() );
      }
      //calculate the variables and substitution
      vector< Node > vars;
      vector< Node > subs;
      for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
        vars.push_back( n[0][i] );
      }
      for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
        //make the new function symbol
        if( argTypes.empty() ){
          Node s = NodeManager::currentNM()->mkSkolem( "sk_$$", n[0][i].getType(), "created during pre-skolemization" );
          subs.push_back( s );
        }else{
          TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, n[0][i].getType() );
          Node op = NodeManager::currentNM()->mkSkolem( "skop_$$", typ, "op created during pre-skolemization" );
          //DOTHIS: set attribute on op, marking that it should not be selected as trigger
          vector< Node > funcArgs;
          funcArgs.push_back( op );
          funcArgs.insert( funcArgs.end(), fvs.begin(), fvs.end() );
          subs.push_back( NodeManager::currentNM()->mkNode( kind::APPLY_UF, funcArgs ) );
        }
      }
      //apply substitution
      nn = nn.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      return nn;
    }
  }else{
    //check if it contains a quantifier as a subterm
    //if so, we will write this node
    if( containsQuantifiers( n ) ){
      if( n.getType().isBoolean() ){
        if( n.getKind()==kind::ITE || n.getKind()==kind::IFF || n.getKind()==kind::XOR || n.getKind()==kind::IMPLIES ){
          Node nn;
          //must remove structure
          if( n.getKind()==kind::ITE ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                   NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n[1] ),
                   NodeManager::currentNM()->mkNode( kind::OR, n[0], n[2] ) );
          }else if( n.getKind()==kind::IFF || n.getKind()==kind::XOR ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                   NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n.getKind()==kind::XOR ? n[1].notNode() : n[1] ),
                   NodeManager::currentNM()->mkNode( kind::OR, n[0], n.getKind()==kind::XOR ? n[1] : n[1].notNode() ) );
          }else if( n.getKind()==kind::IMPLIES ){
            nn = NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n[1] );
          }
          return preSkolemizeQuantifiers( nn, polarity, fvs );
        }else if( n.getKind()==kind::AND || n.getKind()==kind::OR ){
          vector< Node > children;
          for( int i=0; i<(int)n.getNumChildren(); i++ ){
            children.push_back( preSkolemizeQuantifiers( n[i], polarity, fvs ) );
          }
          return NodeManager::currentNM()->mkNode( n.getKind(), children );
        }else{
          //must pull ite's
        }
      }
    }
    return n;
  }
}

void SmtEnginePrivate::removeITEs() {
  d_smt.finalOptionsAreSet();

  Trace("simplify") << "SmtEnginePrivate::removeITEs()" << endl;

  // Remove all of the ITE occurrences and normalize
  d_iteRemover.run(d_assertionsToCheck, d_iteSkolemMap);
  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
    d_assertionsToCheck[i] = Rewriter::rewrite(d_assertionsToCheck[i]);
  }

}

void SmtEnginePrivate::staticLearning() {
  d_smt.finalOptionsAreSet();

  TimerStat::CodeTimer staticLearningTimer(d_smt.d_stats->d_staticLearningTime);

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

// do dumping (before/after any preprocessing pass)
static void dumpAssertions(const char* key,
                           const std::vector<Node>& assertionList) {
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
  d_smt.finalOptionsAreSet();

  TimerStat::CodeTimer nonclausalTimer(d_smt.d_stats->d_nonclausalSimplificationTime);

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify()" << endl;

  if(d_propagatorNeedsFinish) {
    d_propagator.finish();
    d_propagatorNeedsFinish = false;
  }
  d_propagator.initialize();

  // Assert all the assertions to the propagator
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "asserting to propagator" << endl;
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Assert(Rewriter::rewrite(d_assertionsToPreprocess[i]) == d_assertionsToPreprocess[i]);
    // Don't reprocess substitutions
    if (d_substitutionsIndex > 0 && i == d_substitutionsIndex) {
      continue;
    }
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): asserting " << d_assertionsToPreprocess[i] << endl;
    d_propagator.assertTrue(d_assertionsToPreprocess[i]);
  }

  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "propagating" << endl;
  if (d_propagator.propagate()) {
    // If in conflict, just return false
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "conflict in non-clausal propagation" << endl;
    d_assertionsToPreprocess.clear();
    d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
    d_propagatorNeedsFinish = true;
    return false;
  }

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
    Node learnedLiteralNew = newSubstitutions.apply(learnedLiteral);
    if (learnedLiteral != learnedLiteralNew) {
      learnedLiteral = Rewriter::rewrite(learnedLiteralNew);
    }
    for (;;) {
      learnedLiteralNew = constantPropagations.apply(learnedLiteral);
      if (learnedLiteralNew == learnedLiteral) {
        break;
      }
      ++d_smt.d_stats->d_numConstantProps;
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
        d_assertionsToPreprocess.clear();
        d_assertionsToCheck.push_back(NodeManager::currentNM()->mkConst<bool>(false));
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
  }
  // Resize the learnt
  d_nonClausalLearnedLiterals.resize(j);

  hash_set<TNode, TNodeHashFunction> s;
  Trace("debugging") << "NonClausal simplify pre-preprocess\n";
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Node assertion = d_assertionsToPreprocess[i];
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
    d_assertionsToCheck.push_back(assertion);
    Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                      << "non-clausal preprocessed: "
                      << assertion << endl;
  }
  d_assertionsToPreprocess.clear();

  // If in incremental mode, add substitutions to the list of assertions
  if (d_substitutionsIndex > 0) {
    NodeBuilder<> substitutionsBuilder(kind::AND);
    substitutionsBuilder << d_assertionsToCheck[d_substitutionsIndex];
    pos = newSubstitutions.begin();
    for (; pos != newSubstitutions.end(); ++pos) {
      // Add back this substitution as an assertion
      TNode lhs = (*pos).first, rhs = newSubstitutions.apply((*pos).second);
      Node n = NodeManager::currentNM()->mkNode(lhs.getType().isBoolean() ? kind::IFF : kind::EQUAL, lhs, rhs);
      substitutionsBuilder << n;
      Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): will notify SAT layer of substitution: " << n << endl;
    }
    if (substitutionsBuilder.getNumChildren() > 1) {
      d_assertionsToCheck[d_substitutionsIndex] =
        Rewriter::rewrite(Node(substitutionsBuilder));
    }
  }
  else {
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
  Assert(d_realAssertionsEnd <= d_assertionsToCheck.size());
  learnedBuilder << d_assertionsToCheck[d_realAssertionsEnd - 1];

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
    d_assertionsToCheck[d_realAssertionsEnd - 1] =
      Rewriter::rewrite(Node(learnedBuilder));
  }

  d_propagatorNeedsFinish = true;
  return true;
}


void SmtEnginePrivate::bvToBool() {
  Trace("bv-to-bool") << "SmtEnginePrivate::bvToBool()" << endl;
  std::vector<Node> new_assertions;
  d_smt.d_theoryEngine->ppBvToBool(d_assertionsToCheck, new_assertions);
  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
    d_assertionsToCheck[i] = Rewriter::rewrite(new_assertions[i]);
  }
}

bool SmtEnginePrivate::simpITE() {
  TimerStat::CodeTimer simpITETimer(d_smt.d_stats->d_simpITETime);

  Trace("simplify") << "SmtEnginePrivate::simpITE()" << endl;

  unsigned numAssertionOnEntry = d_assertionsToCheck.size();
  for (unsigned i = 0; i < d_assertionsToCheck.size(); ++i) {
    Node result = d_smt.d_theoryEngine->ppSimpITE(d_assertionsToCheck[i]);
    d_assertionsToCheck[i] = result;
    if(result.isConst() && !result.getConst<bool>()){
      return false;
    }
  }
  bool result = d_smt.d_theoryEngine->donePPSimpITE(d_assertionsToCheck);
  if(numAssertionOnEntry < d_assertionsToCheck.size()){
    compressBeforeRealAssertions(numAssertionOnEntry);
  }
  return result;
}

void SmtEnginePrivate::compressBeforeRealAssertions(size_t before){
  size_t curr = d_assertionsToCheck.size();
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
    intoConjunction.push_back(d_assertionsToCheck[i]);
  }
  d_assertionsToCheck.resize(before);
  size_t lastBeforeItes = d_realAssertionsEnd - 1;
  intoConjunction.push_back(d_assertionsToCheck[lastBeforeItes]);
  Node newLast = util::NaryBuilder::mkAssoc(kind::AND, intoConjunction);
  d_assertionsToCheck[lastBeforeItes] = newLast;
  Assert(d_assertionsToCheck.size() == before);
}

void SmtEnginePrivate::unconstrainedSimp() {
  TimerStat::CodeTimer unconstrainedSimpTimer(d_smt.d_stats->d_unconstrainedSimpTime);

  Trace("simplify") << "SmtEnginePrivate::unconstrainedSimp()" << endl;
  d_smt.d_theoryEngine->ppUnconstrainedSimp(d_assertionsToCheck);
}


void SmtEnginePrivate::constrainSubtypes(TNode top, std::vector<Node>& assertions)
  throw() {

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

size_t SmtEnginePrivate::removeFromConjunction(Node& n, const std::hash_set<unsigned long>& toRemove) {
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
  Assert(d_assertionsToPreprocess.empty());
  Assert(d_realAssertionsEnd == d_assertionsToCheck.size());
  Assert(!options::incrementalSolving());

  const booleans::CircuitPropagator::BackEdgesMap& backEdges = d_propagator.getBackEdges();
  hash_set<unsigned long> removeAssertions;

  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConst(Rational(0)), one = nm->mkConst(Rational(1));

  hash_map<TNode, Node, TNodeHashFunction> intVars;
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
              d_assertionsToCheck.push_back(Rewriter::rewrite(geq.andNode(leq)));
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
          d_assertionsToCheck.push_back(newAssertion);
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
      if(removeAssertions.find(d_assertionsToCheck[i].getId()) != removeAssertions.end()) {
        Debug("miplib") << "SmtEnginePrivate::simplify(): - removing " << d_assertionsToCheck[i] << endl;
        d_assertionsToCheck[i] = d_true;
        ++d_smt.d_stats->d_numMiplibAssertionsRemoved;
      } else if(d_assertionsToCheck[i].getKind() == kind::AND) {
        size_t removals = removeFromConjunction(d_assertionsToCheck[i], removeAssertions);
        if(removals > 0) {
          Debug("miplib") << "SmtEnginePrivate::simplify(): - reduced " << d_assertionsToCheck[i] << endl;
          Debug("miplib") << "SmtEnginePrivate::simplify(): -      by " << removals << " conjuncts" << endl;
          d_smt.d_stats->d_numMiplibAssertionsRemoved += removals;
        }
      }
      Debug("miplib") << "had: " << d_assertionsToCheck[i] << endl;
      d_assertionsToCheck[i] = Rewriter::rewrite(d_topLevelSubstitutions.apply(d_assertionsToCheck[i]));
      Debug("miplib") << "now: " << d_assertionsToCheck[i] << endl;
    }
  } else {
    Debug("miplib") << "SmtEnginePrivate::simplify(): miplib pass found nothing." << endl;
  }
  d_realAssertionsEnd = d_assertionsToCheck.size();
}


// returns false if simplification led to "false"
bool SmtEnginePrivate::simplifyAssertions()
  throw(TypeCheckingException, LogicException) {
  Assert(d_smt.d_pendingPops == 0);
  try {
    ScopeCounter depth(d_simplifyAssertionsDepth);

    Trace("simplify") << "SmtEnginePrivate::simplify()" << endl;

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
          d_realAssertionsEnd == d_assertionsToCheck.size() ) {
        Chat() << "...fixing miplib encodings..." << endl;
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "looking for miplib pseudobooleans..." << endl;

        TimerStat::CodeTimer miplibTimer(d_smt.d_stats->d_miplibPassTime);

        doMiplibTrick();
      } else {
        Trace("simplify") << "SmtEnginePrivate::simplify(): "
                          << "skipping miplib pseudobooleans pass (either incrementalSolving is on, or miplib pbs are turned off)..." << endl;
      }
    } else {
      Assert(d_assertionsToCheck.empty());
      d_assertionsToCheck.swap(d_assertionsToPreprocess);
    }

    dumpAssertions("post-nonclausal", d_assertionsToCheck);
    Trace("smt") << "POST nonClausalSimplify" << endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    // Theory preprocessing
    if (d_smt.d_earlyTheoryPP) {
      Chat() << "...doing early theory preprocessing..." << endl;
      TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
      // Call the theory preprocessors
      d_smt.d_theoryEngine->preprocessStart();
      for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
        Assert(Rewriter::rewrite(d_assertionsToCheck[i]) == d_assertionsToCheck[i]);
        d_assertionsToCheck[i] = d_smt.d_theoryEngine->preprocess(d_assertionsToCheck[i]);
        Assert(Rewriter::rewrite(d_assertionsToCheck[i]) == d_assertionsToCheck[i]);
      }
    }

    dumpAssertions("post-theorypp", d_assertionsToCheck);
    Trace("smt") << "POST theoryPP" << endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

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

    dumpAssertions("post-itesimp", d_assertionsToCheck);
    Trace("smt") << "POST iteSimp" << endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    // Unconstrained simplification
    if(options::unconstrainedSimp()) {
      Chat() << "...doing unconstrained simplification..." << endl;
      unconstrainedSimp();
    }

    dumpAssertions("post-unconstrained", d_assertionsToCheck);
    Trace("smt") << "POST unconstrainedSimp" << endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

    if(options::repeatSimp() && options::simplificationMode() != SIMPLIFICATION_MODE_NONE) {
      Chat() << "...doing another round of nonclausal simplification..." << endl;
      Trace("simplify") << "SmtEnginePrivate::simplify(): "
                        << " doing repeated simplification" << endl;
      d_assertionsToCheck.swap(d_assertionsToPreprocess);
      Assert(d_assertionsToCheck.empty());
      bool noConflict = nonClausalSimplify();
      if(!noConflict) {
        return false;
      }
    }

    dumpAssertions("post-repeatsimp", d_assertionsToCheck);
    Trace("smt") << "POST repeatSimp" << endl;
    Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
    Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

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

  // Make sure the prop layer has all of the assertions
  Trace("smt") << "SmtEngine::check(): processing assertions" << endl;
  d_private->processAssertions();

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

  unsigned long millis = 0;
  if(d_timeBudgetCumulative != 0) {
    millis = getTimeRemaining();
    if(millis == 0) {
      return Result(Result::VALIDITY_UNKNOWN, Result::TIMEOUT, d_filename);
    }
  }
  if(d_timeBudgetPerCall != 0 && (millis == 0 || d_timeBudgetPerCall < millis)) {
    millis = d_timeBudgetPerCall;
  }

  unsigned long resource = 0;
  if(d_resourceBudgetCumulative != 0) {
    resource = getResourceRemaining();
    if(resource == 0) {
      return Result(Result::VALIDITY_UNKNOWN, Result::RESOURCEOUT, d_filename);
    }
  }
  if(d_resourceBudgetPerCall != 0 && (resource == 0 || d_resourceBudgetPerCall < resource)) {
    resource = d_resourceBudgetPerCall;
  }

  TimerStat::CodeTimer solveTimer(d_stats->d_solveTime);

  Chat() << "solving..." << endl;
  Trace("smt") << "SmtEngine::check(): running check" << endl;
  Result result = d_propEngine->checkSat(millis, resource);

  // PropEngine::checkSat() returns the actual amount used in these
  // variables.
  d_cumulativeTimeUsed += millis;
  d_cumulativeResourceUsed += resource;

  Trace("limit") << "SmtEngine::check(): cumulative millis " << d_cumulativeTimeUsed
                 << ", conflicts " << d_cumulativeResourceUsed << endl;

  return Result(result, d_filename);
}

Result SmtEngine::quickCheck() {
  Assert(d_fullyInited);
  Trace("smt") << "SMT quickCheck()" << endl;
  return Result(Result::VALIDITY_UNKNOWN, Result::REQUIRES_FULL_CHECK, d_filename);
}


void SmtEnginePrivate::collectSkolems(TNode n, set<TNode>& skolemSet, hash_map<Node, bool, NodeHashFunction>& cache)
{
  hash_map<Node, bool, NodeHashFunction>::iterator it;
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


bool SmtEnginePrivate::checkForBadSkolems(TNode n, TNode skolem, hash_map<Node, bool, NodeHashFunction>& cache)
{
  hash_map<Node, bool, NodeHashFunction>::iterator it;
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

Node SmtEnginePrivate::rewriteBooleanTerms(TNode n) {
  TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_rewriteBooleanTermsTime);
  if(d_booleanTermConverter == NULL) {
    // This needs to be initialized _after_ the whole SMT framework is in place, subscribed
    // to ExprManager notifications, etc.  Otherwise we might miss the "BooleanTerm" datatype
    // definition, and not dump it properly.
    d_booleanTermConverter = new BooleanTermConverter(d_smt);
  }
  Node retval = d_booleanTermConverter->rewriteBooleanTerms(n);
  if(retval != n) {
    switch(booleans::BooleanTermConversionMode mode = options::booleanTermConversionMode()) {
    case booleans::BOOLEAN_TERM_CONVERT_TO_BITVECTORS:
    case booleans::BOOLEAN_TERM_CONVERT_NATIVE:
      if(!d_smt.d_logic.isTheoryEnabled(THEORY_BV)) {
        d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
        d_smt.d_logic.enableTheory(THEORY_BV);
        d_smt.d_logic.lock();
      }
      break;
    case booleans::BOOLEAN_TERM_CONVERT_TO_DATATYPES:
      if(!d_smt.d_logic.isTheoryEnabled(THEORY_DATATYPES)) {
        d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
        d_smt.d_logic.enableTheory(THEORY_DATATYPES);
        d_smt.d_logic.lock();
      }
      break;
    default:
      Unhandled(mode);
    }
  }
  return retval;
}

void SmtEnginePrivate::processAssertions() {
  TimerStat::CodeTimer paTimer(d_smt.d_stats->d_processAssertionsTime);

  Assert(d_smt.d_fullyInited);
  Assert(d_smt.d_pendingPops == 0);

  // Dump the assertions
  dumpAssertions("pre-everything", d_assertionsToPreprocess);

  Trace("smt") << "SmtEnginePrivate::processAssertions()" << endl;

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  Assert(d_assertionsToCheck.size() == 0);

  if (d_assertionsToPreprocess.size() == 0) {
    // nothing to do
    return;
  }

  if (d_assertionsProcessed &&
      ( options::incrementalSolving() ||
        options::simplificationMode() == SIMPLIFICATION_MODE_INCREMENTAL )) {
    // Placeholder for storing substitutions
    d_substitutionsIndex = d_assertionsToPreprocess.size();
    d_assertionsToPreprocess.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  }

  // Add dummy assertion in last position - to be used as a
  // placeholder for any new assertions to get added
  d_assertionsToPreprocess.push_back(NodeManager::currentNM()->mkConst<bool>(true));
  // any assertions added beyond realAssertionsEnd must NOT affect the
  // equisatisfiability
  d_realAssertionsEnd = d_assertionsToPreprocess.size();

  // Assertions are NOT guaranteed to be rewritten by this point

  dumpAssertions("pre-definition-expansion", d_assertionsToPreprocess);
  {
    Chat() << "expanding definitions..." << endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): expanding definitions" << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_definitionExpansionTime);
    hash_map<Node, Node, NodeHashFunction> cache;
    for(unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
      d_assertionsToPreprocess[i] =
        expandDefinitions(d_assertionsToPreprocess[i], cache);
    }
  }
  dumpAssertions("post-definition-expansion", d_assertionsToPreprocess);

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  dumpAssertions("pre-boolean-terms", d_assertionsToPreprocess);
  {
    Chat() << "rewriting Boolean terms..." << endl;
    for(unsigned i = 0, i_end = d_assertionsToPreprocess.size(); i != i_end; ++i) {
      d_assertionsToPreprocess[i] = rewriteBooleanTerms(d_assertionsToPreprocess[i]);
    }
  }
  dumpAssertions("post-boolean-terms", d_assertionsToPreprocess);

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  dumpAssertions("pre-constrain-subtypes", d_assertionsToPreprocess);
  {
    // Any variables of subtype types need to be constrained properly.
    // Careful, here: constrainSubtypes() adds to the back of
    // d_assertionsToPreprocess, but we don't need to reprocess those.
    // We also can't use an iterator, because the vector may be moved in
    // memory during this loop.
    Chat() << "constraining subtypes..." << endl;
    for(unsigned i = 0, i_end = d_assertionsToPreprocess.size(); i != i_end; ++i) {
      constrainSubtypes(d_assertionsToPreprocess[i], d_assertionsToPreprocess);
    }
  }
  dumpAssertions("post-constrain-subtypes", d_assertionsToPreprocess);

  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;

  dumpAssertions("pre-substitution", d_assertionsToPreprocess);

  // Apply the substitutions we already have, and normalize
  Chat() << "applying substitutions..." << endl;
  Trace("simplify") << "SmtEnginePrivate::nonClausalSimplify(): "
                    << "applying substitutions" << endl;
  for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
    Trace("simplify") << "applying to " << d_assertionsToPreprocess[i] << endl;
    d_assertionsToPreprocess[i] =
      Rewriter::rewrite(d_topLevelSubstitutions.apply(d_assertionsToPreprocess[i]));
    Trace("simplify") << "  got " << d_assertionsToPreprocess[i] << endl;
  }
  dumpAssertions("post-substitution", d_assertionsToPreprocess);

  // Assertions ARE guaranteed to be rewritten by this point

  if( d_smt.d_logic.isTheoryEnabled(THEORY_STRINGS) ) {
    CVC4::theory::strings::StringsPreprocess sp;
    sp.simplify( d_assertionsToPreprocess );
    for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
      d_assertionsToPreprocess[i] = Rewriter::rewrite( d_assertionsToPreprocess[i] );
    }
  }
  if( d_smt.d_logic.isQuantified() ){
    dumpAssertions("pre-skolem-quant", d_assertionsToPreprocess);
    if( options::preSkolemQuant() ){
      //apply pre-skolemization to existential quantifiers
      for (unsigned i = 0; i < d_assertionsToPreprocess.size(); ++ i) {
        Node prev = d_assertionsToPreprocess[i];
        vector< Node > fvs;
        d_assertionsToPreprocess[i] = Rewriter::rewrite( preSkolemizeQuantifiers( d_assertionsToPreprocess[i], true, fvs ) );
        if( prev!=d_assertionsToPreprocess[i] ){
          Trace("quantifiers-rewrite") << "*** Pre-skolemize " << prev << endl;
          Trace("quantifiers-rewrite") << "   ...got " << d_assertionsToPreprocess[i] << endl;
        }
      }
    }
    dumpAssertions("post-skolem-quant", d_assertionsToPreprocess);
    if( options::macrosQuant() ){
      //quantifiers macro expansion
      bool success;
      do{
        QuantifierMacros qm;
        success = qm.simplify( d_assertionsToPreprocess, true );
      }while( success );
    }

    Trace("fo-rsn-enable") << std::endl;
    if( options::foPropQuant() ){
      FirstOrderPropagation fop;
      fop.simplify( d_assertionsToPreprocess );
    }
  }

  if( options::sortInference() ){
    //sort inference technique
    d_smt.d_theoryEngine->getSortInference()->simplify( d_assertionsToPreprocess );
  }

  //if( options::quantConflictFind() ){
  //  d_smt.d_theoryEngine->getQuantConflictFind()->registerAssertions( d_assertionsToPreprocess );
  //}

  dumpAssertions("pre-simplify", d_assertionsToPreprocess);
  Chat() << "simplifying assertions..." << endl;
  bool noConflict = simplifyAssertions();
  if(!noConflict){
    ++(d_smt.d_stats->d_simplifiedToFalse);
  }
  dumpAssertions("post-simplify", d_assertionsToCheck);

  dumpAssertions("pre-static-learning", d_assertionsToCheck);
  if(options::doStaticLearning()) {
    // Perform static learning
    Chat() << "doing static learning..." << endl;
    Trace("simplify") << "SmtEnginePrivate::simplify(): "
                      << "performing static learning" << endl;
    staticLearning();
  }
  dumpAssertions("post-static-learning", d_assertionsToCheck);

  // Lift bit-vectors of size 1 to bool
  if(options::bvToBool()) {
    Chat() << "...doing bvToBool..." << endl;
    bvToBool();
  }

  Trace("smt") << "POST bvToBool" << endl;
  Debug("smt") << " d_assertionsToPreprocess: " << d_assertionsToPreprocess.size() << endl;
  Debug("smt") << " d_assertionsToCheck     : " << d_assertionsToCheck.size() << endl;


  dumpAssertions("pre-ite-removal", d_assertionsToCheck);
  {
    Chat() << "removing term ITEs..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_iteRemovalTime);
    // Remove ITEs, updating d_iteSkolemMap
    d_smt.d_stats->d_numAssertionsPre += d_assertionsToCheck.size();
    removeITEs();
    d_smt.d_stats->d_numAssertionsPost += d_assertionsToCheck.size();
  }
  dumpAssertions("post-ite-removal", d_assertionsToCheck);

  dumpAssertions("pre-repeat-simplify", d_assertionsToCheck);
  if(options::repeatSimp()) {
    d_assertionsToCheck.swap(d_assertionsToPreprocess);
    Chat() << "re-simplifying assertions..." << endl;
    ScopeCounter depth(d_simplifyAssertionsDepth);
    noConflict &= simplifyAssertions();
    if (noConflict) {
      // Need to fix up assertion list to maintain invariants:
      // Let Sk be the set of Skolem variables introduced by ITE's.  Let <_sk be the order in which these variables were introduced
      // during ite removal.
      // For each skolem variable sk, let iteExpr = iteMap(sk) be the ite expr mapped to by sk.

      // cache for expression traversal
      hash_map<Node, bool, NodeHashFunction> cache;

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
      builder << d_assertionsToCheck[d_realAssertionsEnd - 1];
      vector<TNode> toErase;
      for (; it != iend; ++it) {
        if (skolemSet.find((*it).first) == skolemSet.end()) {
          TNode iteExpr = d_assertionsToCheck[(*it).second];
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
        builder << d_assertionsToCheck[(*it).second];
        d_assertionsToCheck[(*it).second] = NodeManager::currentNM()->mkConst<bool>(true);
        toErase.push_back((*it).first);
      }
      if(builder.getNumChildren() > 1) {
        while (!toErase.empty()) {
          d_iteSkolemMap.erase(toErase.back());
          toErase.pop_back();
        }
        d_assertionsToCheck[d_realAssertionsEnd - 1] =
          Rewriter::rewrite(Node(builder));
      }
      // For some reason this is needed for some benchmarks, such as
      // http://cvc4.cs.nyu.edu/benchmarks/smtlib2/QF_AUFBV/dwp_formulas/try5_small_difret_functions_dwp_tac.re_node_set_remove_at.il.dwp.smt2
      // Figure it out later
      removeITEs();
      //      Assert(iteRewriteAssertionsEnd == d_assertionsToCheck.size());
    }
  }
  dumpAssertions("post-repeat-simplify", d_assertionsToCheck);

  dumpAssertions("pre-rewrite-apply-to-const", d_assertionsToCheck);
  if(options::rewriteApplyToConst()) {
    Chat() << "Rewriting applies to constants..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      d_assertionsToCheck[i] = Rewriter::rewrite(rewriteApplyToConst(d_assertionsToCheck[i]));
    }
  }
  dumpAssertions("post-rewrite-apply-to-const", d_assertionsToCheck);

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

  dumpAssertions("pre-theory-preprocessing", d_assertionsToCheck);
  {
    Chat() << "theory preprocessing..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_theoryPreprocessTime);
    // Call the theory preprocessors
    d_smt.d_theoryEngine->preprocessStart();
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      d_assertionsToCheck[i] = d_smt.d_theoryEngine->preprocess(d_assertionsToCheck[i]);
    }
  }
  dumpAssertions("post-theory-preprocessing", d_assertionsToCheck);

  // Push the formula to decision engine
  if(noConflict) {
    Chat() << "pushing to decision engine..." << endl;
    Assert(iteRewriteAssertionsEnd == d_assertionsToCheck.size());
    d_smt.d_decisionEngine->addAssertions
      (d_assertionsToCheck, d_realAssertionsEnd, d_iteSkolemMap);
  }

  // end: INVARIANT to maintain: no reordering of assertions or
  // introducing new ones

  dumpAssertions("post-everything", d_assertionsToCheck);

  // Push the formula to SAT
  {
    Chat() << "converting to CNF..." << endl;
    TimerStat::CodeTimer codeTimer(d_smt.d_stats->d_cnfConversionTime);
    for (unsigned i = 0; i < d_assertionsToCheck.size(); ++ i) {
      d_smt.d_propEngine->assertFormula(d_assertionsToCheck[i]);
    }
  }

  d_assertionsProcessed = true;

  d_assertionsToCheck.clear();
  d_iteSkolemMap.clear();
}

void SmtEnginePrivate::addFormula(TNode n)
  throw(TypeCheckingException, LogicException) {

  if (n == d_true) {
    // nothing to do
    return;
  }

  Trace("smt") << "SmtEnginePrivate::addFormula(" << n << ")" << endl;

  // Add the normalized formula to the queue
  d_assertionsToPreprocess.push_back(n);
  //d_assertionsToPreprocess.push_back(Rewriter::rewrite(n));

  // If the mode of processing is incremental prepreocess and assert immediately
  if (options::simplificationMode() == SIMPLIFICATION_MODE_INCREMENTAL) {
    processAssertions();
  }
}

void SmtEngine::ensureBoolean(const Expr& e) throw(TypeCheckingException) {
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

Result SmtEngine::checkSat(const Expr& ex) throw(TypeCheckingException, ModalException, LogicException) {
  Assert(ex.isNull() || ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();

  Trace("smt") << "SmtEngine::checkSat(" << ex << ")" << endl;

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
    // Give it to proof manager
    PROOF( ProofManager::currentPM()->addAssertion(e); );
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
    if(d_assertionList != NULL) {
      d_assertionList->push_back(e);
    }
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

  return r;
}/* SmtEngine::checkSat() */

Result SmtEngine::query(const Expr& ex) throw(TypeCheckingException, ModalException, LogicException) {
  Assert(!ex.isNull());
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT query(" << ex << ")" << endl;

  if(d_queryMade && !options::incrementalSolving()) {
    throw ModalException("Cannot make multiple queries unless "
                         "incremental solving is enabled "
                         "(try --incremental)");
  }

  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  // Ensure that the expression is type-checked at this point, and Boolean
  ensureBoolean(e);
  // Give it to proof manager
  PROOF( ProofManager::currentPM()->addAssertion(e.notExpr()); );

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
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e.notExpr());
  }
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

  return r;
}/* SmtEngine::query() */

Result SmtEngine::assertFormula(const Expr& ex) throw(TypeCheckingException, LogicException) {
  Assert(ex.getExprManager() == d_exprManager);
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();

  PROOF( ProofManager::currentPM()->addAssertion(ex); );

  Trace("smt") << "SmtEngine::assertFormula(" << ex << ")" << endl;

  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();

  ensureBoolean(e);
  if(d_assertionList != NULL) {
    d_assertionList->push_back(e);
  }
  d_private->addFormula(e.getNode());
  return quickCheck().asValidityResult();
}

Node SmtEngine::postprocess(TNode node, TypeNode expectedType) const {
  ModelPostprocessor mpost;
  NodeVisitor<ModelPostprocessor> visitor;
  Node value = visitor.run(mpost, node);
  Debug("boolean-terms") << "postproc: got " << value << " expect type " << expectedType << endl;
  Node realValue = mpost.rewriteAs(value, expectedType);
  Debug("boolean-terms") << "postproc: realval " << realValue << " expect type " << expectedType << endl;
  return realValue;
}

Expr SmtEngine::simplify(const Expr& ex) throw(TypeCheckingException, LogicException) {
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

Expr SmtEngine::expandDefinitions(const Expr& ex) throw(TypeCheckingException, LogicException) {
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
  hash_map<Node, Node, NodeHashFunction> cache;
  Node n = d_private->expandDefinitions(Node::fromExpr(e), cache);
  n = postprocess(n, TypeNode::fromType(e.getType()));
  return n.toExpr();
}

Expr SmtEngine::getValue(const Expr& ex) const throw(ModalException, TypeCheckingException, LogicException) {
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
    throw ModalException(msg);
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
  hash_map<Node, Node, NodeHashFunction> cache;
  n = d_private->expandDefinitions(n, cache);
  n = d_private->rewriteBooleanTerms(n);
  n = Rewriter::rewrite(n);

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
  Assert(resultNode.isNull() || resultNode.getType().isSubtypeOf(expectedType));

  // ensure it's a constant
  Assert(resultNode.getKind() == kind::LAMBDA || resultNode.isConst());

  if(options::abstractValues() && resultNode.getType().isArray()) {
    resultNode = d_private->mkAbstractValue(resultNode);
  }

  return resultNode.toExpr();
}

bool SmtEngine::addToAssignment(const Expr& ex) throw() {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  // Substitute out any abstract values in ex
  Expr e = d_private->substituteAbstractValues(Node::fromExpr(ex)).toExpr();
  Type type = e.getType(options::typeChecking());
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

CVC4::SExpr SmtEngine::getAssignment() throw(ModalException) {
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
    throw ModalException(msg);
  }

  if(d_assignments == NULL) {
    return SExpr(vector<SExpr>());
  }

  vector<SExpr> sexprs;
  TypeNode boolType = d_nodeManager->booleanType();
  TheoryModel* m = d_theoryEngine->getModel();
  for(AssignmentSet::const_iterator i = d_assignments->begin(),
        iend = d_assignments->end();
      i != iend;
      ++i) {
    Assert((*i).getType() == boolType);

    Trace("smt") << "--- getting value of " << *i << endl;

    // Expand, then normalize
    hash_map<Node, Node, NodeHashFunction> cache;
    Node n = d_private->expandDefinitions(*i, cache);
    n = d_private->rewriteBooleanTerms(n);
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
      v.push_back(SExpr::Keyword((*i).getOperator().toString()));
    } else {
      Assert((*i).isVar());
      v.push_back(SExpr::Keyword((*i).toString()));
    }
    v.push_back(SExpr::Keyword(resultNode.toString()));
    sexprs.push_back(v);
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

Model* SmtEngine::getModel() throw(ModalException) {
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
    throw ModalException(msg);
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

void SmtEngine::checkModel(bool hardFailure) {
  // --check-model implies --interactive, which enables the assertion list,
  // so we should be ok.
  Assert(d_assertionList != NULL, "don't have an assertion list to check in SmtEngine::checkModel()");

  TimerStat::CodeTimer checkModelTimer(d_stats->d_checkModelTime);

  // Throughout, we use Notice() to give diagnostic output.
  //
  // If this function is running, the user gave --check-model (or equivalent),
  // and if Notice() is on, the user gave --verbose (or equivalent).

  Notice() << "SmtEngine::checkModel(): generating model" << endl;
  TheoryModel* m = d_theoryEngine->getModel();

  // Check individual theory assertions
  d_theoryEngine->checkTheoryAssertionsWithModel();

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

      // (3) checks complete, add the substitution
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
      hash_map<Node, Node, NodeHashFunction> cache;
      n = d_private->expandDefinitions(n, cache);
    }
    Notice() << "SmtEngine::checkModel(): -- expands to " << n << endl;

    // Apply our model value substitutions.
    Debug("boolean-terms") << "applying subses to " << n << endl;
    n = substitutions.apply(n);
    Debug("boolean-terms") << "++ got " << n << endl;
    Notice() << "SmtEngine::checkModel(): -- substitutes to " << n << endl;

    if(Theory::theoryOf(n) != THEORY_REWRITERULES) {
      // In case it's a quantifier (or contains one), look up its value before
      // simplifying, or the quantifier might be irreparably altered.
      n = m->getValue(n);
    }

    // Simplify the result.
    n = d_private->simplify(n);
    Notice() << "SmtEngine::checkModel(): -- simplifies to  " << n << endl;

    TheoryId thy = Theory::theoryOf(n);
    if(thy == THEORY_REWRITERULES) {
      // Note this "skip" is done here, rather than above.  This is
      // because (1) the quantifier could in principle simplify to false,
      // which should be reported, and (2) checking for the quantifier
      // above, before simplification, doesn't catch buried quantifiers
      // anyway (those not at the top-level).
      Notice() << "SmtEngine::checkModel(): -- skipping rewrite-rules assertion"
               << endl;
      continue;
    }

    // As a last-ditch effort, ask model to simplify it.
    // Presently, this is only an issue for quantifiers, which can have a value
    // but don't show up in our substitution map above.
    n = m->getValue(n);
    Notice() << "SmtEngine::checkModel(): -- model-substitutes to " << n << endl;
    AlwaysAssert(!hardFailure || n.isConst() || n.getKind() == kind::LAMBDA);

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

Proof* SmtEngine::getProof() throw(ModalException) {
  Trace("smt") << "SMT getProof()" << endl;
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetProofCommand();
  }
#ifdef CVC4_PROOF
  if(!options::proof()) {
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

  return ProofManager::getProof(this);
#else /* CVC4_PROOF */
  throw ModalException("This build of CVC4 doesn't have proof support.");
#endif /* CVC4_PROOF */
}

vector<Expr> SmtEngine::getAssertions() throw(ModalException) {
  SmtScope smts(this);
  finalOptionsAreSet();
  if(Dump.isOn("benchmark")) {
    Dump("benchmark") << GetAssertionsCommand();
  }
  Trace("smt") << "SMT getAssertions()" << endl;
  if(!options::interactive()) {
    const char* msg =
      "Cannot query the current assertion list when not in interactive mode.";
    throw ModalException(msg);
  }
  Assert(d_assertionList != NULL);
  // copy the result out
  return vector<Expr>(d_assertionList->begin(), d_assertionList->end());
}

void SmtEngine::push() throw(ModalException, LogicException) {
  SmtScope smts(this);
  finalOptionsAreSet();
  doPendingPops();
  Trace("smt") << "SMT push()" << endl;
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

void SmtEngine::pop() throw(ModalException) {
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
  // Still, we want the right exit status after any final sequence
  // of pops... hm.
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

void SmtEngine::interrupt() throw(ModalException) {
  if(!d_fullyInited) {
    return;
  }
  d_propEngine->interrupt();
  d_theoryEngine->interrupt();
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

Statistics SmtEngine::getStatistics() const throw() {
  return Statistics(*d_statisticsRegistry);
}

SExpr SmtEngine::getStatistic(std::string name) const throw() {
  return d_statisticsRegistry->getStatistic(name);
}

void SmtEngine::setUserAttribute(const std::string& attr, Expr expr) {
  SmtScope smts(this);
  d_theoryEngine->setUserAttribute(attr, expr.getNode());
}

}/* CVC4 namespace */
