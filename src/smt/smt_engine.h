/*********************                                                        */
/*! \file smt_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SmtEngine: the main public entry point of libcvc4.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <string>
#include <vector>

#include "base/modal_exception.h"
#include "context/cdhashmap_forward.h"
#include "context/cdhashset_forward.h"
#include "context/cdlist_forward.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/expr_stream.h"
#include "options/options.h"
#include "proof/unsat_core.h"
#include "smt/logic_exception.h"
#include "smt_util/lemma_channels.h"
#include "theory/logic_info.h"
#include "util/hash.h"
#include "util/proof.h"
#include "util/result.h"
#include "util/sexpr.h"
#include "util/statistics.h"
#include "util/unsafe_interrupt_exception.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {

template <bool ref_count> class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
struct NodeHashFunction;

class Command;
class GetModelCommand;

class SmtEngine;
class DecisionEngine;
class TheoryEngine;

class ProofManager;

class Model;
class LogicRequest;
class StatisticsRegistry;

namespace context {
  class Context;
  class UserContext;
}/* CVC4::context namespace */

namespace prop {
  class PropEngine;
}/* CVC4::prop namespace */

namespace expr {
  namespace attr {
    class AttributeManager;
    struct SmtAttributes;
  }/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */

namespace smt {
  /**
   * Representation of a defined function.  We keep these around in
   * SmtEngine to permit expanding definitions late (and lazily), to
   * support getValue() over defined functions, to support user output
   * in terms of defined functions, etc.
   */
  class DefinedFunction;

  struct SmtEngineStatistics;
  class SmtEnginePrivate;
  class SmtScope;
  class BooleanTermConverter;

  ProofManager* currentProofManager();

  struct CommandCleanup;
  typedef context::CDList<Command*, CommandCleanup> CommandList;
}/* CVC4::smt namespace */

namespace theory {
  class TheoryModel;
}/* CVC4::theory namespace */

namespace stats {
  StatisticsRegistry* getStatisticsRegistry(SmtEngine*);
}/* CVC4::stats namespace */

// TODO: SAT layer (esp. CNF- versus non-clausal solvers under the
// hood): use a type parameter and have check() delegate, or subclass
// SmtEngine and override check()?
//
// Probably better than that is to have a configuration object that
// indicates which passes are desired.  The configuration occurs
// elsewhere (and can even occur at runtime).  A simple "pass manager"
// of sorts determines check()'s behavior.
//
// The CNF conversion can go on in PropEngine.

class CVC4_PUBLIC SmtEngine {

  /** The type of our internal map of defined functions */
  typedef context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>
    DefinedFunctionMap;
  /** The type of our internal assertion list */
  typedef context::CDList<Expr> AssertionList;
  /** The type of our internal assignment set */
  typedef context::CDHashSet<Node, NodeHashFunction> AssignmentSet;
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;

  /** Expr manager context */
  context::Context* d_context;

  /** The context levels of user pushes */
  std::vector<int> d_userLevels;
  /** User level context */
  context::UserContext* d_userContext;

  /** Our expression manager */
  ExprManager* d_exprManager;
  /** Our internal expression/node manager */
  NodeManager* d_nodeManager;
  /** The decision engine */
  DecisionEngine* d_decisionEngine;
  /** The theory engine */
  TheoryEngine* d_theoryEngine;
  /** The propositional engine */
  prop::PropEngine* d_propEngine;
  /** The proof manager */
  ProofManager* d_proofManager;
  /** An index of our defined functions */
  DefinedFunctionMap* d_definedFunctions;
  /** recursive function definition abstractions for --fmf-fun */
  std::map< Node, TypeNode > d_fmfRecFunctionsAbs;
  std::map< Node, std::vector< Node > > d_fmfRecFunctionsConcrete;
  NodeList* d_fmfRecFunctionsDefined;

  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in interactive mode.
   */
  AssertionList* d_assertionList;

  /**
   * List of items for which to retrieve values using getAssignment().
   */
  AssignmentSet* d_assignments;

  /**
   * A list of commands that should be in the Model globally (i.e.,
   * regardless of push/pop).  Only maintained if produce-models option
   * is on.
   */
  std::vector<Command*> d_modelGlobalCommands;

  /**
   * A list of commands that should be in the Model locally (i.e.,
   * it is context-dependent on push/pop).  Only maintained if
   * produce-models option is on.
   */
  smt::CommandList* d_modelCommands;

  /**
   * A vector of declaration commands waiting to be dumped out.
   * Once the SmtEngine is fully initialized, we'll dump them.
   * This ensures the declarations come after the set-logic and
   * any necessary set-option commands are dumped.
   */
  std::vector<Command*> d_dumpCommands;

  /**
   *A vector of command definitions to be imported in the new
   *SmtEngine when checking unsat-cores.
   */
  std::vector<Command*> d_defineCommands;

  /**
   * The logic we're in.
   */
  LogicInfo d_logic;

  /**
   * Keep a copy of the original option settings (for reset()).
   */
  Options d_originalOptions;

  /**
   * Number of internal pops that have been deferred.
   */
  unsigned d_pendingPops;

  /**
   * Whether or not this SmtEngine has been fully initialized (that is,
   * the ).  This post-construction initialization is automatically
   * triggered by the use of the SmtEngine; e.g. when setLogic() is
   * called, or the first assertion is made, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not we have added any assertions/declarations/definitions,
   * or done push/pop, since the last checkSat/query, and therefore we're
   * not responsible for models or proofs.
   */
  bool d_problemExtended;

  /**
   * Whether or not a query() or checkSat() has already been made through
   * this SmtEngine.  If true, and incrementalSolving is false, then
   * attempting an additional query() or checkSat() will fail with a
   * ModalException.
   */
  bool d_queryMade;

  /**
   * Internal status flag to indicate whether we've sent a theory
   * presolve() notification and need to match it with a postsolve().
   */
  bool d_needPostsolve;

  /*
   * Whether to call theory preprocessing during simplification - on
   * by default* but gets turned off if arithRewriteEq is on
   */
  bool d_earlyTheoryPP;

  /**
   * Most recent result of last checkSat/query or (set-info :status).
   */
  Result d_status;

  /**
   * The name of the input (if any).
   */
  std::string d_filename;

  /**
   * Verbosity of various commands.
   */
  std::map<std::string, Integer> d_commandVerbosity;

  /** ReplayStream for the solver. */
  ExprStream* d_replayStream;

  /**
   * A private utility class to SmtEngine.
   */
  smt::SmtEnginePrivate* d_private;

  /**
   * Check that a generated proof (via getProof()) checks.
   */
  void checkProof();

  /**
   * Check that an unsatisfiable core is indeed unsatisfiable.
   */
  void checkUnsatCore();

  /**
   * Check that a generated Model (via getModel()) actually satisfies
   * all user assertions.
   */
  void checkModel(bool hardFailure = true);

  /**
   * Postprocess a value for output to the user.  Involves doing things
   * like turning datatypes back into tuples, length-1-bitvectors back
   * into booleans, etc.
   */
  Node postprocess(TNode n, TypeNode expectedType) const;

  /**
   * This is something of an "init" procedure, but is idempotent; call
   * as often as you like.  Should be called whenever the final options
   * and logic for the problem are set (at least, those options that are
   * not permitted to change after assertions and queries are made).
   */
  void finalOptionsAreSet();

  /**
   * Apply heuristics settings and other defaults.  Done once, at
   * finishInit() time.
   */
  void setDefaults();

  /**
   * Create theory engine, prop engine, decision engine. Called by
   * finalOptionsAreSet()
   */
  void finishInit();

  /**
   * This is called by the destructor, just before destroying the
   * PropEngine, TheoryEngine, and DecisionEngine (in that order).  It
   * is important because there are destruction ordering issues
   * between PropEngine and Theory.
   */
  void shutdown();

  /**
   * Full check of consistency in current context.  Returns true iff
   * consistent.
   */
  Result check();

  /**
   * Quick check of consistency in current context: calls
   * processAssertionList() then look for inconsistency (based only on
   * that).
   */
  Result quickCheck();

  /**
   * Fully type-check the argument, and also type-check that it's
   * actually Boolean.
   */
  void ensureBoolean(const Expr& e) throw(TypeCheckingException);

  void internalPush();

  void internalPop(bool immediate = false);

  void doPendingPops();

  /**
   * Internally handle the setting of a logic.  This function should always
   * be called when d_logic is updated.
   */
  void setLogicInternal() throw();

  friend class ::CVC4::smt::SmtEnginePrivate;
  friend class ::CVC4::smt::SmtScope;
  friend class ::CVC4::smt::BooleanTermConverter;
  friend ::CVC4::StatisticsRegistry* ::CVC4::stats::getStatisticsRegistry(SmtEngine*);
  friend ProofManager* ::CVC4::smt::currentProofManager();
  friend class ::CVC4::LogicRequest;
  // to access d_modelCommands
  friend class ::CVC4::Model;
  friend class ::CVC4::theory::TheoryModel;
  // to access SmtAttributes
  friend class expr::attr::AttributeManager;
  // to access getModel(), which is private (for now)
  friend class GetModelCommand;

  /**
   * There's something of a handshake between the expr package's
   * AttributeManager and the SmtEngine because the expr package
   * doesn't have a Context on its own (that's owned by the
   * SmtEngine).  Thus all context-dependent attributes are stored
   * here.
   */
  expr::attr::SmtAttributes* d_smtAttributes;

  StatisticsRegistry* d_statisticsRegistry;

  smt::SmtEngineStatistics* d_stats;

  /** Container for the lemma input and output channels for this SmtEngine.*/
  LemmaChannels* d_channels;

  /**
   * Add to Model command.  This is used for recording a command
   * that should be reported during a get-model call.
   */
  void addToModelCommandAndDump(const Command& c, uint32_t flags = 0, bool userVisible = true, const char* dumpTag = "declarations");

  /**
   * Get the model (only if immediately preceded by a SAT
   * or INVALID query).  Only permitted if CVC4 was built with model
   * support and produce-models is on.
   */
  Model* getModel() throw(ModalException, UnsafeInterruptException);

  // disallow copy/assignment
  SmtEngine(const SmtEngine&) CVC4_UNDEFINED;
  SmtEngine& operator=(const SmtEngine&) CVC4_UNDEFINED;

  //check satisfiability (for query and check-sat)
  Result checkSatisfiability(const Expr& e, bool inUnsatCore, bool isQuery);
public:

  /**
   * Construct an SmtEngine with the given expression manager.
   */
  SmtEngine(ExprManager* em) throw();

  /**
   * Destruct the SMT engine.
   */
  ~SmtEngine() throw();

  /**
   * Set the logic of the script.
   */
  void setLogic(const std::string& logic) throw(ModalException, LogicException);

  /**
   * Set the logic of the script.
   */
  void setLogic(const char* logic) throw(ModalException, LogicException);

  /**
   * Set the logic of the script.
   */
  void setLogic(const LogicInfo& logic) throw(ModalException);

  /**
   * Get the logic information currently set
   */
  LogicInfo getLogicInfo() const;

  /**
   * Set information about the script executing.
   */
  void setInfo(const std::string& key, const CVC4::SExpr& value)
    throw(OptionException, ModalException);

  /**
   * Query information about the SMT environment.
   */
  CVC4::SExpr getInfo(const std::string& key) const
    throw(OptionException, ModalException);

  /**
   * Set an aspect of the current SMT execution environment.
   */
  void setOption(const std::string& key, const CVC4::SExpr& value)
    throw(OptionException, ModalException);

  /**
   * Get an aspect of the current SMT execution environment.
   */
  CVC4::SExpr getOption(const std::string& key) const
    throw(OptionException);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false if
   * immediately determined to be inconsistent.
   */
  void defineFunction(Expr func,
                      const std::vector<Expr>& formals,
                      Expr formula);

  /** is defined function */
  bool isDefinedFunction(Expr func);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false if
   * immediately determined to be inconsistent.  This version
   * takes a Boolean flag to determine whether to include this asserted
   * formula in an unsat core (if one is later requested).
   */
  Result assertFormula(const Expr& e, bool inUnsatCore = true) throw(TypeCheckingException, LogicException, UnsafeInterruptException);

  /**
   * Check validity of an expression with respect to the current set
   * of assertions by asserting the query expression's negation and
   * calling check().  Returns valid, invalid, or unknown result.
   */
  Result query(const Expr& e, bool inUnsatCore = true) throw(TypeCheckingException, ModalException, LogicException);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns sat, unsat, or unknown result.
   */
  Result checkSat(const Expr& e = Expr(), bool inUnsatCore = true) throw(TypeCheckingException, ModalException, LogicException);

  /**
   * Assert a synthesis conjecture to the current context and call
   * check().  Returns sat, unsat, or unknown result.
   */
  Result checkSynth(const Expr& e) throw(TypeCheckingException, ModalException, LogicException);

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   *
   * @todo (design) is this meant to give an equivalent or an
   * equisatisfiable formula?
   */
  Expr simplify(const Expr& e) throw(TypeCheckingException, LogicException, UnsafeInterruptException);

  /**
   * Expand the definitions in a term or formula.  No other
   * simplification or normalization is done.
   */
  Expr expandDefinitions(const Expr& e) throw(TypeCheckingException, LogicException, UnsafeInterruptException);

  /**
   * Get the assigned value of an expr (only if immediately preceded
   * by a SAT or INVALID query).  Only permitted if the SmtEngine is
   * set to operate interactively and produce-models is on.
   */
  Expr getValue(const Expr& e) const throw(ModalException, TypeCheckingException, LogicException, UnsafeInterruptException);

  /**
   * Add a function to the set of expressions whose value is to be
   * later returned by a call to getAssignment().  The expression
   * should be a Boolean zero-ary defined function or a Boolean
   * variable.  Rather than throwing a ModalException on modal
   * failures (not in interactive mode or not producing assignments),
   * this function returns true if the expression was added and false
   * if this request was ignored.
   */
  bool addToAssignment(const Expr& e) throw();

  /**
   * Get the assignment (only if immediately preceded by a SAT or
   * INVALID query).  Only permitted if the SmtEngine is set to
   * operate interactively and produce-assignments is on.
   */
  CVC4::SExpr getAssignment() throw(ModalException, UnsafeInterruptException);

  /**
   * Get the last proof (only if immediately preceded by an UNSAT
   * or VALID query).  Only permitted if CVC4 was built with proof
   * support and produce-proofs is on.
   */
  Proof* getProof() throw(ModalException, UnsafeInterruptException);

  /**
   * Print all instantiations made by the quantifiers module.
   */
  void printInstantiations( std::ostream& out );

  /**
   * Print solution for synthesis conjectures found by ce_guided_instantiation module
   */
  void printSynthSolution( std::ostream& out );

  /**
   * Do quantifier elimination, doFull false means just output one disjunct, strict is whether to output warnings.
   */
  Expr doQuantifierElimination(const Expr& e, bool doFull, bool strict=true) throw(TypeCheckingException, ModalException, LogicException);

  /**
   * Get list of quantified formulas that were instantiated
   */
  void getInstantiatedQuantifiedFormulas( std::vector< Expr >& qs );
   
  /**
   * Get instantiations
   */
  void getInstantiations( Expr q, std::vector< Expr >& insts );
  void getInstantiationTermVectors( Expr q, std::vector< std::vector< Expr > >& tvecs );

  /**
   * Get an unsatisfiable core (only if immediately preceded by an
   * UNSAT or VALID query).  Only permitted if CVC4 was built with
   * unsat-core support and produce-unsat-cores is on.
   */
  UnsatCore getUnsatCore() throw(ModalException, UnsafeInterruptException);

  /**
   * Get the current set of assertions.  Only permitted if the
   * SmtEngine is set to operate interactively.
   */
  std::vector<Expr> getAssertions() throw(ModalException);

  /**
   * Push a user-level context.
   */
  void push() throw(ModalException, LogicException, UnsafeInterruptException);

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop() throw(ModalException, UnsafeInterruptException);

  /**
   * Completely reset the state of the solver, as though destroyed and
   * recreated.  The result is as if newly constructed (so it still
   * retains the same options structure and ExprManager).
   */
  void reset() throw();

  /**
   * Reset all assertions, global declarations, etc.
   */
  void resetAssertions() throw();

  /**
   * Interrupt a running query.  This can be called from another thread
   * or from a signal handler.  Throws a ModalException if the SmtEngine
   * isn't currently in a query.
   */
  void interrupt() throw(ModalException);

  /**
   * Set a resource limit for SmtEngine operations.  This is like a time
   * limit, but it's deterministic so that reproducible results can be
   * obtained.  Currently, it's based on the number of conflicts.
   * However, please note that the definition may change between different
   * versions of CVC4 (as may the number of conflicts required, anyway),
   * and it might even be different between instances of the same version
   * of CVC4 on different platforms.
   *
   * A cumulative and non-cumulative (per-call) resource limit can be
   * set at the same time.  A call to setResourceLimit() with
   * cumulative==true replaces any cumulative resource limit currently
   * in effect; a call with cumulative==false replaces any per-call
   * resource limit currently in effect.  Time limits can be set in
   * addition to resource limits; the SmtEngine obeys both.  That means
   * that up to four independent limits can control the SmtEngine
   * at the same time.
   *
   * When an SmtEngine is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the SmtEngine to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param units the resource limit, or 0 for no limit
   * @param cumulative whether this resource limit is to be a cumulative
   * resource limit for all remaining calls into the SmtEngine (true), or
   * whether it's a per-call resource limit (false); the default is false
   */
  void setResourceLimit(unsigned long units, bool cumulative = false);

  /**
   * Set a time limit for SmtEngine operations.
   *
   * A cumulative and non-cumulative (per-call) time limit can be
   * set at the same time.  A call to setTimeLimit() with
   * cumulative==true replaces any cumulative time limit currently
   * in effect; a call with cumulative==false replaces any per-call
   * time limit currently in effect.  Resource limits can be set in
   * addition to time limits; the SmtEngine obeys both.  That means
   * that up to four independent limits can control the SmtEngine
   * at the same time.
   *
   * Note that the cumulative timer only ticks away when one of the
   * SmtEngine's workhorse functions (things like assertFormula(),
   * query(), checkSat(), and simplify()) are running.  Between calls,
   * the timer is still.
   *
   * When an SmtEngine is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the SmtEngine to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param millis the time limit in milliseconds, or 0 for no limit
   * @param cumulative whether this time limit is to be a cumulative
   * time limit for all remaining calls into the SmtEngine (true), or
   * whether it's a per-call time limit (false); the default is false
   */
  void setTimeLimit(unsigned long millis, bool cumulative = false);

  /**
   * Get the current resource usage count for this SmtEngine.  This
   * function can be used to ascertain reasonable values to pass as
   * resource limits to setResourceLimit().
   */
  unsigned long getResourceUsage() const;

  /**
   * Get the current millisecond count for this SmtEngine.
   */
  unsigned long getTimeUsage() const;

  /**
   * Get the remaining resources that can be consumed by this SmtEngine
   * according to the currently-set cumulative resource limit.  If there
   * is not a cumulative resource limit set, this function throws a
   * ModalException.
   */
  unsigned long getResourceRemaining() const throw(ModalException);

  /**
   * Get the remaining number of milliseconds that can be consumed by
   * this SmtEngine according to the currently-set cumulative time limit.
   * If there is not a cumulative resource limit set, this function
   * throws a ModalException.
   */
  unsigned long getTimeRemaining() const throw(ModalException);

  /**
   * Permit access to the underlying ExprManager.
   */
  ExprManager* getExprManager() const {
    return d_exprManager;
  }

  /**
   * Export statistics from this SmtEngine.
   */
  Statistics getStatistics() const throw();

  /**
   * Get the value of one named statistic from this SmtEngine.
   */
  SExpr getStatistic(std::string name) const throw();

  /**
   * Returns the most recent result of checkSat/query or (set-info :status).
   */
  Result getStatusOfLastCommand() const throw() {
    return d_status;
  }

  /**
   * Set user attribute.
   * This function is called when an attribute is set by a user.
   * In SMT-LIBv2 this is done via the syntax (! expr :attr)
   */
  void setUserAttribute(const std::string& attr, Expr expr, std::vector<Expr> expr_values, std::string str_value);

  /**
   * Set print function in model
   */
  void setPrintFuncInModel(Expr f, bool p);


  /** Throws a ModalException if the SmtEngine has been fully initialized. */
  void beforeSearch() throw(ModalException);

  LemmaChannels* channels() { return d_channels; }


  /**
   * Expermintal feature: Sets the sequence of decisions.
   * This currently requires very fine grained knowledge about literal
   * translation.
   */
  void setReplayStream(ExprStream* exprStream);

};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */
