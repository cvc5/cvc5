/*********************                                                        */
/*! \file smt_engine.h
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
 ** \brief SmtEngine: the main public entry point of libcvc4.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SMT_ENGINE_H
#define __CVC4__SMT_ENGINE_H

#include <vector>

#include "context/cdlist_forward.h"
#include "context/cdhashmap_forward.h"
#include "context/cdhashset_forward.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "util/proof.h"
#include "smt/bad_option_exception.h"
#include "smt/modal_exception.h"
#include "smt/no_such_function_exception.h"
#include "util/hash.h"
#include "util/options.h"
#include "util/result.h"
#include "util/sexpr.h"
#include "util/stats.h"
#include "theory/logic_info.h"

// In terms of abstraction, this is below (and provides services to)
// ValidityChecker and above (and requires the services of)
// PropEngine.

namespace CVC4 {


template <bool ref_count> class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
class NodeHashFunction;

class DecisionEngine;
class TheoryEngine;

class StatisticsRegistry;

namespace context {
  class Context;
  class UserContext;
}/* CVC4::context namespace */

namespace prop {
  class PropEngine;
}/* CVC4::prop namespace */

namespace smt {
  /**
   * Representation of a defined function.  We keep these around in
   * SmtEngine to permit expanding definitions late (and lazily), to
   * support getValue() over defined functions, to support user output
   * in terms of defined functions, etc.
   */
  class DefinedFunction;

  class SmtEnginePrivate;
}/* CVC4::smt namespace */

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
  /** An index of our defined functions */
  DefinedFunctionMap* d_definedFunctions;
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
   * The logic we're in.
   */
  LogicInfo d_logic;

  /**
   * Whether or not this SmtEngine has been fully initialized (that is,
   * the ).  This post-construction initialization is automatically
   * triggered by the use of the SmtEngine; e.g. when setLogic() is
   * called, or the first assertion is made, etc.
   */
  bool d_fullyInited;

  /**
   * Whether or not we have added any assertions/declarations/definitions
   * since the last checkSat/query (and therefore we're not responsible
   * for an assignment).
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

  /** A user-imposed cumulative time budget, in milliseconds.  0 = no limit. */
  unsigned long d_timeBudgetCumulative;
  /** A user-imposed per-call time budget, in milliseconds.  0 = no limit. */
  unsigned long d_timeBudgetPerCall;
  /** A user-imposed cumulative resource budget.  0 = no limit. */
  unsigned long d_resourceBudgetCumulative;
  /** A user-imposed per-call resource budget.  0 = no limit. */
  unsigned long d_resourceBudgetPerCall;

  /** The number of milliseconds used by this SmtEngine since its inception. */
  unsigned long d_cumulativeTimeUsed;
  /** The amount of resource used by this SmtEngine since its inception. */
  unsigned long d_cumulativeResourceUsed;

  /**
   * Most recent result of last checkSat/query or (set-info :status).
   */
  Result d_status;

  /**
   * A private utility class to SmtEngine.
   */
  smt::SmtEnginePrivate* d_private;

  /**
   * This is something of an "init" procedure, but is idempotent; call
   * as often as you like.  Should be called whenever the final options
   * and logic for the problem are set (at least, those options that are
   * not permitted to change after assertions and queries are made).
   */
  void finalOptionsAreSet();

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
  void ensureBoolean(const BoolExpr& e);

  void internalPush();

  void internalPop();

  /**
   * Internally handle the setting of a logic.  This function should always
   * be called when d_logic is updated.
   */
  void setLogicInternal() throw(AssertionException);

  friend class ::CVC4::smt::SmtEnginePrivate;

  // === STATISTICS ===
  /** time spent in definition-expansion */
  TimerStat d_definitionExpansionTime;
  /** time spent in non-clausal simplification */
  TimerStat d_nonclausalSimplificationTime;
  /** Num of constant propagations found during nonclausal simp */
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

  /** how the SMT engine got the answer -- SAT solver or DE */
  BackedStat<std::string> d_statResultSource;

public:

  /**
   * Construct an SmtEngine with the given expression manager.
   */
  SmtEngine(ExprManager* em) throw(AssertionException);

  /**
   * Destruct the SMT engine.
   */
  ~SmtEngine() throw();

  /**
   * Set the logic of the script.
   */
  void setLogic(const std::string& logic) throw(ModalException);

  /**
   * Set the logic of the script.
   */
  void setLogic(const LogicInfo& logic) throw(ModalException);

  /**
   * Set information about the script executing.
   */
  void setInfo(const std::string& key, const SExpr& value)
    throw(BadOptionException, ModalException);

  /**
   * Query information about the SMT environment.
   */
  SExpr getInfo(const std::string& key) const
    throw(BadOptionException);

  /**
   * Set an aspect of the current SMT execution environment.
   */
  void setOption(const std::string& key, const SExpr& value)
    throw(BadOptionException, ModalException);

  /**
   * Get an aspect of the current SMT execution environment.
   */
  SExpr getOption(const std::string& key) const
    throw(BadOptionException);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  void defineFunction(Expr func,
                      const std::vector<Expr>& formals,
                      Expr formula);

  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false iff
   * inconsistent.
   */
  Result assertFormula(const BoolExpr& e);

  /**
   * Check validity of an expression with respect to the current set
   * of assertions by asserting the query expression's negation and
   * calling check().  Returns valid, invalid, or unknown result.
   */
  Result query(const BoolExpr& e);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns sat, unsat, or unknown result.
   */
  Result checkSat(const BoolExpr& e = BoolExpr());

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * assertions and the current partial model, if one has been
   * constructed.
   *
   * @todo (design) is this meant to give an equivalent or an
   * equisatisfiable formula?
   */
  Expr simplify(const Expr& e);

  /**
   * Get the assigned value of an expr (only if immediately preceded
   * by a SAT or INVALID query).  Only permitted if the SmtEngine is
   * set to operate interactively and produce-models is on.
   */
  Expr getValue(const Expr& e) throw(ModalException, AssertionException);

  /**
   * Add a function to the set of expressions whose value is to be
   * later returned by a call to getAssignment().  The expression
   * should be a Boolean zero-ary defined function or a Boolean
   * variable.  Rather than throwing a ModalException on modal
   * failures (not in interactive mode or not producing assignments),
   * this function returns true if the expression was added and false
   * if this request was ignored.
   */
  bool addToAssignment(const Expr& e) throw(AssertionException);

  /**
   * Get the assignment (only if immediately preceded by a SAT or
   * INVALID query).  Only permitted if the SmtEngine is set to
   * operate interactively and produce-assignments is on.
   */
  SExpr getAssignment() throw(ModalException, AssertionException);

  /**
   * Get the last proof (only if immediately preceded by an UNSAT
   * or VALID query).  Only permitted if CVC4 was built with proof
   * support and produce-proofs is on.
   */
  Proof* getProof() throw(ModalException, AssertionException);

  /**
   * Get the current set of assertions.  Only permitted if the
   * SmtEngine is set to operate interactively.
   */
  std::vector<Expr> getAssertions() throw(ModalException, AssertionException);

  /**
   * Get the current context level.
   */
  size_t getStackLevel() const;

  /**
   * Push a user-level context.
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   */
  void pop();

  /**
   * Interrupt a running query.  This can be called from another thread
   * or from a signal handler.  Throws a ModalException if the SmtEngine
   * isn't currently in a query.
   */
  void interrupt() throw(ModalException);

  /**
   * Set a resource limit for SmtEngine operations.  This is like a time
   * limit, but it's deterministic so that reproducible results can be
   * obtained.  However, please note that it may not be deterministic
   * between different versions of CVC4, or even the same version on
   * different platforms.
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
   * Permit access to the underlying StatisticsRegistry.
   */
  StatisticsRegistry* getStatisticsRegistry() const;

  Result getStatusOfLastCommand() const {
    return d_status;
  }

};/* class SmtEngine */

}/* CVC4 namespace */

#endif /* __CVC4__SMT_ENGINE_H */
