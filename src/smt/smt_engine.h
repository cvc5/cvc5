/*********************                                                        */
/*! \file smt_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief SmtEngine: the main public entry point of libcvc4.
 **
 ** SmtEngine: the main public entry point of libcvc4.
 **/

#include "cvc4_public.h"

#ifndef CVC4__SMT_ENGINE_H
#define CVC4__SMT_ENGINE_H

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

/* -------------------------------------------------------------------------- */

namespace context {
  class Context;
  class UserContext;
}/* CVC4::context namespace */

/* -------------------------------------------------------------------------- */

namespace preprocessing {
class PreprocessingPassContext;
}

/* -------------------------------------------------------------------------- */

namespace prop {
  class PropEngine;
}/* CVC4::prop namespace */

/* -------------------------------------------------------------------------- */

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

/* -------------------------------------------------------------------------- */

namespace theory {
  class TheoryModel;
}/* CVC4::theory namespace */

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

/* -------------------------------------------------------------------------- */

class CVC4_PUBLIC SmtEngine
{
  // TODO (Issue #1096): Remove this friend relationship.
  friend class ::CVC4::preprocessing::PreprocessingPassContext;
  friend class ::CVC4::smt::SmtEnginePrivate;
  friend class ::CVC4::smt::SmtScope;
  friend class ::CVC4::smt::BooleanTermConverter;
  friend ProofManager* ::CVC4::smt::currentProofManager();
  friend class ::CVC4::LogicRequest;
  friend class ::CVC4::Model;  // to access d_modelCommands
  friend class ::CVC4::theory::TheoryModel;

  /* .......................................................................  */
 public:
  /* .......................................................................  */

  /** Construct an SmtEngine with the given expression manager.  */
  SmtEngine(ExprManager* em);
  /** Destruct the SMT engine.  */
  ~SmtEngine();

  /**
   * Return true if this SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool isFullyInited() { return d_fullyInited; }

  /** Return true if a query() or checkSat() has already been made.  */
  bool isQueryMade() { return d_queryMade; }

  /** Return the user context level.  */
  size_t getNumUserLevels() { return d_userLevels.size(); }

  /**
   * Set the logic of the script.
   * @throw ModalException, LogicException
   */
  void setLogic(const std::string& logic);

  /**
   * Set the logic of the script.
   * @throw ModalException, LogicException
   */
  void setLogic(const char* logic);

  /**
   * Set the logic of the script.
   * @throw ModalException
   */
  void setLogic(const LogicInfo& logic);

  /** Get the logic information currently set. */
  LogicInfo getLogicInfo() const;

  /**
   * Set information about the script executing.
   * @throw OptionException, ModalException
   */
  void setInfo(const std::string& key, const CVC4::SExpr& value);

  /** Query information about the SMT environment.  */
  CVC4::SExpr getInfo(const std::string& key) const;

  /**
   * Set an aspect of the current SMT execution environment.
   * @throw OptionException, ModalException
   */
  void setOption(const std::string& key, const CVC4::SExpr& value);

  /** Set is internal subsolver.
   *
   * This function is called on SmtEngine objects that are created internally.
   * It is used to mark that this SmtEngine should not perform preprocessing
   * passes that rephrase the input, such as --sygus-rr-synth-input or
   * --sygus-abduct.
   */
  void setIsInternalSubsolver();

  /** set the input name */
  void setFilename(std::string filename);
  /** return the input name (if any) */
  std::string getFilename() const;

  /**
   * Get the model (only if immediately preceded by a SAT
   * or INVALID query).  Only permitted if produce-models is on.
   */
  Model* getModel();

  /**
   * Block the current model. Can be called only if immediately preceded by
   * a SAT or INVALID query. Only permitted if produce-models is on, and the
   * block-models option is set to a mode other than "none".
   *
   * This adds an assertion to the assertion stack that blocks the current
   * model based on the current options configured by CVC4.
   *
   * The return value has the same meaning as that of assertFormula.
   */
  Result blockModel();

  /**
   * Block the current model values of (at least) the values in exprs.
   * Can be called only if immediately preceded by a SAT or INVALID query. Only
   * permitted if produce-models is on, and the block-models option is set to a
   * mode other than "none".
   *
   * This adds an assertion to the assertion stack of the form:
   *  (or (not (= exprs[0] M0)) ... (not (= exprs[n] Mn)))
   * where M0 ... Mn are the current model values of exprs[0] ... exprs[n].
   *
   * The return value has the same meaning as that of assertFormula.
   */
  Result blockModelValues(const std::vector<Expr>& exprs);

  /** When using separation logic, obtain the expression for the heap.  */
  Expr getSepHeapExpr();

  /** When using separation logic, obtain the expression for nil.  */
  Expr getSepNilExpr();

  /**
   * Get an aspect of the current SMT execution environment.
   * @throw OptionException
   */
  CVC4::SExpr getOption(const std::string& key) const;

  /**
   * Define function func in the current context to be:
   *   (lambda (formals) formula)
   * This adds func to the list of defined functions, which indicates that
   * all occurrences of func should be expanded during expandDefinitions.
   * This method expects input such that:
   * - func : a variable of function type that expects the arguments in
   *          formals,
   * - formals : a list of BOUND_VARIABLE expressions,
   * - formula does not contain func.
   */
  void defineFunction(Expr func,
                      const std::vector<Expr>& formals,
                      Expr formula);

  /** Return true if given expression is a defined function. */
  bool isDefinedFunction(Expr func);

  /**
   * Define functions recursive
   *
   * For each i, this constrains funcs[i] in the current context to be:
   *   (lambda (formals[i]) formulas[i])
   * where formulas[i] may contain variables from funcs. Unlike defineFunction
   * above, we do not add funcs[i] to the set of defined functions. Instead,
   * we consider funcs[i] to be a free uninterpreted function, and add:
   *   forall formals[i]. f(formals[i]) = formulas[i]
   * to the set of assertions in the current context.
   * This method expects input such that for each i:
   * - func[i] : a variable of function type that expects the arguments in
   *             formals[i], and
   * - formals[i] : a list of BOUND_VARIABLE expressions.
   */
  void defineFunctionsRec(const std::vector<Expr>& funcs,
                          const std::vector<std::vector<Expr> >& formals,
                          const std::vector<Expr>& formulas);
  /**
   * Define function recursive
   * Same as above, but for a single function.
   */
  void defineFunctionRec(Expr func,
                         const std::vector<Expr>& formals,
                         Expr formula);
  /**
   * Add a formula to the current context: preprocess, do per-theory
   * setup, use processAssertionList(), asserting to T-solver for
   * literals and conjunction of literals.  Returns false if
   * immediately determined to be inconsistent.  This version
   * takes a Boolean flag to determine whether to include this asserted
   * formula in an unsat core (if one is later requested).
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  Result assertFormula(const Expr& e, bool inUnsatCore = true);

  /**
   * Check validity of an expression with respect to the current set
   * of assertions by asserting the query expression's negation and
   * calling check().  Returns valid, invalid, or unknown result.
   *
   * @throw Exception
   */
  Result query(const Expr& assumption = Expr(), bool inUnsatCore = true);
  Result query(const std::vector<Expr>& assumptions, bool inUnsatCore = true);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns sat, unsat, or unknown result.
   *
   * @throw Exception
   */
  Result checkSat(const Expr& assumption = Expr(), bool inUnsatCore = true);
  Result checkSat(const std::vector<Expr>& assumptions,
                  bool inUnsatCore = true);

  /**
   * Returns a set of so-called "failed" assumptions.
   *
   * The returned set is a subset of the set of assumptions of a previous
   * (unsatisfiable) call to checkSatisfiability. Calling checkSatisfiability
   * with this set of failed assumptions still produces an unsat answer.
   *
   * Note that the returned set of failed assumptions is not necessarily
   * minimal.
   */
  std::vector<Expr> getUnsatAssumptions(void);

  /*---------------------------- sygus commands  ---------------------------*/

  /**
   * Add variable declaration.
   *
   * Declared SyGuS variables may be used in SyGuS constraints, in which they
   * are assumed to be universally quantified.
   */
  void declareSygusVar(const std::string& id, Expr var, Type type);

  /**
   * Store information for debugging sygus invariants setup.
   *
   * Since in SyGuS the commands "declare-primed-var" are not necessary for
   * building invariant constraints, we only use them to check that the number
   * of variables declared corresponds to the number of arguments of the
   * invariant-to-synthesize.
   */
  void declareSygusPrimedVar(const std::string& id, Type type);

  /**
   * Add a function variable declaration.
   *
   * Is SyGuS semantics declared functions are treated in the same manner as
   * declared variables, i.e. as universally quantified (function) variables
   * which can occur in the SyGuS constraints that compose the conjecture to
   * which a function is being synthesized.
   */
  void declareSygusFunctionVar(const std::string& id, Expr var, Type type);

  /**
   * Add a function-to-synthesize declaration.
   *
   * The given type may not correspond to the actual function type but to a
   * datatype encoding the syntax restrictions for the
   * function-to-synthesize. In this case this information is stored to be used
   * during solving.
   *
   * vars contains the arguments of the function-to-synthesize. These variables
   * are also stored to be used during solving.
   *
   * isInv determines whether the function-to-synthesize is actually an
   * invariant. This information is necessary if we are dumping a command
   * corresponding to this declaration, so that it can be properly printed.
   */
  void declareSynthFun(const std::string& id,
                       Expr func,
                       Type type,
                       bool isInv,
                       const std::vector<Expr>& vars);

  /** Add a regular sygus constraint.*/
  void assertSygusConstraint(Expr constraint);

  /**
   * Add an invariant constraint.
   *
   * Invariant constraints are not explicitly declared: they are given in terms
   * of the invariant-to-synthesize, the pre condition, transition relation and
   * post condition. The actual constraint is built based on the inputs of these
   * place holder predicates :
   *
   * PRE(x) -> INV(x)
   * INV() ^ TRANS(x, x') -> INV(x')
   * INV(x) -> POST(x)
   *
   * The regular and primed variables are retrieved from the declaration of the
   * invariant-to-synthesize.
   */
  void assertSygusInvConstraint(const Expr& inv,
                                const Expr& pre,
                                const Expr& trans,
                                const Expr& post);
  /**
   * Assert a synthesis conjecture to the current context and call
   * check().  Returns sat, unsat, or unknown result.
   *
   * The actual synthesis conjecture is built based on the previously
   * communicated information to this module (universal variables, defined
   * functions, functions-to-synthesize, and which constraints compose it). The
   * built conjecture is a higher-order formula of the form
   *
   * exists f1...fn . forall v1...vm . F
   *
   * in which f1...fn are the functions-to-synthesize, v1...vm are the declared
   * universal variables and F is the set of declared constraints.
   *
   * @throw Exception
   */
  Result checkSynth();

  /*------------------------- end of sygus commands ------------------------*/

  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   *
   * @todo (design) is this meant to give an equivalent or an
   * equisatisfiable formula?
   */
  Expr simplify(const Expr& e);

  /**
   * Expand the definitions in a term or formula.  No other
   * simplification or normalization is done.
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  Expr expandDefinitions(const Expr& e);

  /**
   * Get the assigned value of an expr (only if immediately preceded
   * by a SAT or INVALID query).  Only permitted if the SmtEngine is
   * set to operate interactively and produce-models is on.
   *
   * @throw ModalException, TypeCheckingException, LogicException,
   *        UnsafeInterruptException
   */
  Expr getValue(const Expr& e) const;

  /**
   * Same as getValue but for a vector of expressions
   */
  std::vector<Expr> getValues(const std::vector<Expr>& exprs);

  /**
   * Add a function to the set of expressions whose value is to be
   * later returned by a call to getAssignment().  The expression
   * should be a Boolean zero-ary defined function or a Boolean
   * variable.  Rather than throwing a ModalException on modal
   * failures (not in interactive mode or not producing assignments),
   * this function returns true if the expression was added and false
   * if this request was ignored.
   */
  bool addToAssignment(const Expr& e);

  /**
   * Get the assignment (only if immediately preceded by a SAT or
   * INVALID query).  Only permitted if the SmtEngine is set to
   * operate interactively and produce-assignments is on.
   */
  std::vector<std::pair<Expr, Expr> > getAssignment();

  /**
   * Get the last proof (only if immediately preceded by an UNSAT
   * or VALID query).  Only permitted if CVC4 was built with proof
   * support and produce-proofs is on.
   *
   * The Proof object is owned by this SmtEngine until the SmtEngine is
   * destroyed.
   */
  const Proof& getProof();

  /** Print all instantiations made by the quantifiers module.  */
  void printInstantiations(std::ostream& out);

  /**
   * Print solution for synthesis conjectures found by counter-example guided
   * instantiation module.
   */
  void printSynthSolution(std::ostream& out);

  /**
   * Get synth solution.
   *
   * This function adds entries to sol_map that map functions-to-synthesize with
   * their solutions, for all active conjectures. This should be called
   * immediately after the solver answers unsat for sygus input.
   *
   * Specifically, given a sygus conjecture of the form
   *   exists x1...xn. forall y1...yn. P( x1...xn, y1...yn )
   * where x1...xn are second order bound variables, we map each xi to
   * lambda term in sol_map such that
   *    forall y1...yn. P( sol_map[x1]...sol_map[xn], y1...yn )
   * is a valid formula.
   */
  void getSynthSolutions(std::map<Expr, Expr>& sol_map);

  /**
   * Do quantifier elimination.
   *
   * This function takes as input a quantified formula e
   * of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free
   * formula in a logic that supports quantifier elimination.
   * Currently, the only logics supported by quantifier
   * elimination is LRA and LIA.
   *
   * This function returns a formula ret such that, given
   * the current set of formulas A asserted to this SmtEngine :
   *
   * If doFull = true, then
   *   - ( A ^ e ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn.
   *
   * If doFull = false, then
   *   - (A ^ e) => (A ^ ret) if Q is forall or
   *     (A ^ ret) => (A ^ e) if Q is exists,
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n
   *     where for each i=1,...n, formula ret^Q_i
   *     is the result of calling doQuantifierElimination
   *     for e with the set of assertions A^Q_{i-1}.
   *     Similarly, if Q is forall, then let A^Q_n be
   *       A ^ ret^Q_1 ^ ... ^ ret^Q_n
   *     where ret^Q_i is the same as above.
   *     In either case, we have that ret^Q_j will
   *     eventually be true or false, for some finite j.
   *
   * The former feature is quantifier elimination, and
   * is run on invocations of the smt2 extended command get-qe.
   * The latter feature is referred to as partial quantifier
   * elimination, and is run on invocations of the smt2
   * extended command get-qe-disjunct, which can be used
   * for incrementally computing the result of a
   * quantifier elimination.
   *
   * The argument strict is whether to output
   * warnings, such as when an unexpected logic is used.
   *
   * throw@ Exception
   */
  Expr doQuantifierElimination(const Expr& e, bool doFull, bool strict = true);

  /**
   * This method asks this SMT engine to find an abduct with respect to the
   * current assertion stack (call it A) and the conjecture (call it B).
   * If this method returns true, then abd is set to a formula C such that
   * A ^ C is satisfiable, and A ^ ~B ^ C is unsatisfiable.
   *
   * The argument grammarType is a sygus datatype type that encodes the syntax
   * restrictions on the shape of possible solutions.
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getAbduct(const Expr& conj, const Type& grammarType, Expr& abd);

  /** Same as above, but without user-provided grammar restrictions */
  bool getAbduct(const Expr& conj, Expr& abd);

  /**
   * Get list of quantified formulas that were instantiated on the last call
   * to check-sat.
   */
  void getInstantiatedQuantifiedFormulas(std::vector<Expr>& qs);

  /**
   * Get instantiations for quantified formula q.
   *
   * If q was a quantified formula that was instantiated on the last call to
   * check-sat (i.e. q is returned as part of the vector in the method
   * getInstantiatedQuantifiedFormulas above), then the list of instantiations
   * of that formula that were generated are added to insts.
   *
   * In particular, if q is of the form forall x. P(x), then insts is a list
   * of formulas of the form P(t1), ..., P(tn).
   */
  void getInstantiations(Expr q, std::vector<Expr>& insts);
  /**
   * Get instantiation term vectors for quantified formula q.
   *
   * This method is similar to above, but in the example above, we return the
   * (vectors of) terms t1, ..., tn instead.
   *
   * Notice that these are not guaranteed to come in the same order as the
   * instantiation lemmas above.
   */
  void getInstantiationTermVectors(Expr q,
                                   std::vector<std::vector<Expr> >& tvecs);

  /**
   * Get an unsatisfiable core (only if immediately preceded by an
   * UNSAT or VALID query).  Only permitted if CVC4 was built with
   * unsat-core support and produce-unsat-cores is on.
   */
  UnsatCore getUnsatCore();

  /**
   * Get the current set of assertions.  Only permitted if the
   * SmtEngine is set to operate interactively.
   */
  std::vector<Expr> getAssertions();

  /**
   * Push a user-level context.
   * throw@ ModalException, LogicException, UnsafeInterruptException
   */
  void push();

  /**
   * Pop a user-level context.  Throws an exception if nothing to pop.
   * @throw ModalException
   */
  void pop();

  /**
   * Completely reset the state of the solver, as though destroyed and
   * recreated.  The result is as if newly constructed (so it still
   * retains the same options structure and ExprManager).
   */
  void reset();

  /** Reset all assertions, global declarations, etc.  */
  void resetAssertions();

  /**
   * Interrupt a running query.  This can be called from another thread
   * or from a signal handler.  Throws a ModalException if the SmtEngine
   * isn't currently in a query.
   *
   * @throw ModalException
   */
  void interrupt();

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

  /** Get the current millisecond count for this SmtEngine.  */
  unsigned long getTimeUsage() const;

  /**
   * Get the remaining resources that can be consumed by this SmtEngine
   * according to the currently-set cumulative resource limit.  If there
   * is not a cumulative resource limit set, this function throws a
   * ModalException.
   *
   * @throw ModalException
   */
  unsigned long getResourceRemaining() const;

  /**
   * Get the remaining number of milliseconds that can be consumed by
   * this SmtEngine according to the currently-set cumulative time limit.
   * If there is not a cumulative resource limit set, this function
   * throws a ModalException.
   *
   * @throw ModalException
   */
  unsigned long getTimeRemaining() const;

  /** Permit access to the underlying ExprManager. */
  ExprManager* getExprManager() const { return d_exprManager; }

  /** Export statistics from this SmtEngine. */
  Statistics getStatistics() const;

  /** Get the value of one named statistic from this SmtEngine. */
  SExpr getStatistic(std::string name) const;

  /** Flush statistic from this SmtEngine. Safe to use in a signal handler. */
  void safeFlushStatistics(int fd) const;

  /** Returns the most recent result of checkSat/query or (set-info :status). */
  Result getStatusOfLastCommand() const { return d_status; }

  /**
   * Set user attribute.
   * This function is called when an attribute is set by a user.
   * In SMT-LIBv2 this is done via the syntax (! expr :attr)
   */
  void setUserAttribute(const std::string& attr,
                        Expr expr,
                        const std::vector<Expr>& expr_values,
                        const std::string& str_value);

  /** Set print function in model. */
  void setPrintFuncInModel(Expr f, bool p);

  /**
   * Check and throw a ModalException if the SmtEngine has been fully
   * initialized.
   *
   * throw@ ModalException
   */
  void beforeSearch();

  LemmaChannels* channels() { return d_channels; }

  /**
   * Expermintal feature: Sets the sequence of decisions.
   * This currently requires very fine grained knowledge about literal
   * translation.
   */
  void setReplayStream(ExprStream* exprStream);

  /**
   * Get expression name.
   *
   * Return true if given expressoion has a name in the current context.
   * If it returns true, the name of expression 'e' is stored in 'name'.
   */
  bool getExpressionName(Expr e, std::string& name) const;

  /**
   * Set name of given expression 'e' to 'name'.
   *
   * This information is user-context-dependent.
   * If 'e' already has a name, it is overwritten.
   */
  void setExpressionName(Expr e, const std::string& name);

  /* .......................................................................  */
 private:
  /* .......................................................................  */

  /** The type of our internal map of defined functions */
  typedef context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>
      DefinedFunctionMap;
  /** The type of our internal assertion list */
  typedef context::CDList<Expr> AssertionList;
  /** The type of our internal assignment set */
  typedef context::CDHashSet<Node, NodeHashFunction> AssignmentSet;
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;

  /**
   * The current mode of the solver, see Figure 4.1 on page 52 of the
   * SMT-LIB version 2.6 standard
   * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
   */
  enum SmtMode
  {
    // the initial state of the solver
    SMT_MODE_START,
    // normal state of the solver, after assert/push/pop/declare/define
    SMT_MODE_ASSERT,
    // immediately after a check-sat returning "sat" or "unknown"
    SMT_MODE_SAT,
    // immediately after a check-sat returning "unsat"
    SMT_MODE_UNSAT,
    // immediately after a successful call to get-abduct
    SMT_MODE_ABDUCT
  };

  // disallow copy/assignment
  SmtEngine(const SmtEngine&) = delete;
  SmtEngine& operator=(const SmtEngine&) = delete;

  /**
   * Check that a generated proof (via getProof()) checks.
   */
  void checkProof();

  /**
   * Internal method to get an unsatisfiable core (only if immediately preceded
   * by an UNSAT or VALID query). Only permitted if CVC4 was built with
   * unsat-core support and produce-unsat-cores is on. Does not dump the
   * command.
   */
  UnsatCore getUnsatCoreInternal();

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
   * Check that a solution to a synthesis conjecture is indeed a solution.
   *
   * The check is made by determining if the negation of the synthesis
   * conjecture in which the functions-to-synthesize have been replaced by the
   * synthesized solutions, which is a quantifier-free formula, is
   * unsatisfiable. If not, then the found solutions are wrong.
   */
  void checkSynthSolution();
  /**
   * Check that a solution to an abduction conjecture is indeed a solution.
   *
   * The check is made by determining that the assertions conjoined with the
   * solution to the abduction problem (a) is SAT, and the assertions conjoined
   * with the abduct and the goal is UNSAT. If these criteria are not met, an
   * internal error is thrown.
   */
  void checkAbduct(Expr a);

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
   * Sets that the problem has been extended. This sets the smt mode of the
   * solver to SMT_MODE_ASSERT, and clears the list of assumptions from the
   * previous call to checkSatisfiability.
   */
  void setProblemExtended();

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
   * Get the model, if it is available and return a pointer to it
   *
   * This ensures that the model is currently available, which means that
   * CVC4 is producing models, and is in "SAT mode", otherwise an exception
   * is thrown.
   *
   * The flag c is used for giving an error message to indicate the context
   * this method was called.
   */
  theory::TheoryModel* getAvailableModel(const char* c) const;

  /**
   * Fully type-check the argument, and also type-check that it's
   * actually Boolean.
   *
   * throw@ TypeCheckingException
   */
  void ensureBoolean(const Expr& e);

  void internalPush();

  void internalPop(bool immediate = false);

  void doPendingPops();

  /**
   * Internally handle the setting of a logic.  This function should always
   * be called when d_logic is updated.
   */
  void setLogicInternal();

  /**
   * Add to Model command.  This is used for recording a command
   * that should be reported during a get-model call.
   */
  void addToModelCommandAndDump(const Command& c,
                                uint32_t flags = 0,
                                bool userVisible = true,
                                const char* dumpTag = "declarations");

  /* Check satisfiability (used for query and check-sat). */
  Result checkSatisfiability(const Expr& assumption,
                             bool inUnsatCore,
                             bool isQuery);
  Result checkSatisfiability(const std::vector<Expr>& assumptions,
                             bool inUnsatCore,
                             bool isQuery);

  /**
   * Check that all Expr in formals are of BOUND_VARIABLE kind, where func is
   * the function that the formal argument list is for. This method is used
   * as a helper function when defining (recursive) functions.
   */
  void debugCheckFormals(const std::vector<Expr>& formals, Expr func);

  /**
   * Checks whether formula is a valid function body for func whose formal
   * argument list is stored in formals. This method is
   * used as a helper function when defining (recursive) functions.
   */
  void debugCheckFunctionBody(Expr formula,
                              const std::vector<Expr>& formals,
                              Expr func);
  /**
   * Get abduct internal.
   *
   * Get the next abduct from the internal subsolver d_subsolver. If
   * successful, this method returns true and sets abd to that abduct.
   *
   * This method assumes d_subsolver has been initialized to do abduction
   * problems.
   */
  bool getAbductInternal(Expr& abd);

  /**
   * Helper method to obtain both the heap and nil from the solver. Returns a
   * std::pair where the first element is the heap expression and the second
   * element is the nil expression.
   */
  std::pair<Expr, Expr> getSepHeapAndNilExpr();

  /**
   * Get expanded assertions.
   *
   * Return the set of assertions, after expanding definitions.
   */
  std::vector<Expr> getExpandedAssertions();

  /* Members -------------------------------------------------------------- */

  /** Expr manager context */
  context::Context* d_context;
  /** User level context */
  context::UserContext* d_userContext;
  /** The context levels of user pushes */
  std::vector<int> d_userLevels;

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

  /** The SMT engine subsolver
   *
   * This is a separate copy of the SMT engine which is used for making
   * calls that cannot be answered by this copy of the SMT engine. An example
   * of invoking this subsolver is the get-abduct command, where we wish to
   * solve a sygus conjecture based on the current assertions. In particular,
   * consider the input:
   *   (assert A)
   *   (get-abduct B)
   * In the copy of the SMT engine where these commands are issued, we maintain
   * A in the assertion stack. To solve the abduction problem, instead of
   * modifying the assertion stack to remove A and add the sygus conjecture
   * (exists I. ...), we invoke a fresh copy of the SMT engine and leave the
   * assertion stack unchaged. This copy of the SMT engine can be further
   * queried for information regarding further solutions.
   */
  std::unique_ptr<SmtEngine> d_subsolver;

  /**
   * If applicable, the function-to-synthesize that the subsolver is solving
   * for. This is used for the get-abduct command.
   */
  Expr d_sssf;

  /**
   * The conjecture of the current abduction problem. This expression is only
   * valid while we are in mode SMT_MODE_ABDUCT.
   */
  Expr d_abdConj;

  /** recursive function definition abstractions for --fmf-fun */
  std::map<Node, TypeNode> d_fmfRecFunctionsAbs;
  std::map<Node, std::vector<Node> > d_fmfRecFunctionsConcrete;
  NodeList* d_fmfRecFunctionsDefined;

  /**
   * The assertion list (before any conversion) for supporting
   * getAssertions().  Only maintained if in interactive mode.
   */
  AssertionList* d_assertionList;

  /**
   * The list of assumptions from the previous call to checkSatisfiability.
   * Note that if the last call to checkSatisfiability was a validity check,
   * i.e., a call to query(a1, ..., an), then d_assumptions contains one single
   * assumption ~(a1 AND ... AND an).
   */
  std::vector<Expr> d_assumptions;

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
   * A vector of command definitions to be imported in the new
   * SmtEngine when checking unsat-cores.
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

  /** Whether this is an internal subsolver. */
  bool d_isInternalSubsolver;

  /**
   * Number of internal pops that have been deferred.
   */
  unsigned d_pendingPops;

  /**
   * Whether or not this SmtEngine is fully initialized (post-construction).
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  bool d_fullyInited;

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

  /*
   * Whether we did a global negation of the formula.
   */
  bool d_globalNegation;

  /**
   * Most recent result of last checkSat/query or (set-info :status).
   */
  Result d_status;

  /**
   * The expected status of the next satisfiability check.
   */
  Result d_expectedStatus;

  SmtMode d_smtMode;

  /**
   * The input file name (if any) or the name set through setInfo (if any)
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

  StatisticsRegistry* d_statisticsRegistry;

  smt::SmtEngineStatistics* d_stats;

  /** Container for the lemma input and output channels for this SmtEngine.*/
  LemmaChannels* d_channels;

  /*---------------------------- sygus commands  ---------------------------*/

  /**
   * Set sygus conjecture is stale. The sygus conjecture is stale if either:
   * (1) no sygus conjecture has been added as an assertion to this SMT engine,
   * (2) there is a sygus conjecture that has been added as an assertion
   * internally to this SMT engine, and there have been further calls such that
   * the asserted conjecture is no longer up-to-date.
   *
   * This method should be called when new sygus constraints are asserted and
   * when functions-to-synthesize are declared. This function pops a user
   * context if we are in incremental mode and the sygus conjecture was
   * previously not stale.
   */
  void setSygusConjectureStale();

  /*------------------------- end of sygus commands ------------------------*/
}; /* class SmtEngine */

/* -------------------------------------------------------------------------- */

}/* CVC4 namespace */

#endif /* CVC4__SMT_ENGINE_H */
