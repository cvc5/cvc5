/*********************                                                        */
/*! \file smt_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "options/options.h"
#include "proof/unsat_core.h"
#include "smt/logic_exception.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "util/hash.h"
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

namespace api {
class Solver;
}  // namespace api

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
/** Utilities */
class SmtEngineState;
class AbstractValues;
class Assertions;
class ExprNames;
class DumpManager;
class ResourceOutListener;
class SmtNodeManagerListener;
class OptionsManager;
class Preprocessor;
/** Subsolvers */
class SmtSolver;
class SygusSolver;
class AbductionSolver;
class InterpolationSolver;
class QuantElimSolver;
/**
 * Representation of a defined function.  We keep these around in
 * SmtEngine to permit expanding definitions late (and lazily), to
 * support getValue() over defined functions, to support user output
 * in terms of defined functions, etc.
 */
class DefinedFunction;

struct SmtEngineStatistics;
class SmtScope;
class ProcessAssertions;
class PfManager;

ProofManager* currentProofManager();
}/* CVC4::smt namespace */

/* -------------------------------------------------------------------------- */

namespace theory {
  class TheoryModel;
  class Rewriter;
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
  friend class ::CVC4::api::Solver;
  // TODO (Issue #1096): Remove this friend relationship.
  friend class ::CVC4::preprocessing::PreprocessingPassContext;
  friend class ::CVC4::smt::SmtEngineState;
  friend class ::CVC4::smt::SmtScope;
  friend class ::CVC4::smt::ProcessAssertions;
  friend class ::CVC4::smt::SmtSolver;
  friend ProofManager* ::CVC4::smt::currentProofManager();
  friend class ::CVC4::LogicRequest;
  friend class ::CVC4::theory::TheoryModel;
  friend class ::CVC4::theory::Rewriter;

  /* .......................................................................  */
 public:
  /* .......................................................................  */

  /**
   * Construct an SmtEngine with the given expression manager.
   * If provided, optr is a pointer to a set of options that should initialize the values
   * of the options object owned by this class.
   */
  SmtEngine(ExprManager* em, Options* optr = nullptr);
  /** Destruct the SMT engine.  */
  ~SmtEngine();

  //--------------------------------------------- concerning the state

  /**
   * This is the main initialization procedure of the SmtEngine.
   *
   * Should be called whenever the final options and logic for the problem are
   * set (at least, those options that are not permitted to change after
   * assertions and queries are made).
   *
   * Internally, this creates the theory engine, prop engine, decision engine,
   * and other utilities whose initialization depends on the final set of
   * options being set.
   *
   * This post-construction initialization is automatically triggered by the
   * use of the SmtEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  void finishInit();
  /**
   * Return true if this SmtEngine is fully initialized (post-construction)
   * by the above call.
   */
  bool isFullyInited() const;
  /**
   * Return true if a checkEntailed() or checkSatisfiability() has been made.
   */
  bool isQueryMade() const;
  /** Return the user context level.  */
  size_t getNumUserLevels() const;
  /** Return the current mode of the solver. */
  SmtMode getSmtMode() const;
  /**
   * Returns the most recent result of checkSat/checkEntailed or
   * (set-info :status).
   */
  Result getStatusOfLastCommand() const;
  //--------------------------------------------- end concerning the state

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

  /** Get the logic information set by the user. */
  LogicInfo getUserLogicInfo() const;

  /**
   * Set information about the script executing.
   * @throw OptionException, ModalException
   */
  void setInfo(const std::string& key, const CVC4::SExpr& value);

  /** Return true if given keyword is a valid SMT-LIB v2 get-info flag. */
  bool isValidGetInfoFlag(const std::string& key) const;

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
  /** Is this an internal subsolver? */
  bool isInternalSubsolver() const;

  /**
   * Notify that we are now parsing the input with the given filename.
   * This call sets the filename maintained by this SmtEngine for bookkeeping
   * and also makes a copy of the current options of this SmtEngine. This
   * is required so that the SMT-LIB command (reset) returns the SmtEngine
   * to a state where its options were prior to parsing but after e.g.
   * reading command line options.
   */
  void notifyStartParsing(std::string filename);
  /** return the input name (if any) */
  const std::string& getFilename() const;

  /**
   * Get the model (only if immediately preceded by a SAT or NOT_ENTAILED
   * query).  Only permitted if produce-models is on.
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
   * Can be called only if immediately preceded by a SAT or NOT_ENTAILED query.
   * Only permitted if produce-models is on, and the block-models option is set
   * to a mode other than "none".
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
   *
   * @param func a variable of function type that expects the arguments in
   *             formal
   * @param formals a list of BOUND_VARIABLE expressions
   * @param formula The body of the function, must not contain func
   * @param global True if this definition is global (i.e. should persist when
   *               popping the user context)
   */
  void defineFunction(Expr func,
                      const std::vector<Expr>& formals,
                      Expr formula,
                      bool global = false);

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
   *
   * @param global True if this definition is global (i.e. should persist when
   *               popping the user context)
   */
  void defineFunctionsRec(const std::vector<Expr>& funcs,
                          const std::vector<std::vector<Expr>>& formals,
                          const std::vector<Expr>& formulas,
                          bool global = false);
  /**
   * Define function recursive
   * Same as above, but for a single function.
   */
  void defineFunctionRec(Expr func,
                         const std::vector<Expr>& formals,
                         Expr formula,
                         bool global = false);
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
  Result assertFormula(const Node& formula, bool inUnsatCore = true);

  /**
   * Check if a given (set of) expression(s) is entailed with respect to the
   * current set of assertions. We check this by asserting the negation of
   * the (big AND over the) given (set of) expression(s).
   * Returns ENTAILED, NOT_ENTAILED, or ENTAILMENT_UNKNOWN result.
   *
   * @throw Exception
   */
  Result checkEntailed(const Expr& assumption = Expr(),
                       bool inUnsatCore = true);
  Result checkEntailed(const std::vector<Expr>& assumptions,
                       bool inUnsatCore = true);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns SAT, UNSAT, or SAT_UNKNOWN result.
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
  std::vector<Node> getUnsatAssumptions(void);

  /*---------------------------- sygus commands  ---------------------------*/

  /**
   * Add sygus variable declaration.
   *
   * Declared SyGuS variables may be used in SyGuS constraints, in which they
   * are assumed to be universally quantified.
   *
   * In SyGuS semantics, declared functions are treated in the same manner as
   * declared variables, i.e. as universally quantified (function) variables
   * which can occur in the SyGuS constraints that compose the conjecture to
   * which a function is being synthesized. Thus declared functions should use
   * this method as well.
   */
  void declareSygusVar(const std::string& id, Node var, TypeNode type);

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
                       Node func,
                       TypeNode type,
                       bool isInv,
                       const std::vector<Node>& vars);

  /** Add a regular sygus constraint.*/
  void assertSygusConstraint(Node constraint);

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
  void assertSygusInvConstraint(Node inv, Node pre, Node trans, Node post);
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
  Node simplify(const Node& e);

  /**
   * Expand the definitions in a term or formula.  No other
   * simplification or normalization is done.
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  Node expandDefinitions(const Node& e);

  /**
   * Get the assigned value of an expr (only if immediately preceded by a SAT
   * or NOT_ENTAILED query).  Only permitted if the SmtEngine is set to operate
   * interactively and produce-models is on.
   *
   * @throw ModalException, TypeCheckingException, LogicException,
   *        UnsafeInterruptException
   */
  Node getValue(const Node& e) const;

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
   * NOT_ENTAILED query).  Only permitted if the SmtEngine is set to
   * operate interactively and produce-assignments is on.
   */
  std::vector<std::pair<Expr, Expr> > getAssignment();

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
   * This method returns true if we are in a state immediately preceded by
   * a successful call to checkSynth.
   *
   * This method adds entries to solMap that map functions-to-synthesize with
   * their solutions, for all active conjectures. This should be called
   * immediately after the solver answers unsat for sygus input.
   *
   * Specifically, given a sygus conjecture of the form
   *   exists x1...xn. forall y1...yn. P( x1...xn, y1...yn )
   * where x1...xn are second order bound variables, we map each xi to
   * lambda term in solMap such that
   *    forall y1...yn. P( solMap[x1]...solMap[xn], y1...yn )
   * is a valid formula.
   */
  bool getSynthSolutions(std::map<Node, Node>& solMap);

  /**
   * Do quantifier elimination.
   *
   * This function takes as input a quantified formula q
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
   *   - ( A ^ q ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn.
   *
   * If doFull = false, then
   *   - (A ^ q) => (A ^ ret) if Q is forall or
   *     (A ^ ret) => (A ^ q) if Q is exists,
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n
   *     where for each i=1,...n, formula ret^Q_i
   *     is the result of calling doQuantifierElimination
   *     for q with the set of assertions A^Q_{i-1}.
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
  Node getQuantifierElimination(Node q, bool doFull, bool strict = true);

  /**
   * This method asks this SMT engine to find an interpolant with respect to
   * the current assertion stack (call it A) and the conjecture (call it B). If
   * this method returns true, then interpolant is set to a formula I such that
   * A ^ ~I and I ^ ~B are both unsatisfiable.
   *
   * The argument grammarType is a sygus datatype type that encodes the syntax
   * restrictions on the shapes of possible solutions.
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getInterpol(const Node& conj,
                   const TypeNode& grammarType,
                   Node& interpol);

  /** Same as above, but without user-provided grammar restrictions */
  bool getInterpol(const Node& conj, Node& interpol);

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
  bool getAbduct(const Node& conj, const TypeNode& grammarType, Node& abd);

  /** Same as above, but without user-provided grammar restrictions */
  bool getAbduct(const Node& conj, Node& abd);

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
   * Get an unsatisfiable core (only if immediately preceded by an UNSAT or
   * ENTAILED query).  Only permitted if CVC4 was built with unsat-core support
   * and produce-unsat-cores is on.
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
   * Set a per-call time limit for SmtEngine operations.
   *
   * A per-call time limit can be set at the same time and replaces
   * any per-call time limit currently in effect.
   * Resource limits (either per-call or cumulative) can be set in
   * addition to a time limit; the SmtEngine obeys all three of them.
   *
   * Note that the per-call timer only ticks away when one of the
   * SmtEngine's workhorse functions (things like assertFormula(),
   * checkEntailed(), checkSat(), and simplify()) are running.
   * Between calls, the timer is still.
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
   */
  void setTimeLimit(unsigned long millis);

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

  /** Permit access to the underlying ExprManager. */
  ExprManager* getExprManager() const { return d_exprManager; }

  /** Permit access to the underlying NodeManager. */
  NodeManager* getNodeManager() const;

  /** Export statistics from this SmtEngine. */
  Statistics getStatistics() const;

  /** Get the value of one named statistic from this SmtEngine. */
  SExpr getStatistic(std::string name) const;

  /** Flush statistic from this SmtEngine. Safe to use in a signal handler. */
  void safeFlushStatistics(int fd) const;

  /**
   * Set user attribute.
   * This function is called when an attribute is set by a user.
   * In SMT-LIBv2 this is done via the syntax (! expr :attr)
   */
  void setUserAttribute(const std::string& attr,
                        Expr expr,
                        const std::vector<Expr>& expr_values,
                        const std::string& str_value);

  /**
   * Get expression name.
   *
   * Return true if given expressoion has a name in the current context.
   * If it returns true, the name of expression 'e' is stored in 'name'.
   */
  bool getExpressionName(const Node& e, std::string& name) const;

  /**
   * Set name of given expression 'e' to 'name'.
   *
   * This information is user-context-dependent.
   * If 'e' already has a name, it is overwritten.
   */
  void setExpressionName(const Node& e, const std::string& name);

  /** Get the options object (const and non-const versions) */
  Options& getOptions();
  const Options& getOptions() const;

  /** Get the resource manager of this SMT engine */
  ResourceManager* getResourceManager();

  /** Permit access to the underlying dump manager. */
  smt::DumpManager* getDumpManager();

  /** Get a pointer to the Rewriter owned by this SmtEngine. */
  theory::Rewriter* getRewriter() { return d_rewriter.get(); }

  /**
   * Get expanded assertions.
   *
   * Return the set of assertions, after expanding definitions.
   */
  std::vector<Expr> getExpandedAssertions();
  /* .......................................................................  */
 private:
  /* .......................................................................  */

  /** The type of our internal map of defined functions */
  typedef context::CDHashMap<Node, smt::DefinedFunction, NodeHashFunction>
      DefinedFunctionMap;
  /** The type of our internal assertion list */
  typedef context::CDList<Node> AssertionList;
  /** The type of our internal assignment set */
  typedef context::CDHashSet<Node, NodeHashFunction> AssignmentSet;

  // disallow copy/assignment
  SmtEngine(const SmtEngine&) = delete;
  SmtEngine& operator=(const SmtEngine&) = delete;

  /** Set solver instance that owns this SmtEngine. */
  void setSolver(api::Solver* solver) { d_solver = solver; }

  /** Get a pointer to the UserContext owned by this SmtEngine. */
  context::UserContext* getUserContext();

  /** Get a pointer to the Context owned by this SmtEngine. */
  context::Context* getContext();

  /** Get a pointer to the TheoryEngine owned by this SmtEngine. */
  TheoryEngine* getTheoryEngine();

  /** Get a pointer to the PropEngine owned by this SmtEngine. */
  prop::PropEngine* getPropEngine();

  /**
   * Get a pointer to the ProofManager owned by this SmtEngine.
   * TODO (project #37): this is the old proof manager and will be deleted
   */
  ProofManager* getProofManager() { return d_proofManager.get(); };

  /** Get a pointer to the StatisticsRegistry owned by this SmtEngine. */
  StatisticsRegistry* getStatisticsRegistry()
  {
    return d_statisticsRegistry.get();
  };

  /**
   * Internal method to get an unsatisfiable core (only if immediately preceded
   * by an UNSAT or ENTAILED query). Only permitted if CVC4 was built with
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
   * Check that a solution to an interpolation problem is indeed a solution.
   *
   * The check is made by determining that the assertions imply the solution of
   * the interpolation problem (interpol), and the solution implies the goal
   * (conj). If these criteria are not met, an internal error is thrown.
   */
  void checkInterpol(Expr interpol,
                     const std::vector<Expr>& easserts,
                     const Node& conj);

  /**
   * This is called by the destructor, just before destroying the
   * PropEngine, TheoryEngine, and DecisionEngine (in that order).  It
   * is important because there are destruction ordering issues
   * between PropEngine and Theory.
   */
  void shutdown();

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

  // --------------------------------------- callbacks from the state
  /**
   * Notify push pre, which is called just before the user context of the state
   * pushes. This processes all pending assertions.
   */
  void notifyPushPre();
  /**
   * Notify push post, which is called just after the user context of the state
   * pushes. This performs a push on the underlying prop engine.
   */
  void notifyPushPost();
  /**
   * Notify pop pre, which is called just before the user context of the state
   * pops. This performs a pop on the underlying prop engine.
   */
  void notifyPopPre();
  /**
   * Notify post solve pre, which is called once per check-sat query. It
   * is triggered when the first d_state.doPendingPops() is issued after the
   * check-sat. This method is called before the contexts pop in the method
   * doPendingPops.
   */
  void notifyPostSolvePre();
  /**
   * Same as above, but after contexts are popped. This calls the postsolve
   * method of the underlying TheoryEngine.
   */
  void notifyPostSolvePost();
  // --------------------------------------- end callbacks from the state

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

  /*
   * Check satisfiability (used to check satisfiability and entailment).
   */
  Result checkSatInternal(const std::vector<Node>& assumptions,
                          bool inUnsatCore,
                          bool isEntailmentCheck);

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
   * Helper method to obtain both the heap and nil from the solver. Returns a
   * std::pair where the first element is the heap expression and the second
   * element is the nil expression.
   */
  std::pair<Expr, Expr> getSepHeapAndNilExpr();

  /* Members -------------------------------------------------------------- */

  /** Solver instance that owns this SmtEngine instance. */
  api::Solver* d_solver = nullptr;

  /**
   * The state of this SmtEngine, which is responsible for maintaining which
   * SMT mode we are in, the contexts, the last result, etc.
   */
  std::unique_ptr<smt::SmtEngineState> d_state;

  /** Our expression manager */
  ExprManager* d_exprManager;
  /** Our internal expression/node manager */
  NodeManager* d_nodeManager;
  /** Abstract values */
  std::unique_ptr<smt::AbstractValues> d_absValues;
  /** Assertions manager */
  std::unique_ptr<smt::Assertions> d_asserts;
  /** Expression names */
  std::unique_ptr<smt::ExprNames> d_exprNames;
  /** The dump manager */
  std::unique_ptr<smt::DumpManager> d_dumpm;
  /** Resource out listener */
  std::unique_ptr<smt::ResourceOutListener> d_routListener;
  /** Node manager listener */
  std::unique_ptr<smt::SmtNodeManagerListener> d_snmListener;

  /** The SMT solver */
  std::unique_ptr<smt::SmtSolver> d_smtSolver;

  /** The (old) proof manager TODO (project #37): delete this */
  std::unique_ptr<ProofManager> d_proofManager;

  /**
   * The proof manager, which manages all things related to checking,
   * processing, and printing proofs.
   */
  std::unique_ptr<smt::PfManager> d_pfManager;

  /**
   * The rewriter associated with this SmtEngine. We have a different instance
   * of the rewriter for each SmtEngine instance. This is because rewriters may
   * hold references to objects that belong to theory solvers, which are
   * specific to an SmtEngine/TheoryEngine instance.
   */
  std::unique_ptr<theory::Rewriter> d_rewriter;

  /** An index of our defined functions */
  DefinedFunctionMap* d_definedFunctions;

  /** The solver for sygus queries */
  std::unique_ptr<smt::SygusSolver> d_sygusSolver;

  /** The solver for abduction queries */
  std::unique_ptr<smt::AbductionSolver> d_abductSolver;
  /** The solver for interpolation queries */
  std::unique_ptr<smt::InterpolationSolver> d_interpolSolver;
  /** The solver for quantifier elimination queries */
  std::unique_ptr<smt::QuantElimSolver> d_quantElimSolver;
  /**
   * List of items for which to retrieve values using getAssignment().
   */
  AssignmentSet* d_assignments;

  /**
   * The logic we're in. This logic may be an extension of the logic set by the
   * user.
   */
  LogicInfo d_logic;

  /** The logic set by the user. */
  LogicInfo d_userLogic;

  /**
   * Keep a copy of the original option settings (for reset()).
   */
  Options d_originalOptions;

  /** Whether this is an internal subsolver. */
  bool d_isInternalSubsolver;

  /**
   * Verbosity of various commands.
   */
  std::map<std::string, Integer> d_commandVerbosity;

  std::unique_ptr<StatisticsRegistry> d_statisticsRegistry;

  std::unique_ptr<smt::SmtEngineStatistics> d_stats;

  /** The options object */
  Options d_options;
  /**
   * Manager for limiting time and abstract resource usage.
   */
  std::unique_ptr<ResourceManager> d_resourceManager;
  /**
   * The options manager, which is responsible for implementing core options
   * such as those related to time outs and printing. It is also responsible
   * for set default options based on the logic.
   */
  std::unique_ptr<smt::OptionsManager> d_optm;
  /**
   * The preprocessor.
   */
  std::unique_ptr<smt::Preprocessor> d_pp;
  /**
   * The global scope object. Upon creation of this SmtEngine, it becomes the
   * SmtEngine in scope. It says the SmtEngine in scope until it is destructed,
   * or another SmtEngine is created.
   */
  std::unique_ptr<smt::SmtScope> d_scope;
}; /* class SmtEngine */

/* -------------------------------------------------------------------------- */

}/* CVC4 namespace */

#endif /* CVC4__SMT_ENGINE_H */
