/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SmtEngine: the main public entry point of libcvc5.
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT_ENGINE_H
#define CVC5__SMT_ENGINE_H

#include <map>
#include <memory>
#include <string>
#include <vector>

#include "context/cdhashmap_forward.h"
#include "cvc5_export.h"
#include "options/options.h"
#include "smt/output_manager.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "util/result.h"

namespace cvc5 {

template <bool ref_count> class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
class TypeNode;

class Env;
class NodeManager;
class TheoryEngine;
class UnsatCore;
class LogicRequest;
class StatisticsRegistry;
class Printer;
class ResourceManager;

/* -------------------------------------------------------------------------- */

namespace api {
class Solver;
}  // namespace api

/* -------------------------------------------------------------------------- */

namespace context {
  class Context;
  class UserContext;
  }  // namespace context

/* -------------------------------------------------------------------------- */

namespace preprocessing {
class PreprocessingPassContext;
}

/* -------------------------------------------------------------------------- */

namespace prop {
  class PropEngine;
  }  // namespace prop

/* -------------------------------------------------------------------------- */

namespace smt {
/** Utilities */
class Model;
class SmtEngineState;
class AbstractValues;
class Assertions;
class DumpManager;
class ResourceOutListener;
class SmtNodeManagerListener;
class OptionsManager;
class Preprocessor;
class CheckModels;
/** Subsolvers */
class SmtSolver;
class SygusSolver;
class AbductionSolver;
class InterpolationSolver;
class QuantElimSolver;

struct SmtEngineStatistics;
class SmtScope;
class PfManager;
class UnsatCoreManager;

}  // namespace smt

/* -------------------------------------------------------------------------- */

namespace theory {
  class Rewriter;
  class QuantifiersEngine;
  }  // namespace theory

/* -------------------------------------------------------------------------- */

class CVC5_EXPORT SmtEngine
{
  friend class ::cvc5::api::Solver;
  friend class ::cvc5::smt::SmtEngineState;
  friend class ::cvc5::smt::SmtScope;
  friend class ::cvc5::LogicRequest;

  /* .......................................................................  */
 public:
  /* .......................................................................  */

  /**
   * Construct an SmtEngine with the given expression manager.
   * If provided, optr is a pointer to a set of options that should initialize the values
   * of the options object owned by this class.
   */
  SmtEngine(NodeManager* nm, Options* optr = nullptr);
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
   * Whether the SmtMode allows for get-value, get-model, get-assignment, etc.
   * This is equivalent to:
   * getSmtMode()==SmtMode::SAT || getSmtMode()==SmtMode::SAT_UNKNOWN
   */
  bool isSmtModeSat() const;
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
  const LogicInfo& getLogicInfo() const;

  /** Get the logic information set by the user. */
  LogicInfo getUserLogicInfo() const;

  /**
   * Set information about the script executing.
   */
  void setInfo(const std::string& key, const std::string& value);

  /** Return true if given keyword is a valid SMT-LIB v2 get-info flag. */
  bool isValidGetInfoFlag(const std::string& key) const;

  /** Query information about the SMT environment.  */
  std::string getInfo(const std::string& key) const;

  /**
   * Set an aspect of the current SMT execution environment.
   * @throw OptionException, ModalException
   */
  void setOption(const std::string& key, const std::string& value);

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
  void notifyStartParsing(const std::string& filename) CVC5_EXPORT;
  /** return the input name (if any) */
  const std::string& getFilename() const;

  /**
   * Helper method for the API to put the last check result into the statistics.
   */
  void setResultStatistic(const std::string& result) CVC5_EXPORT;
  /**
   * Helper method for the API to put the total runtime into the statistics.
   */
  void setTotalTimeStatistic(double seconds) CVC5_EXPORT;

  /**
   * Get the model (only if immediately preceded by a SAT or NOT_ENTAILED
   * query).  Only permitted if produce-models is on.
   */
  smt::Model* getModel();

  /**
   * Block the current model. Can be called only if immediately preceded by
   * a SAT or INVALID query. Only permitted if produce-models is on, and the
   * block-models option is set to a mode other than "none".
   *
   * This adds an assertion to the assertion stack that blocks the current
   * model based on the current options configured by cvc5.
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
  Result blockModelValues(const std::vector<Node>& exprs);

  /**
   * Declare heap. For smt2 inputs, this is called when the command
   * (declare-heap (locT datat)) is invoked by the user. This sets locT as the
   * location type and dataT is the data type for the heap. This command should
   * be executed only once, and must be invoked before solving separation logic
   * inputs.
   */
  void declareSepHeap(TypeNode locT, TypeNode dataT);

  /**
   * Get the separation heap types, which extracts which types were passed to
   * the method above.
   *
   * @return true if the separation logic heap types have been declared.
   */
  bool getSepHeapTypes(TypeNode& locT, TypeNode& dataT);

  /** When using separation logic, obtain the expression for the heap.  */
  Node getSepHeapExpr();

  /** When using separation logic, obtain the expression for nil.  */
  Node getSepNilExpr();

  /**
   * Get an aspect of the current SMT execution environment.
   * @throw OptionException
   */
  std::string getOption(const std::string& key) const;

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
  void defineFunction(Node func,
                      const std::vector<Node>& formals,
                      Node formula,
                      bool global = false);

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
  void defineFunctionsRec(const std::vector<Node>& funcs,
                          const std::vector<std::vector<Node>>& formals,
                          const std::vector<Node>& formulas,
                          bool global = false);
  /**
   * Define function recursive
   * Same as above, but for a single function.
   */
  void defineFunctionRec(Node func,
                         const std::vector<Node>& formals,
                         Node formula,
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
  Result checkEntailed(const Node& assumption, bool inUnsatCore = true);
  Result checkEntailed(const std::vector<Node>& assumptions,
                       bool inUnsatCore = true);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns SAT, UNSAT, or SAT_UNKNOWN result.
   *
   * @throw Exception
   */
  Result checkSat();
  Result checkSat(const Node& assumption, bool inUnsatCore = true);
  Result checkSat(const std::vector<Node>& assumptions,
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
  void declareSygusVar(Node var);

  /**
   * Add a function-to-synthesize declaration.
   *
   * The given sygusType may not correspond to the actual function type of func
   * but to a datatype encoding the syntax restrictions for the
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
  void declareSynthFun(Node func,
                       TypeNode sygusType,
                       bool isInv,
                       const std::vector<Node>& vars);
  /**
   * Same as above, without a sygus type.
   */
  void declareSynthFun(Node func, bool isInv, const std::vector<Node>& vars);

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
   * Declare pool whose initial value is the terms in initValue. A pool is
   * a variable of type (Set T) that is used in quantifier annotations and does
   * not occur in constraints.
   *
   * @param p The pool to declare, which should be a variable of type (Set T)
   * for some type T.
   * @param initValue The initial value of p, which should be a vector of terms
   * of type T.
   */
  void declarePool(const Node& p, const std::vector<Node>& initValue);
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
   * Expand the definitions in a term or formula.
   *
   * @param n The node to expand
   *
   * @throw TypeCheckingException, LogicException, UnsafeInterruptException
   */
  Node expandDefinitions(const Node& n);

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
  std::vector<Node> getValues(const std::vector<Node>& exprs);

  /** print instantiations
   *
   * Print all instantiations for all quantified formulas on out,
   * returns true if at least one instantiation was printed. The type of output
   * (list, num, etc.) is determined by printInstMode.
   */
  void printInstantiations(std::ostream& out);
  /**
   * Print the current proof. This method should be called after an UNSAT
   * response. It gets the proof of false from the PropEngine and passes
   * it to the ProofManager, which post-processes the proof and prints it
   * in the proper format.
   */
  void printProof();

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
  void getInstantiatedQuantifiedFormulas(std::vector<Node>& qs);

  /**
   * Get instantiation term vectors for quantified formula q.
   *
   * This method is similar to above, but in the example above, we return the
   * (vectors of) terms t1, ..., tn instead.
   *
   * Notice that these are not guaranteed to come in the same order as the
   * instantiation lemmas above.
   */
  void getInstantiationTermVectors(Node q,
                                   std::vector<std::vector<Node>>& tvecs);
  /**
   * As above but only the instantiations that were relevant for the
   * refutation.
   */
  void getRelevantInstantiationTermVectors(
      std::map<Node, std::vector<std::vector<Node>>>& insts);
  /**
   * Get instantiation term vectors, which maps each instantiated quantified
   * formula to the list of instantiations for that quantified formula. This
   * list is minimized if proofs are enabled, and this call is immediately
   * preceded by an UNSAT or ENTAILED query
   */
  void getInstantiationTermVectors(
      std::map<Node, std::vector<std::vector<Node>>>& insts);

  /**
   * Get an unsatisfiable core (only if immediately preceded by an UNSAT or
   * ENTAILED query).  Only permitted if cvc5 was built with unsat-core support
   * and produce-unsat-cores is on.
   */
  UnsatCore getUnsatCore();

  /**
   * Get a refutation proof (only if immediately preceded by an UNSAT or
   * ENTAILED query). Only permitted if cvc5 was built with proof support and
   * the proof option is on. */
  std::string getProof();

  /**
   * Get the current set of assertions.  Only permitted if the
   * SmtEngine is set to operate interactively.
   */
  std::vector<Node> getAssertions();

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
   * versions of cvc5 (as may the number of conflicts required, anyway),
   * and it might even be different between instances of the same version
   * of cvc5 on different platforms.
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
  void setResourceLimit(uint64_t units, bool cumulative = false);

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
  void setTimeLimit(uint64_t millis);

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

  /** Permit access to the underlying NodeManager. */
  NodeManager* getNodeManager() const;

  /**
   * Print statistics from the statistics registry in the env object owned by
   * this SmtEngine.
   */
  void printStatistics(std::ostream& out) const;

  /**
   * Print statistics from the statistics registry in the env object owned by
   * this SmtEngine. Safe to use in a signal handler.
   */
  void printStatisticsSafe(int fd) const;

  /**
   * Print the changes to the statistics from the statistics registry in the
   * env object owned by this SmtEngine since this method was called the last
   * time. Internally prints the diff and then stores a snapshot for the next
   * call.
   */
  void printStatisticsDiff(std::ostream&) const;

  /**
   * Set user attribute.
   * This function is called when an attribute is set by a user.
   * In SMT-LIBv2 this is done via the syntax (! expr :attr)
   */
  void setUserAttribute(const std::string& attr,
                        Node expr,
                        const std::vector<Node>& expr_values,
                        const std::string& str_value);

  /** Get the options object (const and non-const versions) */
  Options& getOptions();
  const Options& getOptions() const;

  /** Get a pointer to the UserContext owned by this SmtEngine. */
  context::UserContext* getUserContext();

  /** Get a pointer to the Context owned by this SmtEngine. */
  context::Context* getContext();

  /** Get a pointer to the TheoryEngine owned by this SmtEngine. */
  TheoryEngine* getTheoryEngine();

  /** Get a pointer to the PropEngine owned by this SmtEngine. */
  prop::PropEngine* getPropEngine();

  /** Get the resource manager of this SMT engine */
  ResourceManager* getResourceManager() const;

  /** Permit access to the underlying dump manager. */
  smt::DumpManager* getDumpManager();

  /** Get the printer used by this SMT engine */
  const Printer& getPrinter() const;

  /** Get the output manager for this SMT engine */
  OutputManager& getOutputManager();

  /** Get a pointer to the Rewriter owned by this SmtEngine. */
  theory::Rewriter* getRewriter();
  /**
   * Get expanded assertions.
   *
   * Return the set of assertions, after expanding definitions.
   */
  std::vector<Node> getExpandedAssertions();

  /**
   * !!!!! temporary, until the environment is passsed to all classes that
   * require it.
   */
  Env& getEnv();
  /* .......................................................................  */
 private:
  /* .......................................................................  */

  // disallow copy/assignment
  SmtEngine(const SmtEngine&) = delete;
  SmtEngine& operator=(const SmtEngine&) = delete;

  /** Set solver instance that owns this SmtEngine. */
  void setSolver(api::Solver* solver) { d_solver = solver; }

  /** Get a pointer to the (new) PfManager owned by this SmtEngine. */
  smt::PfManager* getPfManager() { return d_pfManager.get(); };

  /** Get a pointer to the StatisticsRegistry owned by this SmtEngine. */
  StatisticsRegistry& getStatisticsRegistry();

  /**
   * Internal method to get an unsatisfiable core (only if immediately preceded
   * by an UNSAT or ENTAILED query). Only permitted if cvc5 was built with
   * unsat-core support and produce-unsat-cores is on. Does not dump the
   * command.
   */
  UnsatCore getUnsatCoreInternal();

  /**
   * Check that a generated proof checks. This method is the same as printProof,
   * but does not print the proof. Like that method, it should be called
   * after an UNSAT response. It ensures that a well-formed proof of false
   * can be constructed by the combination of the PropEngine and ProofManager.
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
   * Check that a solution to an interpolation problem is indeed a solution.
   *
   * The check is made by determining that the assertions imply the solution of
   * the interpolation problem (interpol), and the solution implies the goal
   * (conj). If these criteria are not met, an internal error is thrown.
   */
  void checkInterpol(Node interpol,
                     const std::vector<Node>& easserts,
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
   * Get the (SMT-level) model pointer, if we are in SAT mode. Otherwise,
   * return nullptr.
   *
   * This ensures that the underlying theory model of the SmtSolver maintained
   * by this class is currently available, which means that cvc5 is producing
   * models, and is in "SAT mode", otherwise a recoverable exception is thrown.
   *
   * @param c used for giving an error message to indicate the context
   * this method was called.
   */
  smt::Model* getAvailableModel(const char* c) const;
  /**
   * Get available quantifiers engine, which throws a modal exception if it
   * does not exist. This can happen if a quantifiers-specific call (e.g.
   * getInstantiatedQuantifiedFormulas) is called in a non-quantified logic.
   *
   * @param c used for giving an error message to indicate the context
   * this method was called.
   */
  theory::QuantifiersEngine* getAvailableQuantifiersEngine(const char* c) const;

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
  void debugCheckFormals(const std::vector<Node>& formals, Node func);

  /**
   * Checks whether formula is a valid function body for func whose formal
   * argument list is stored in formals. This method is
   * used as a helper function when defining (recursive) functions.
   */
  void debugCheckFunctionBody(Node formula,
                              const std::vector<Node>& formals,
                              Node func);

  /**
   * Helper method to obtain both the heap and nil from the solver. Returns a
   * std::pair where the first element is the heap expression and the second
   * element is the nil expression.
   */
  std::pair<Node, Node> getSepHeapAndNilExpr();

  /* Members -------------------------------------------------------------- */

  /** Solver instance that owns this SmtEngine instance. */
  api::Solver* d_solver = nullptr;

  /**
   * The environment object, which contains all utilities that are globally
   * available to internal code.
   */
  std::unique_ptr<Env> d_env;
  /**
   * The state of this SmtEngine, which is responsible for maintaining which
   * SMT mode we are in, the contexts, the last result, etc.
   */
  std::unique_ptr<smt::SmtEngineState> d_state;

  /** Abstract values */
  std::unique_ptr<smt::AbstractValues> d_absValues;
  /** Assertions manager */
  std::unique_ptr<smt::Assertions> d_asserts;
  /** Resource out listener */
  std::unique_ptr<smt::ResourceOutListener> d_routListener;
  /** Node manager listener */
  std::unique_ptr<smt::SmtNodeManagerListener> d_snmListener;

  /** The SMT solver */
  std::unique_ptr<smt::SmtSolver> d_smtSolver;

  /**
   * The SMT-level model object, which contains information about how to
   * print the model, as well as a pointer to the underlying TheoryModel
   * implementation maintained by the SmtSolver.
   */
  std::unique_ptr<smt::Model> d_model;

  /**
   * The utility used for checking models
   */
  std::unique_ptr<smt::CheckModels> d_checkModels;

  /**
   * The proof manager, which manages all things related to checking,
   * processing, and printing proofs.
   */
  std::unique_ptr<smt::PfManager> d_pfManager;

  /**
   * The unsat core manager, which produces unsat cores and related information
   * from refutations. */
  std::unique_ptr<smt::UnsatCoreManager> d_ucManager;

  /** The solver for sygus queries */
  std::unique_ptr<smt::SygusSolver> d_sygusSolver;

  /** The solver for abduction queries */
  std::unique_ptr<smt::AbductionSolver> d_abductSolver;
  /** The solver for interpolation queries */
  std::unique_ptr<smt::InterpolationSolver> d_interpolSolver;
  /** The solver for quantifier elimination queries */
  std::unique_ptr<smt::QuantElimSolver> d_quantElimSolver;

  /**
   * The logic set by the user. The actual logic, which may extend the user's
   * logic, lives in the Env class.
   */
  LogicInfo d_userLogic;

  /** Whether this is an internal subsolver. */
  bool d_isInternalSubsolver;

  /**
   * Verbosity of various commands.
   */
  std::map<std::string, int> d_commandVerbosity;

  /** The statistics class */
  std::unique_ptr<smt::SmtEngineStatistics> d_stats;

  /** the output manager for commands */
  mutable OutputManager d_outMgr;
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

}  // namespace cvc5

#endif /* CVC5__SMT_ENGINE_H */
