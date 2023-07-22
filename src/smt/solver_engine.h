/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SolverEngine: the main public entry point of libcvc5.
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT__SOLVER_ENGINE_H
#define CVC5__SMT__SOLVER_ENGINE_H

#include <cvc5/cvc5_export.h>

#include <map>
#include <memory>
#include <string>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap_forward.h"
#include "options/options.h"
#include "smt/smt_mode.h"
#include "theory/logic_info.h"
#include "util/result.h"
#include "util/synth_result.h"

namespace cvc5 {

class Solver;

namespace internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
typedef NodeTemplate<false> TNode;
class TypeNode;

class Env;
class UnsatCore;
class StatisticsRegistry;
class Printer;
class ResourceManager;
struct InstantiationList;

/* -------------------------------------------------------------------------- */

namespace smt {
/** Utilities */
class ContextManager;
class SolverEngineState;
class ResourceOutListener;
class CheckModels;
/** Subsolvers */
class SmtSolver;
class SmtDriver;
class SygusSolver;
class AbductionSolver;
class InterpolationSolver;
class QuantElimSolver;
class FindSynthSolver;

struct SolverEngineStatistics;
class PfManager;
class UnsatCoreManager;

}  // namespace smt

/* -------------------------------------------------------------------------- */

namespace theory {
class TheoryModel;
class QuantifiersEngine;
}  // namespace theory

/* -------------------------------------------------------------------------- */

class CVC5_EXPORT SolverEngine
{
  friend class cvc5::Solver;

  /* .......................................................................  */
 public:
  /* .......................................................................  */

  /**
   * Construct an SolverEngine with the given expression manager.
   * If provided, optr is a pointer to a set of options that should initialize
   * the values of the options object owned by this class.
   */
  SolverEngine(const Options* optr = nullptr);
  /** Destruct the SMT engine.  */
  ~SolverEngine();

  //--------------------------------------------- concerning the state

  /**
   * This is the main initialization procedure of the SolverEngine.
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
   * use of the SolverEngine; e.g. when the first formula is asserted, a call
   * to simplify() is issued, a scope is pushed, etc.
   */
  void finishInit();
  /**
   * Return true if this SolverEngine is fully initialized (post-construction)
   * by the above call.
   */
  bool isFullyInited() const;
  /**
   * Return true if a checkSatisfiability() has been made.
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
   * Returns the most recent result of checkSat or
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
   * This function is called on SolverEngine objects that are created
   * internally.  It is used to mark that this SolverEngine should not
   * perform preprocessing passes that rephrase the input, such as
   * --sygus-rr-synth-input or
   * --sygus-abduct.
   */
  void setIsInternalSubsolver();
  /** Is this an internal subsolver? */
  bool isInternalSubsolver() const;

  /**
   * Block the current model. Can be called only if immediately preceded by
   * a SAT or INVALID query. Only permitted if produce-models is on, and the
   * block-models option is set to a mode other than "none".
   *
   * This adds an assertion to the assertion stack that blocks the current
   * model based on the current options configured by cvc5.
   */
  void blockModel(modes::BlockModelsMode mode);

  /**
   * Block the current model values of (at least) the values in exprs. Can be
   * called only if immediately preceded by a SAT query. Only permitted if
   * produce-models is on, and the block-models option is set to a mode other
   * than "none".
   *
   * This adds an assertion to the assertion stack of the form:
   *  (or (not (= exprs[0] M0)) ... (not (= exprs[n] Mn)))
   * where M0 ... Mn are the current model values of exprs[0] ... exprs[n].
   */
  void blockModelValues(const std::vector<Node>& exprs);

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
   * Get the list of top-level learned literals that are entailed by the current
   * set of assertions.
   */
  std::vector<Node> getLearnedLiterals(modes::LearnedLitType t);

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
  /** Same as above, with lambda */
  void defineFunction(Node func, Node lambda, bool global = false);

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
   * literals and conjunction of literals. Note this formula will
   * be included in the unsat core when applicable.
   *
   * @throw TypeCheckingException, LogicException
   */
  void assertFormula(const Node& formula);

  /**
   * Assert a formula (if provided) to the current context and call
   * check().  Returns SAT, UNSAT, or UNKNOWN result.
   *
   * @throw Exception
   */
  Result checkSat();
  Result checkSat(const Node& assumption);
  Result checkSat(const std::vector<Node>& assumptions);

  /**
   * Get a timeout core, which computes a subset of the current assertions that
   * cause a timeout. Note it does not require being proceeded by a call to
   * checkSat.
   *
   * @return The result of the timeout core computation. This is a pair
   * containing a result and a list of formulas. If the result is unknown
   * and the reason is timeout, then the list of formulas correspond to a
   * subset of the current assertions that cause a timeout in the specified
   * time. If the result is unsat, then the list of formulas correspond to an
   * unsat core for the current assertions. Otherwise, the result is sat,
   * indicating that the current assertions are satisfiable, and
   * the list of formulas is empty.
   */
  std::pair<Result, std::vector<Node>> getTimeoutCore();
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

  /**
   * Add a regular sygus constraint or assumption.
   * @param n The formula
   * @param isAssume True if n is an assumption.
   */
  void assertSygusConstraint(Node n, bool isAssume = false);

  /** @return sygus constraints .*/
  std::vector<Node> getSygusConstraints();

  /** @return sygus assumptions .*/
  std::vector<Node> getSygusAssumptions();

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
   * @param isNext Whether we are asking for the next synthesis solution (if
   * using incremental).
   *
   * @throw Exception
   */
  SynthResult checkSynth(bool isNext = false);
  /**
   * Find synth for the given target and grammar.
   */
  Node findSynth(modes::FindSynthTarget fst, const TypeNode& gtn);
  /**
   * Find synth for the given target and grammar.
   */
  Node findSynthNext();

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
   * Add an oracle function to the state, also adds an oracle interface
   * defining it.
   *
   * @param var The oracle function symbol
   * @param fn The method for the oracle
   */
  void declareOracleFun(
      Node var, std::function<std::vector<Node>(const std::vector<Node>&)> fn);
  /**
   * Simplify a formula without doing "much" work.  Does not involve
   * the SAT Engine in the simplification, but uses the current
   * definitions, assertions, and the current partial model, if one
   * has been constructed.  It also involves theory normalization.
   *
   * @throw TypeCheckingException, LogicException
   *
   * @todo (design) is this meant to give an equivalent or an
   * equisatisfiable formula?
   */
  Node simplify(const Node& e);

  /**
   * Get the assigned value of an expr (only if immediately preceded by a SAT
   * query). Only permitted if the SolverEngine is set to operate interactively
   * and produce-models is on.
   *
   * @throw ModalException, TypeCheckingException, LogicException
   */
  Node getValue(const Node& e) const;

  /**
   * Same as getValue but for a vector of expressions
   */
  std::vector<Node> getValues(const std::vector<Node>& exprs) const;

  /**
   * @return the domain elements for uninterpreted sort tn.
   */
  std::vector<Node> getModelDomainElements(TypeNode tn) const;

  /**
   * @return true if v is a model core symbol
   */
  bool isModelCoreSymbol(Node v);

  /**
   * Get a model (only if immediately preceded by an SAT or unknown query).
   * Only permitted if the model option is on.
   *
   * @param declaredSorts The sorts to print in the model
   * @param declaredFuns The free constants to print in the model. A subset
   * of these may be printed based on isModelCoreSymbol.
   * @return the string corresponding to the model. If the output language is
   * smt2, then this corresponds to a response to the get-model command.
   */
  std::string getModel(const std::vector<TypeNode>& declaredSorts,
                       const std::vector<Node>& declaredFuns);

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
   * Same as above, but used for getting synthesis solutions from a "subsolver"
   * that has been initialized to assert the synthesis conjecture as a
   * normal assertion.
   *
   * This method returns true if we are in a state immediately preceded by
   * a successful call to checkSat, where this SolverEngine has an asserted
   * synthesis conjecture.
   */
  bool getSubsolverSynthSolutions(std::map<Node, Node>& solMap);

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
   * the current set of formulas A asserted to this SolverEngine :
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
   */
  Node getQuantifierElimination(Node q, bool doFull);

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
  Node getInterpolant(const Node& conj, const TypeNode& grammarType);

  /**
   * Get next interpolant. This can only be called immediately after a
   * successful call to getInterpolant or getInterpolantNext.
   *
   * Returns the interpolant if one exists, or the null node otherwise.
   */
  Node getInterpolantNext();

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
  Node getAbduct(const Node& conj, const TypeNode& grammarType);

  /**
   * Get next abduct. This can only be called immediately after a successful
   * call to getAbduct or getAbductNext.
   *
   * Returns the abduct if one exists, or the null node otherwise.
   */
  Node getAbductNext();

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
   * Adds the skolemizations and instantiations that were relevant
   * for the refutation.
   * @param insts The relevant instantiations
   * @param sks The relevant skolemizations
   * @param getDebugInfo If true, we add identifiers on instantiations that
   * indicate their source (the strategy that invoked them)
   */
  void getRelevantQuantTermVectors(std::map<Node, InstantiationList>& insts,
                                   std::map<Node, std::vector<Node>>& sks,
                                   bool getDebugInfo = false);
  /**
   * Get instantiation term vectors, which maps each instantiated quantified
   * formula to the list of instantiations for that quantified formula. This
   * list is minimized if proofs are enabled, and this call is immediately
   * preceded by an UNSAT query.
   */
  void getInstantiationTermVectors(
      std::map<Node, std::vector<std::vector<Node>>>& insts);

  /**
   * Get an unsatisfiable core (only if immediately preceded by an UNSAT
   * query). Only permitted if cvc5 was built with unsat-core support and
   * produce-unsat-cores is on.
   */
  UnsatCore getUnsatCore();

  /**
   * Get a refutation proof (only if immediately preceded by an UNSAT query).
   * Only permitted if cvc5 was built with proof support and the proof option
   * is on.
   */
  std::string getProof(modes::ProofComponent c = modes::PROOF_COMPONENT_FULL);

  /**
   * Get the current set of assertions.  Only permitted if the
   * SolverEngine is set to operate interactively.
   */
  std::vector<Node> getAssertions();

  /**
   * Get difficulty map, which populates dmap, mapping input assertions
   * to a value that estimates their difficulty for solving the current problem.
   */
  void getDifficultyMap(std::map<Node, Node>& dmap);

  /**
   * Push a user-level context.
   * throw@ ModalException, LogicException
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
   * or from a signal handler.  Throws a ModalException if the SolverEngine
   * isn't currently in a query.
   *
   * @throw ModalException
   */
  void interrupt();

  /**
   * Set a resource limit for SolverEngine operations.  This is like a time
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
   * addition to resource limits; the SolverEngine obeys both.  That means
   * that up to four independent limits can control the SolverEngine
   * at the same time.
   *
   * When an SolverEngine is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the SolverEngine to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param units the resource limit, or 0 for no limit
   * @param cumulative whether this resource limit is to be a cumulative
   * resource limit for all remaining calls into the SolverEngine (true), or
   * whether it's a per-call resource limit (false); the default is false
   */
  void setResourceLimit(uint64_t units, bool cumulative = false);

  /**
   * Set a per-call time limit for SolverEngine operations.
   *
   * A per-call time limit can be set at the same time and replaces
   * any per-call time limit currently in effect.
   * Resource limits (either per-call or cumulative) can be set in
   * addition to a time limit; the SolverEngine obeys all three of them.
   *
   * Note that the per-call timer only ticks away when one of the
   * SolverEngine's workhorse functions (things like assertFormula(),
   * checkSat(), and simplify()) are running.
   * Between calls, the timer is still.
   *
   * When an SolverEngine is first created, it has no time or resource
   * limits.
   *
   * Currently, these limits only cause the SolverEngine to stop what its
   * doing when the limit expires (or very shortly thereafter); no
   * heuristics are altered by the limits or the threat of them expiring.
   * We reserve the right to change this in the future.
   *
   * @param millis the time limit in milliseconds, or 0 for no limit
   */
  void setTimeLimit(uint64_t millis);

  /**
   * Get the current resource usage count for this SolverEngine.  This
   * function can be used to ascertain reasonable values to pass as
   * resource limits to setResourceLimit().
   */
  unsigned long getResourceUsage() const;

  /** Get the current millisecond count for this SolverEngine.  */
  unsigned long getTimeUsage() const;

  /**
   * Get the remaining resources that can be consumed by this SolverEngine
   * according to the currently-set cumulative resource limit.  If there
   * is not a cumulative resource limit set, this function throws a
   * ModalException.
   *
   * @throw ModalException
   */
  unsigned long getResourceRemaining() const;

  /**
   * Print statistics from the statistics registry in the env object owned by
   * this SolverEngine. Safe to use in a signal handler.
   */
  void printStatisticsSafe(int fd) const;

  /**
   * Print the changes to the statistics from the statistics registry in the
   * env object owned by this SolverEngine since this method was called the last
   * time. Internally prints the diff and then stores a snapshot for the next
   * call.
   */
  void printStatisticsDiff() const;

  /** Get the options object (const and non-const versions) */
  Options& getOptions();
  const Options& getOptions() const;

  /** Get the resource manager of this SMT engine */
  ResourceManager* getResourceManager() const;

  /**
   * Get substituted assertions.
   *
   * Return the set of assertions, after applying top-level substitutions.
   */
  std::vector<Node> getSubstitutedAssertions();

  /**
   * Get the enviornment from this solver engine.
   */
  Env& getEnv();
  /* .......................................................................  */
 private:
  /* .......................................................................  */

  // disallow copy/assignment
  SolverEngine(const SolverEngine&) = delete;
  SolverEngine& operator=(const SolverEngine&) = delete;

  /**
   * Begin call, which is called before any method that requires initializing
   * this solver engine and make the state of the internal solver current.
   *
   * In particular, this ensures the solver is initialized, the pending pops
   * on the context are processed, and optionally calls the resource manager
   * to reset its limits (ResourceManager::beginCall).
   *
   * @param needsRLlimit If true, then beginCall() is called on the resource
   * manager maintained by this class.
   */
  void beginCall(bool needsRLlimit = false);
  /**
   * End call. Should follow after a call to beginCall where needsRLlimit
   * was true.
   */
  void endCall();

  /** Set solver instance that owns this SolverEngine. */
  void setSolver(cvc5::Solver* solver) { d_solver = solver; }

  /** Get a pointer to the (new) PfManager owned by this SolverEngine. */
  smt::PfManager* getPfManager() { return d_pfManager.get(); };

  /** Get a pointer to the StatisticsRegistry owned by this SolverEngine. */
  StatisticsRegistry& getStatisticsRegistry();

  /**
   * Internal method to get an unsatisfiable core (only if immediately preceded
   * by an UNSAT query). Only permitted if cvc5 was built with unsat-core
   * support and produce-unsat-cores is on. Does not dump the command.
   *
   * @param isInternal Whether this call was made internally (not by the user).
   * This impacts whether the unsat core is post-processed.
   */
  UnsatCore getUnsatCoreInternal(bool isInternal = true);

  /** Internal version of assertFormula */
  void assertFormulaInternal(const Node& formula);

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
  theory::TheoryModel* getAvailableModel(const char* c) const;
  /**
   * Get available quantifiers engine, which throws a modal exception if it
   * does not exist. This can happen if a quantifiers-specific call (e.g.
   * getInstantiatedQuantifiedFormulas) is called in a non-quantified logic.
   *
   * @param c used for giving an error message to indicate the context
   * this method was called.
   */
  theory::QuantifiersEngine* getAvailableQuantifiersEngine(const char* c) const;

  /**
   * Internally handle the setting of a logic.  This function should always
   * be called when d_logic is updated.
   */
  void setLogicInternal();

  /*
   * Check satisfiability (used to check satisfiability and entailment).
   */
  Result checkSatInternal(const std::vector<Node>& assumptions);

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
  /**
   * Get assertions internal, which is only called after initialization. This
   * should be used internally to get the assertions instead of getAssertions
   * or getExpandedAssertions, which may trigger initialization and SMT state
   * changes.
   */
  std::vector<Node> getAssertionsInternal() const;

  /**
   * Return a reference to options like for `EnvObj`.
   */
  const Options& options() const;

  /**
   * Check that the given term is a valid closed term, which can be used as an
   * argument to, e.g., assert, get-value, block-model-values, etc.
   *
   * @param n The node to check
   * @param src The source of the check, which is printed in the exception if
   * this check fails.
   */
  void ensureWellFormedTerm(const Node& n, const std::string& src) const;
  /** Vector version of above. */
  void ensureWellFormedTerms(const std::vector<Node>& ns,
                             const std::string& src) const;
  /**
   * Convert preprocessed assertions to the input formulas that imply them. In
   * detail, this converts a set of preprocessed assertions to a set of input
   * assertions based on the proof of preprocessing. It is used for unsat cores
   * and timeout cores.
   *
   * @param ppa The preprocessed assertions to convert
   * @param isInternal Used for debug printing unsat cores, i.e. when isInternal
   * is false, we print debug information.
   */
  std::vector<Node> convertPreprocessedToInput(const std::vector<Node>& ppa,
                                               bool isInternal);
  /* Members -------------------------------------------------------------- */

  /** Solver instance that owns this SolverEngine instance. */
  cvc5::Solver* d_solver = nullptr;

  /**
   * The environment object, which contains all utilities that are globally
   * available to internal code.
   */
  std::unique_ptr<Env> d_env;
  /**
   * The state of this SolverEngine, which is responsible for maintaining which
   * SMT mode we are in, the last result, etc.
   */
  std::unique_ptr<smt::SolverEngineState> d_state;
  /**
   * The context manager of this SolverEngine, which is responsible for
   * maintaining which the contexts.
   */
  std::unique_ptr<smt::ContextManager> d_ctxManager;

  /** Resource out listener */
  std::unique_ptr<smt::ResourceOutListener> d_routListener;

  /** The SMT solver */
  std::unique_ptr<smt::SmtSolver> d_smtSolver;
  /** The SMT solver driver */
  std::unique_ptr<smt::SmtDriver> d_smtDriver;

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
  /** The solver for find-synth queries */
  std::unique_ptr<smt::FindSynthSolver> d_findSynthSolver;

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

  /** The statistics class */
  std::unique_ptr<smt::SolverEngineStatistics> d_stats;
}; /* class SolverEngine */

/* -------------------------------------------------------------------------- */

}  // namespace internal
}  // namespace cvc5

#endif /* CVC5__SMT_ENGINE_H */
