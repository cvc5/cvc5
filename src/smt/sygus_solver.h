/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for SyGuS queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SYGUS_SOLVER_H
#define CVC5__SMT__SYGUS_SOLVER_H

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"
#include "util/synth_result.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

class SmtSolver;

/**
 * A solver for sygus queries.
 *
 * This class is responsible for responding to check-synth commands. It calls
 * check satisfiability using a separate SolverEngine "subsolver".
 *
 * This solver operates in two modes.
 *
 * If in incremental mode, then the "main" SolverEngine for SyGuS inputs only
 * maintains a (user-context) dependent state of SyGuS assertions, as well as
 * assertions corresponding to (recursive) function definitions. The subsolver
 * that solves SyGuS conjectures may be called to checkSat multiple times,
 * however, push/pop (which impact SyGuS constraints) impacts only the main
 * solver. This means that the conjecture being handled by the subsolver is
 * reconstructed when the SyGuS conjecture is updated. The key property that
 * this enables is that the subsolver does *not* get calls to push/pop,
 * although it may receive multiple check-sat if the sygus functions and
 * constraints are not updated between check-sat calls.
 *
 * If not in incremental mode, then the internal SyGuS conjecture is asserted
 * to the "main" SolverEngine.
 */
class SygusSolver : protected EnvObj
{
  using NodeList = context::CDList<Node>;

 public:
  SygusSolver(Env& env, SmtSolver& sms);
  ~SygusSolver();

  /**
   * Add variable declaration.
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
  void declareSynthFun(Node func,
                       TypeNode type,
                       bool isInv,
                       const std::vector<Node>& vars);

  /** Add a regular sygus constraint or assumption.*/
  void assertSygusConstraint(Node n, bool isAssume);

  /** @return sygus constraints .*/
  std::vector<Node> getSygusConstraints() const;

  /** @return sygus assumptions .*/
  std::vector<Node> getSygusAssumptions() const;

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
   */
  SynthResult checkSynth(bool isNext);
  /**
   * Get synth solution.
   *
   * This method returns true if we are in a state immediately preceded by
   * a successful call to checkSynth.
   *
   * This method adds entries to sol_map that map functions-to-synthesize with
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
  bool getSynthSolutions(std::map<Node, Node>& sol_map);
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
   * Returns true if we can trust the results of synthesis solutions for
   * solvers that use the given options. This is false e.g. if we are using an
   * approximate checking algorithm for solution correctness.
   */
  static bool canTrustSynthesisResult(const Options& opts);
  /**
   * Get the list of synthesis functions in the current context, each paired
   * with their corresponding grammar (if one exists).
   */
  std::vector<std::pair<Node, TypeNode>> getSynthFunctions() const;

 private:
  /**
   * Check that a solution to a synthesis conjecture is indeed a solution.
   *
   * The check is made by determining if the negation of the synthesis
   * conjecture in which the functions-to-synthesize have been replaced by the
   * synthesized solutions, which is a quantifier-free formula, is
   * unsatisfiable. If not, then the found solutions are wrong.
   *
   * @param as The background assertions, which may include define-fun and
   * define-fun-rec,
   * @param sol_map Map from functions-to-synthesize to their solution (of the
   * same type) for the asserted synthesis conjecture.
   */
  void checkSynthSolution(Assertions& as, const std::map<Node, Node>& solMap);
  /**
   * Expand definitions in sygus datatype tn, which ensures that all
   * sygus constructors that are used to build values of sygus datatype
   * tn are associated with their expanded definition form.
   *
   * This method is required at this level since sygus grammars may include
   * user-defined functions. Thus, we must use the preprocessor here to
   * associate the use of those functions with their expanded form, since
   * the internal sygus solver must reason about sygus operators after
   * expansion.
   */
  void expandDefinitionsSygusDt(TypeNode tn) const;
  /** List to vector helper */
  static std::vector<Node> listToVector(const NodeList& list);
  /**
   * Initialize SyGuS subsolver based on the assertions from the "main" solver.
   * This is used for check-synth using a subsolver, and for check-synth-sol.
   * This constructs a subsolver se, and makes calls to add all define-fun
   * and auxilary assertions.
   */
  void initializeSygusSubsolver(std::unique_ptr<SolverEngine>& se,
                                Assertions& as);
  /** Are we using a subsolver for the SyGuS query? */
  bool usingSygusSubsolver() const;
  /** The SMT solver. */
  SmtSolver& d_smtSolver;
  /**
   * sygus variables declared (from "declare-var" and "declare-fun" commands)
   *
   * The SyGuS semantics for declared variables is that they are implicitly
   * universally quantified in the constraints.
   */
  NodeList d_sygusVars;
  /** sygus constraints */
  NodeList d_sygusConstraints;
  /** sygus assumptions */
  NodeList d_sygusAssumps;
  /** functions-to-synthesize */
  NodeList d_sygusFunSymbols;
  /** The current sygus conjecture */
  Node d_conj;
  /**
   * Whether we need to reconstruct the sygus conjecture.
   *
   * The sygus conjecture is stale if either:
   * (1) no sygus conjecture has been added as an assertion to this SMT engine,
   * (2) there is a sygus conjecture that has been added as an assertion
   * internally to this SMT engine, and there have been further calls such that
   * the asserted conjecture is no longer up-to-date.
   *
   * This flag should be set to true when new sygus constraints are asserted and
   * when functions-to-synthesize are declared.
   */
  context::CDO<bool> d_sygusConjectureStale;
  /**
   * The (context-dependent) pointer to the subsolver we have constructed.
   * This is used to verify if the current subsolver is current, in case
   * user-context dependent pop has a occurred. If this pointer does not match
   * d_subsolver, then d_subsolver must be reconstructed in this context.
   */
  context::CDO<SolverEngine*> d_subsolverCd;
  /**
   * The subsolver we are using. This is a separate copy of the SolverEngine
   * which has the asserted synthesis conjecture, i.e. a formula returned by
   * quantifiers::SygusUtils::mkSygusConjecture.
   */
  std::unique_ptr<SolverEngine> d_subsolver;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__SYGUS_SOLVER_H */
