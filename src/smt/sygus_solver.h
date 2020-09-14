/*********************                                                        */
/*! \file sygus_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for sygus queries
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__SYGUS_SOLVER_H
#define CVC4__SMT__SYGUS_SOLVER_H

#include "context/cdo.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/assertions.h"
#include "util/result.h"

namespace CVC4 {
namespace smt {

class Preprocessor;
class SmtSolver;

/**
 * A solver for sygus queries.
 *
 * This class is responsible for responding to check-synth commands. It calls
 * check satisfiability using an underlying SmtSolver object.
 *
 * It also maintains a reference to a preprocessor for implementing
 * checkSynthSolution.
 */
class SygusSolver
{
 public:
  SygusSolver(SmtSolver& sms, Preprocessor& pp, context::UserContext* u);
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
   */
  Result checkSynth(Assertions& as);
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

 private:
  /**
   * Check that a solution to a synthesis conjecture is indeed a solution.
   *
   * The check is made by determining if the negation of the synthesis
   * conjecture in which the functions-to-synthesize have been replaced by the
   * synthesized solutions, which is a quantifier-free formula, is
   * unsatisfiable. If not, then the found solutions are wrong.
   */
  void checkSynthSolution(Assertions& as);
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
  /** The SMT solver, which is used during checkSynth. */
  SmtSolver& d_smtSolver;
  /** The preprocessor, used for checkSynthSolution. */
  Preprocessor& d_pp;
  /**
   * sygus variables declared (from "declare-var" and "declare-fun" commands)
   *
   * The SyGuS semantics for declared variables is that they are implicitly
   * universally quantified in the constraints.
   */
  std::vector<Node> d_sygusVars;
  /** sygus constraints */
  std::vector<Node> d_sygusConstraints;
  /** functions-to-synthesize */
  std::vector<Node> d_sygusFunSymbols;
  /**
   * Whether we need to reconstruct the sygus conjecture.
   */
  context::CDO<bool> d_sygusConjectureStale;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__SYGUS_SOLVER_H */
