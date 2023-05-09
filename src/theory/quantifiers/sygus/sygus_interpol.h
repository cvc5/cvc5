/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus interpolation utility, which transforms an input of axioms and
 * conjecture into an interpolation problem, and solve it.
 */

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H

#include <string>
#include <vector>

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class Env;
class SolverEngine;

namespace theory {
namespace quantifiers {
/**
 * This is an utility for the SMT-LIB command (get-interpolant <term>).
 * The utility turns a set of quantifier-free assertions into a sygus
 * conjecture that encodes an interpolation problem, and then solve the
 * interpolation problem by synthesizing it. In detail, if our input formula is
 * F( x ) for free symbol x, and is partitioned into axioms Fa and conjecture Fc
 * then the sygus conjecture we construct is:
 *
 * (Fa( x ) => A( x )) ^ (A( x ) => Fc( x ))
 *
 * where A( x ) is a predicate over the free symbols of our input that are
 * shared between Fa and Fc. In other words, A( x ) must be implied by our
 * axioms Fa( x ) and implies Fc( x ). Then, to solve the interpolation problem,
 * we just need to synthesis A( x ).
 *
 * This class uses a fresh copy of the SMT engine which is used for solving the
 * interpolation problem. In particular, consider the input:
 *   (assert A)
 *   (get-interpolant s B)
 * In the copy of the SMT engine where these commands are issued, we maintain
 * A in the assertion stack. In solving the interpolation problem, we will
 * need to call a SMT engine solver with a different assertion stack, which is
 * a sygus conjecture build from A and B. Then to solve the interpolation
 * problem, instead of modifying the assertion stack to remove A and add the
 * sygus conjecture (exists I. ...), we invoke a fresh copy of the SMT engine
 * and leave the original assertion stack unchanged. This copy of the SMT
 * engine will have the assertion stack with the sygus conjecture. This copy
 * of the SMT engine can be further queried for information regarding further
 * solutions.
 */
class SygusInterpol : protected EnvObj
{
 public:
  SygusInterpol(Env& env);

  /**
   * Returns the sygus conjecture in interpol corresponding to the interpolation
   * problem for input problem (F above) given by axioms (Fa above), and conj
   * (Fc above). And solve the interpolation by sygus. Note that axioms is
   * expected to be a subset of assertions in SMT-LIB.
   *
   * @param name the name for the interpol-to-synthesize.
   * @param axioms the assertions (Fa above)
   * @param conj the conjecture (Fc above)
   * @param itpGType (if non-null) a sygus datatype type that encodes the
   * grammar that should be used for solutions of the interpolation conjecture.
   * @interpol the solution to the sygus conjecture.
   */
  bool solveInterpolation(const std::string& name,
                          const std::vector<Node>& axioms,
                          const Node& conj,
                          const TypeNode& itpGType,
                          Node& interpol);

  /**
   * Internal call for getting next interpolant. This can only be called after a
   * successful call to solveInterpolation. It solves the interpolation problem
   * constructed already and returns true if an interpolant was found, and sets
   * interpol to the interpolant.
   *
   * @interpol the solution to the sygus conjecture.
   */
  bool solveInterpolationNext(Node& interpol);

 private:
  /**
   * Collects symbols from axioms (axioms) and conjecture (conj), which are
   * stored in d_syms, and computes the shared symbols between axioms and
   * conjecture, stored in d_symSetShared.
   *
   * @param axioms the assertions (Fa above)
   * @param conj the conjecture (Fc above)
   */
  void collectSymbols(const std::vector<Node>& axioms, const Node& conj);

  /**
   * Creates free variables and shared free variables from d_syms and
   * d_symSetShared, which are stored in d_vars and d_varsShared. And also
   * creates the corresponding set of variables for the formal argument list,
   * which is stored in d_vlvs and d_vlvsShared. Extracts the types of shared
   * variables, which are stored in d_varTypesShared. Creates the formal
   * argument list of the interpol-to-synthese, stored in d_ibvlShared.
   *
   * When using default grammar, the needsShared is true. When using
   * user-defined gramar, the needsShared is false.
   *
   * @param needsShared If it is true, the argument list of the
   * interpol-to-synthesis will be restricted to be over shared variables. If it
   * is false, the argument list will be over all the variables.
   */
  void createVariables(bool needsShared);

  /**
   * Get include_cons for mkSygusDefaultType.
   * mkSygusDefaultType() is a function to make default grammar. It has an
   * arguemnt include_cons, which will restrict what operators we want in the
   * grammar. The return value depends on the produceInterpols option. In
   * ASSUMPTIONS option, it will return the operators from axioms. In CONJECTURE
   * option, it will return the operators from conj. In SHARED option, it will
   * return the oprators shared by axioms and conj. In ALL option, it will
   * return the operators from either axioms or conj.
   *
   * @param axioms input argument
   * @param conj input argument
   * @param result the return value
   */
  void getIncludeCons(const std::vector<Node>& axioms,
                      const Node& conj,
                      std::map<TypeNode, std::unordered_set<Node>>& result);

  /**
   * Set up the grammar for the interpol-to-synthesis.
   *
   * The user-defined grammar will be encoded by itpGType. The options for
   * grammar is given by the produceInterpols option. In DEFAULT option, it will
   * set up the grammar from itpGType. And if itpGType is null, it will set up
   * the default grammar, which is built according to a policy handled by
   * getIncludeCons().
   *
   * @param itpGType (if non-null) a sygus datatype type that encodes the
   * grammar that should be used for solutions of the interpolation conjecture.
   * @param axioms the assertions (Fa above)
   * @param conj the conjecture (Fc above)
   */
  TypeNode setSynthGrammar(const TypeNode& itpGType,
                           const std::vector<Node>& axioms,
                           const Node& conj);

  /**
   * Make the interpolation predicate.
   *
   * @param name the name of the interpol-to-synthesis.
   */
  Node mkPredicate(const std::string& name);

  /**
   * Make the sygus conjecture to be synthesis.
   * The conjecture body is Fa( x ) => A( x ) ^ A( x ) => Fc( x ) as described
   * above.
   *
   * @param itp the interpolation predicate.
   * @param axioms the assertions (Fa above)
   * @param conj the conjecture (Fc above)
   */
  void mkSygusConjecture(Node itp,
                         const std::vector<Node>& axioms,
                         const Node& conj);

  /**
   * Get the synthesis solution, stored in interpol.
   *
   * @param interpol the solution to the sygus conjecture.
   * @param itp the interpolation predicate.
   */
  bool findInterpol(SolverEngine* subsolver, Node& interpol, Node itp);
  /**
   * symbols from axioms and conjecture.
   */
  std::vector<Node> d_syms;
  /**
   * unordered set for shared symbols between axioms and conjecture.
   */
  std::unordered_set<Node> d_symSetShared;
  /**
   * free variables created from d_syms.
   */
  std::vector<Node> d_vars;
  /**
   * variables created from d_syms for formal argument list.
   */
  std::vector<Node> d_vlvs;
  /**
   * free variables created from d_symSetShared.
   */
  std::vector<Node> d_varsShared;
  /**
   * variables created from d_symShared for formal argument list.
   */
  std::vector<Node> d_vlvsShared;
  /**
   * types of shared variables between axioms and conjecture.
   */
  std::vector<TypeNode> d_varTypesShared;
  /**
   * formal argument list of the interpol-to-synthesis.
   */
  Node d_ibvlShared;

  /**
   * the sygus conjecture to synthesis for interpolation problem
   */
  Node d_sygusConj;
  /**
   * The predicate for interpolation in the subsolver, which we pass to
   * findInterpol above when the solving is successful.
   */
  Node d_itp;
  /** The subsolver to initialize */
  std::unique_ptr<SolverEngine> d_subSolver;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H */
