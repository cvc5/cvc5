/*********************                                                        */
/*! \file sygus_interpol.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus interpolation utility, which transforms an input of axioms and
 ** conjecture into an interpolation problem, and solve it.
 **/

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H

#include <string>
#include <vector>

#include "expr/node.h"
#include "expr/type.h"
#include "smt/smt_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
/**
 * This is an utility for the SMT-LIB command (get-interpol <term>).
 * The utility turns a set of quantifier-free assertions into a sygus
 * conjecture that encodes an interpolation problem, and then solve the
 * interpolation problem by synthesizing it. In detail, if our input formula is
 * F( x ) for free symbol x, and is partitioned into axioms Fa and conjecture Fc
 * then the sygus conjecture we construct is:
 *
 * exists A. forall x. ( (Fa( x ) => A( x )) ^ (A( x ) => Fc( x )) )
 *
 * where A( x ) is a predicate over the free symbols of our input that are
 * shared between Fa and Fc. In other words, A( x ) must be implied by our
 * axioms Fa( x ) and implies Fc( x ). Then, to solve the interpolation problem,
 * we just need to synthesis A( x ).
 */
class SygusInterpol
{
 public:
  SygusInterpol();

  SygusInterpol(LogicInfo logic);

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
  bool SolveInterpolation(const std::string& name,
                          const std::vector<Node>& axioms,
                          const Node& conj,
                          const TypeNode& itpGType,
                          Expr& interpol);

 private:
  /**
   * Collects symbols from axioms (axioms) and conjecture (conj), which are
   * stored in d_syms, and computes the shared symbols between axioms and
   * conjecture, stored in d_symsShared.
   *
   * @param axioms the assertions (Fa above)
   * @param conj the conjecture (Fc above)
   */
  void collectSymbols(const std::vector<Node>& axioms, const Node& conj);

  /**
   * Creates free variables and shared free variables from d_syms and
   * d_symsShared, which are stored in d_vars and d_varsShared. And also creates
   * the corresponding set of variables for the formal argument list, which is
   * stored in d_vlvs and d_vlvsShared. Extracts the types of shared variables,
   * which are stored in d_varTypesShared. Creates the formal argument list of
   * the interpol-to-synthesis, stored in d_ibvlShared.
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
   * Set up the grammar for the interpol-to-synthesis.
   *
   * The user-defined grammar will be encoded by itpGType. The options for
   * grammar is given by options::produceInterpols(). In DEFAULT option, it will
   * set up the grammar from itpGType. And if itpGType is null, it will set up
   * the default grammar. In ASSUMPTIONS option, it will set up the grammar by
   * only using the operators from axioms. In CONJECTURE option, it will set up
   * the grammar by only using the operators from conj. In SHARED option, it
   * will set up the grammar by only using the operators shared by axioms and
   * conj. In ALL option, it will set up the grammar by only using the operators
   * from either axioms or conj.
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
  bool findInterpol(Expr& interpol, Node itp);

  /** The SMT engine subSolver
   *
   * This is a fresh copy of the SMT engine which is used for solving the
   * interpolation problem. In particular, consider the input: (assert A)
   *   (get-interpol s B)
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
  std::unique_ptr<SmtEngine> d_subSolver;

  /**
   * The logic for the local copy of SMT engine (d_subSolver).
   */
  LogicInfo d_logic;

  /**
   * symbols from axioms and conjecture.
   */
  std::vector<Node> d_syms;
  /**
   * shared symbols between axioms and conjecture.
   */
  std::vector<Node> d_symsShared;
  /**
   * free variables created from d_syms.
   */
  std::vector<Node> d_vars;
  /**
   * variables created from d_syms for formal argument list.
   */
  std::vector<Node> d_vlvs;
  /**
   * free variables created from d_symsShared.
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
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H */
