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
 ** \brief Sygus interpolation utility, which transforms an arbitrary input into
 ** an interpolation problem.
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
 * A utility that turns a set of quantifier-free assertions into
 * a sygus conjecture that encodes an interpolation problem. In detail, if our
 * input formula is F( x ) for free symbols x, and is partitioned into axioms Fa
 * and conjecture Fc then the sygus conjecture we construct is:
 *
 * exists A. forall x. ( (Fa( x ) => A( x )) ^ (A( x ) => Fc( x )) )
 *
 * where A( x ) is a predicate over the free symbols of our input that are
 * shared between Fa and Fc. In other words, A( x ) must be implied by our
 * axioms Fa and implies Fc( x ).
 */
class SygusInterpol
{
 public:
  SygusInterpol();

  SygusInterpol(LogicInfo logic);

  /**
   * Returns the sygus conjecture corresponding to the interpolation problem for
   * input problem (F above) given by axioms (Fa above), and conj (Fc above).
   *  Note that axioms is expected to be a subset of asserts.
   *
   * The argument name is the name for the interpol-to-synthesize.
   *
   * The type itpGType (if non-null) is a sygus datatype type that encodes the
   * grammar that should be used for solutions of the interpolation conjecture.
   *
   * The output argument interpol is the solution to the synthesis conjector.
   *
   * The relationship between the free variables of asserts and the formal
   * argument list of the interpol-to-synthesize are tracked by the attribute
   * SygusVarToTermAttribute.
   *
   * In particular, solutions to the synthesis conjecture will be in the form
   * of a closed term (lambda varlist. t). The intended solution, which is a
   * term whose free variables are a subset of asserts, is the term
   * t * { varlist -> SygusVarToTermAttribute(varlist) }.
   */
  bool SolveInterpolation(const std::string& name,
                          const std::vector<Node>& axioms,
                          const Node& conj,
                          const TypeNode& itpGType,
                          Expr& interpol);

 private:
  /**
   * Collects symbols from axioms (axioms) and conjecture (conj), which stored
   * in d_syms. And computes the shared symbols between axioms and conjecture,
   * stored in d_symsShared.
   */
  void collectSymbols(const std::vector<Node>& axioms, const Node& conj);

  /**
   * Creates free variables and shared free variables from d_syms and
   * d_symsShared, which stored in d_vars and d_varsShared. And also creates the
   * same set of variables for formal argument list, which stored in d_vlvs and
   * d_vlvsShared. Extracts the types of shared variables, which stored in
   * d_varTypesShared. Creates the formal argument list of the
   * interpol-to-synthesis, stored in d_abvlShared.
   *
   * The argument needsShared denotes if we want to restrict the argument list
   * of the interpol-to-synthesis to be over shared variables or not.
   */
  void createVariables(bool needsShared);

  /**
   * Set up the grammar for the interpol-to-synthesis.
   *
   * The user-defined grammar will be encoded by itpGType. In DEFAULT option, it
   * will set up the grammar from itpGType. And if itpGType is null, it will set
   * up the default grammar. In ASSUMPTIONS option, it will set up the grammar
   * by only using the operators from axioms. In CONCLUSION option, it will set
   * up the grammar by only using the operators from conj. In SHARED option, it
   * will set up the grammar by only using the operators shared by axioms and
   * conj. In ALL option, it will set up the grammar by only using the operators
   * from axioms or conj.
   */
  TypeNode setSynthGrammar(const TypeNode& itpGType,
                           const std::vector<Node>& axioms,
                           const Node& conj);

  /**
   * Make the interpolation predicate.
   *
   * The argument name is the name of the interpol-to-synthesis.
   */
  Node mkPredicate(const std::string& name);

  /**
   * Make the sygus conjecture to be synthesis.
   *
   * The argument itp is the interpolation predicate.
   */
  void mkSygusConjecture(Node itp,
                         const std::vector<Node>& axioms,
                         const Node& conj);

  /**
   * Get the synthesis solution, stored in interpol.
   *
   * The argument itp is the interpolation predicate.
   */
  bool findInterpol(Expr& interpol, Node itp);

  /** The SMT engine subsolver
   *
   * This is a fresh copy of the SMT engine which is used for making calls
   * especially for interpolation problem. In particular, consider the input:
   *   (assert A)
   *   (get-interpol s B)
   * In the copy of the SMT engine where these commands are issued, we maintain
   * A in the assertion stack. To solve the interpolation problem, instead of
   * modifying the assertion stack to remove A and add the sygus conjecture
   * (exists I. ...), we invoke a fresh copy of the SMT engine and leave the
   * assertion stack unchaged. This copy of the SMT engine can be further
   * queried for information regarding further solutions.
   */
  std::unique_ptr<SmtEngine> d_subsolver;

  // The logic for the local copy of SMT engine (d_subsolver).
  LogicInfo d_logic;

  // symbols from axioms and conjecture
  std::vector<Node> d_syms;
  // shared symbols between axioms and conjecture
  std::vector<Node> d_symsShared;
  // free variables created from d_syms
  std::vector<Node> d_vars;
  // variables created from d_syms for formal argument list
  std::vector<Node> d_vlvs;
  // free variables created from d_symsShared
  std::vector<Node> d_varsShared;
  // variables created from d_symShared for formal argument list
  std::vector<Node> d_vlvsShared;
  // types of shared variables between axioms and conjecture
  std::vector<TypeNode> d_varTypesShared;
  // formal argument list of the interpol-to-synthesis
  Node d_abvlShared;

  // the sygus conjecture to synthesis for interpolation problem
  Node d_sygusConj;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__SYGUS_INTERPOL_H */
