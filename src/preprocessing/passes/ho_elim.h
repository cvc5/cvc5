/*********************                                                        */
/*! \file ho_elim.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The HoElim preprocessing pass
 **
 ** Eliminates higher-order constraints.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H
#define __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/** Higher-order elimination.
 *
 * This preprocessing pass eliminates all occurrences of higher-order
 * constraints in the input, and replaces the entire input problem with
 * an equisatisfiable one. This is based on the following steps.
 *
 * [1] Eliminate all occurrences of lambdas via lambda lifting. This includes
 * lambdas with free variables that occur in quantifier bodies (see
 * documentation for eliminateLambdaComplete).
 *
 * [2] Eliminate all occurrences of partial applications and constraints
 * involving functions as first-class members. This is done by first
 * turning all function applications into an applicative encoding involving the
 * parametric binary operator @ (of kind HO_APPLY). Then we introduce:
 * - An uninterpreted sort U(T) for each function type T,
 * - A function H(f) of sort U(T1) x .. x U(Tn) -> U(T) for each function f
 * of sort T1 x ... x Tn -> T.
 * - A function App_{T1 x T2 ... x Tn -> T} of type
 *   U(T1 x T2 ... x Tn -> T) x U(T1) -> U(T2 ... x Tn -> T)
 * for each occurrence of @ applied to arguments of types T1 x T2 ... x Tn -> T
 * and T1.
 *
 * [3] Add additional axioms to ensure the correct interpretation of
 * the sorts U(...), and functions App_{...}. This includes:
 *
 * - The "extensionality" axiom for App_{...} terms, stating that functions
 * that behave the same according to App for all inputs must be equal:
 *   forall x : U(T1->T2), y : U(T1->T2).
 *      ( forall z : T1. App_{T1->T2}( x, z ) = App_{T1->T2}( y, z ) ) =>
 *        x = y
 *
 * - The "store" axiom, which effectively states that for all (encoded)
 * functions f, there exists a function g that behaves identically to f, except
 * that g for argument i is e:
 *   forall x : U(T1->T2), i : U(T1), e : U(T2).
 *     exists g : U(T1->T2).
 *       forall z: T1.
 *         App_{T1->T2}( g, z ) = ite( z = i, e, App_{T1->T2}( f, z ) ).
 *
 *
 * Based on options, this preprocessing pass may apply a subset o the above
 * steps. In particular:
 * * If options::hoElim() is true, then step [2] is taken and extensionality
 * axioms are added in step [3].
 * * If options::hoElimStoreAx() is true, then store axioms are added in step 3.
 * The form of these axioms depends on whether options::hoElim() is true. If it
 * is true, the axiom is given in terms of the uninterpreted functions that
 * encode function sorts. If it is false, then the store axiom is given in terms
 * of the original function sorts.
 */
class HoElim : public PreprocessingPass
{
 public:
  HoElim(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  /**
   * Eliminate all occurrences of lambdas in term n, return the result. This
   * is step [1] mentioned at the header of this class.
   *
   * The map newLambda maps newly introduced function skolems with their
   * (lambda) definition, which is a closed term.
   *
   * Notice that to ensure that all lambda definitions are closed, we
   * introduce extra bound arguments to the lambda, for example:
   *    forall x. (lambda y. x+y) != f
   * becomes
   *    forall x. g(x) != f
   * where g is mapped to the (closed) term ( lambda xy. x+y ).
   *
   * Notice that the definitions in newLambda may themselves contain lambdas,
   * hence, this method is run until a fix point is reached.
   */
  Node eliminateLambdaComplete(Node n, std::map<Node, Node>& newLambda);

  /**
   * Eliminate all higher-order constraints in n, return the result. This is
   * step [2] mentioned at the header of this class.
   */
  Node eliminateHo(Node n);
  /**
   * Stores the set of nodes we have current visited and their results
   * in steps [1] and [2] of this pass.
   */
  std::unordered_map<TNode, Node, TNodeHashFunction> d_visited;
  /**
   * Stores the mapping from functions f to their corresponding function H(f)
   * in the encoding for step [2] of this pass.
   */
  std::unordered_map<TNode, Node, TNodeHashFunction> d_visited_op;
  /** The set of all function types encountered in assertions. */
  std::unordered_set<TypeNode, TypeNodeHashFunction> d_funTypes;

  /**
   * Get ho apply uf, this returns App_{@_{T1 x T2 ... x Tn -> T}}
   */
  Node getHoApplyUf(TypeNode tn);
  /**
   * Get ho apply uf, where:
   *   tn is T1 x T2 ... x Tn -> T,
   *   tna is T1,
   *   tnr is T2 ... x Tn -> T
   * This returns App_{@_{T1 x T2 ... x Tn -> T}}.
   */
  Node getHoApplyUf(TypeNode tn, TypeNode tna, TypeNode tnr);
  /** cache of getHoApplyUf */
  std::map<TypeNode, Node> d_hoApplyUf;
  /**
   * Get uninterpreted sort for function sort. This returns U(T) for function
   * type T for step [2] of this pass.
   */
  TypeNode getUSort(TypeNode tn);
  /** cache of the above function */
  std::map<TypeNode, TypeNode> d_ftypeMap;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__HO_ELIM_PASS_H */
