/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Function definition processor for finite model finding.
 */

#ifndef CVC5__PREPROCESSING__PASSES__FUN_DEF_FMF_H
#define CVC5__PREPROCESSING__PASSES__FUN_DEF_FMF_H

#include <map>
#include <vector>

#include "context/cdlist.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * Preprocessing pass to allow finite model finding for admissible recursive
 * function definitions. For details, see Reynolds et al "Model Finding for
 * Recursive Functions" IJCAR 2016.
 */
class FunDefFmf : public PreprocessingPass
{
  /** The types for the recursive function definitions */
  typedef context::CDList<Node> NodeList;

 public:
  FunDefFmf(PreprocessingPassContext* preprocContext);
  ~FunDefFmf();

 protected:
  /**
   * Run the preprocessing pass on the pipeline, taking into account the
   * previous definitions.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** Run the preprocessing pass on the pipeline. */
  void process(AssertionPipeline* assertionsToPreprocess);
  /** simplify formula
   * This is A_0 in Figure 1 of Reynolds et al "Model Finding for Recursive
   * Functions". The input of A_0 in that paper is a pair ( term t, polarity p )
   * The return value of A_0 in that paper is a pair ( term t', set of formulas
   * X ).
   *
   * This function implements this such that :
   *   n is t
   *   pol/hasPol is p
   *   the return value is t'
   *   the set of formulas X are stored in "constraints"
   *
   * Additionally, is_fun_def is whether we are currently processing the top of
   * a function defintion, since this affects whether we process the head of the
   * definition.
   */
  Node simplifyFormula(Node n,
                       bool pol,
                       bool hasPol,
                       std::vector<Node>& constraints,
                       Node hd,
                       bool is_fun_def,
                       std::map<int, std::map<Node, Node>>& visited,
                       std::map<int, std::map<Node, Node>>& visited_cons);
  /** get constraints
   *
   * This computes constraints for the final else branch of A_0 in Figure 1
   * of Reynolds et al "Model Finding for Recursive Functions". The range of
   * the cache visited stores the constraint (if any) for each node.
   */
  void getConstraints(Node n,
                      std::vector<Node>& constraints,
                      std::map<Node, Node>& visited);
  /** recursive function definition abstractions for fmf-fun */
  std::map<Node, TypeNode> d_fmfRecFunctionsAbs;
  /** map to concrete definitions for fmf-fun */
  std::map<Node, std::vector<Node>> d_fmfRecFunctionsConcrete;
  /** List of defined recursive functions processed by fmf-fun */
  NodeList* d_fmfRecFunctionsDefined;
  // defined functions to input sort (alpha)
  std::map<Node, TypeNode> d_sorts;
  // defined functions to injections input -> argument elements (gamma)
  std::map<Node, std::vector<Node>> d_input_arg_inj;
  // (newly) defined functions
  std::vector<Node> d_funcs;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__SYGUS_INFERENCE_H_ */
