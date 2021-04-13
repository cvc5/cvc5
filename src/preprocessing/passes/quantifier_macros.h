/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Pre-process step for detecting quantifier macro definitions.
 */

#include "cvc4_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__QUANTIFIER_MACROS_H
#define CVC5__PREPROCESSING__PASSES__QUANTIFIER_MACROS_H

#include <map>
#include <vector>
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

class QuantifierMacros : public PreprocessingPass
{
 public:
  QuantifierMacros(PreprocessingPassContext* preprocContext);
  ~QuantifierMacros() {}
 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  bool processAssertion(Node n);
  bool isBoundVarApplyUf(Node n);
  bool process(Node n, bool pol, std::vector<Node>& args, Node f);
  bool containsBadOp(Node n,
                     Node op,
                     std::vector<Node>& opc,
                     std::map<Node, bool>& visited);
  bool isGroundUfTerm(Node f, Node n);
  void getMacroCandidates(Node n,
                          std::vector<Node>& candidates,
                          std::map<Node, bool>& visited);
  Node solveInEquality(Node n, Node lit);
  bool getFreeVariables(Node n,
                        std::vector<Node>& v_quant,
                        std::vector<Node>& vars,
                        bool retOnly,
                        std::map<Node, bool>& visited);
  bool addMacroEq(Node n, Node ndef);
  /**
   * This applies macro elimination to the given pipeline, which discovers
   * whether there are any quantified formulas corresponding to macros,
   * and rewrites the given assertions pipeline.
   *
   * @param ap The pipeline to apply macros to.
   * @return Whether new definitions were inferred and we rewrote the assertions
   * based on them.
   */
  bool simplify(AssertionPipeline* ap);
  void finalizeDefinitions();
  void clearMaps();

  // map from operators to macro definition
  std::map<Node, Node> d_macroDefs;
  std::map<Node, Node> d_macroDefs_new;
  // simplify caches
  std::map<Node, Node> d_simplify_cache;
  std::map<Node, bool> d_quant_macros;
  bool d_ground_macros;
};

}  // passes
}  // preprocessing
}  // namespace cvc5

#endif /*CVC5__PREPROCESSING__PASSES__QUANTIFIER_MACROS_H */
