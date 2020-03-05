/*********************                                                        */
/*! \file quantifier_macro_elimination.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Scott Kovach, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **/
#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING_PASSES_FOO_H
#define CVC4__PREPROCESSING_PASSES_FOO_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace std;

// TODO: are these already defined somewhere else?
template <typename T>
bool setContains(set<T> s, T t)
{
  return s.find(t) != s.end();
}
template <typename K, typename V>
bool mapContains(map<K, V> s, K k)
{
  return s.find(k) != s.end();
}

class QuantifierMacroElimination : public PreprocessingPass
{
 public:
  QuantifierMacroElimination(PreprocessingPassContext* preprocContext);
  ~QuantifierMacroElimination() override;

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  map<Node, Node> d_macroDefinitions;
  map<Node, vector<Node>> d_macroBoundVariables;
  bool addMacroDefinitionIfPresent(Node assertion);
  Node replaceMacroInstances(Node assertion);
  bool isDefinitionValid(Node predicate, Node definition);

  set<Node> d_definitionNodes;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif
