/*********************                                                        */
/*! \file bv_to_int.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar, Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BVToInt preprocessing pass
 **
 ** Converts bit-vector operations into integer operations.
 **
 **/

#include "preprocessing/passes/bv_to_int.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;
using namespace CVC4::theory::bv;

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_intBlaster(preprocContext->getSmt(), options::solveBVAsInt(), options::BVAndIntegerGranularity()){};

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> rangeConstraints;
  std::map<Node, Node> skolems;
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node bvNode = (*assertionsToPreprocess)[i];
    Node intNode = d_intBlaster.intBlast(bvNode, rangeConstraints, skolems);
    Node rwNode = Rewriter::rewrite(intNode);
    Trace("bv-to-int-debug") << "bv node: " << bvNode << std::endl;
    Trace("bv-to-int-debug") << "int node: " << intNode << std::endl;
    Trace("bv-to-int-debug") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  addFinalizeRangeAssertions(assertionsToPreprocess, rangeConstraints);
  return PreprocessingPassResult::NO_CONFLICT;
}

void BVToInt::addFinalizeRangeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    std::vector<Node> rangeConstraints)
{
  NodeManager* nm = NodeManager::currentNM();
  Node rangeLemma = nm->mkAnd(rangeConstraints);
  assertionsToPreprocess->push_back(rangeLemma);
  Trace("bv-to-int-debug") << "range constraints: " << rangeLemma.toString()
                           << std::endl;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
