/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BVToInt preprocessing pass.
 *
 * Converts bit-vector operations into integer operations.
 *
 */

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
#include "preprocessing/assertion_pipeline.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace std;
using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::bv;

BVToInt::BVToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-to-int"),
      d_intBlaster(preprocContext->getEnv(),
                   options().smt.solveBVAsInt,
                   options().smt.BVAndIntegerGranularity) {}

PreprocessingPassResult BVToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // vector of boolean nodes for additional constraints
  // this will always contain range constraints
  // and for options::SolveBVAsIntMode::BITWISE, it will
  // also include bitwise assertion constraints
  std::vector<Node> additionalConstraints;
  std::map<Node, Node> skolems;
  for (uint64_t i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    Node bvNode = (*assertionsToPreprocess)[i];
    Node intNode =
        d_intBlaster.intBlast(bvNode, additionalConstraints, skolems);
    Node rwNode = rewrite(intNode);
    Trace("bv-to-int-debug") << "bv node: " << bvNode << std::endl;
    Trace("bv-to-int-debug") << "int node: " << intNode << std::endl;
    Trace("bv-to-int-debug") << "rw node: " << rwNode << std::endl;
    assertionsToPreprocess->replace(i, rwNode);
  }
  addFinalizeAssertions(assertionsToPreprocess, additionalConstraints);
  addSkolemDefinitions(skolems);
  return PreprocessingPassResult::NO_CONFLICT;
}

void BVToInt::addSkolemDefinitions(const std::map<Node, Node>& skolems)
{
  map<Node, Node>::const_iterator it;
  for (it = skolems.begin(); it != skolems.end(); it++)
  {
    Node originalSkolem = it->first;
    Node definition = it->second;
    std::vector<Node> args;
    Node body;
    if (definition.getType().isFunction())
    {
      args.insert(args.end(), definition[0].begin(), definition[0].end());
      body = definition[1];
    }
    else
    {
      body = definition;
    }
    Trace("bv-to-int-debug") << "adding substitution: " << "[" << originalSkolem  << "] ----> [" << definition << "]"  << std::endl; 
    d_preprocContext->addSubstitution(originalSkolem, definition);
  }
}

void BVToInt::addFinalizeAssertions(
    AssertionPipeline* assertionsToPreprocess,
    const std::vector<Node>& additionalConstraints)
{
  NodeManager* nm = NodeManager::currentNM();
  Node lemmas = nm->mkAnd(additionalConstraints);
  assertionsToPreprocess->push_back(lemmas);
  Trace("bv-to-int-debug") << "range constraints: " << lemmas.toString()
                           << std::endl;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
