/*********************                                                        */
/*! \file assertion_pipeline.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Justin Xu, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief AssertionPipeline stores a list of assertions modified by
 ** preprocessing passes
 **/

#include "preprocessing/assertion_pipeline.h"

#include "expr/node_manager.h"
#include "proof/proof.h"
#include "proof/proof_manager.h"

namespace CVC4 {
namespace preprocessing {

AssertionPipeline::AssertionPipeline()
    : d_realAssertionsEnd(0), d_assumptionsStart(0), d_numAssumptions(0)
{
}

void AssertionPipeline::clear()
{
  d_nodes.clear();
  d_realAssertionsEnd = 0;
  d_assumptionsStart = 0;
  d_numAssumptions = 0;
}

void AssertionPipeline::push_back(Node n, bool isAssumption)
{
  d_nodes.push_back(n);
  if (isAssumption)
  {
    if (d_numAssumptions == 0)
    {
      d_assumptionsStart = d_nodes.size() - 1;
    }
    // Currently, we assume that assumptions are all added one after another
    // and that we store them in the same vector as the assertions. Once we
    // split the assertions up into multiple vectors (see issue #2473), we will
    // not have this limitation anymore.
    Assert(d_assumptionsStart + d_numAssumptions == d_nodes.size() - 1);
    d_numAssumptions++;
  }
}

void AssertionPipeline::replace(size_t i, Node n)
{
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]););
  d_nodes[i] = n;
}

void AssertionPipeline::replace(size_t i,
                                Node n,
                                const std::vector<Node>& addnDeps)
{
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]);
        for (const auto& addnDep
             : addnDeps) {
          ProofManager::currentPM()->addDependence(n, addnDep);
        });
  d_nodes[i] = n;
}

void AssertionPipeline::replace(size_t i, const std::vector<Node>& ns)
{
  PROOF(
      for (const auto& n
           : ns) { ProofManager::currentPM()->addDependence(n, d_nodes[i]); });
  d_nodes[i] = NodeManager::currentNM()->mkConst<bool>(true);

  for (const auto& n : ns)
  {
    d_nodes.push_back(n);
  }
}

}  // namespace preprocessing
}  // namespace CVC4
