/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for updating proof nodes.
 */

#include "proof/proof_node_converter.h"

namespace cvc5::internal {

ProofNodeConverter::ProofNodeConverter(Env& env,
                                       ProofNodeConverterCallback& cb,
                                       bool autoSym)
    : EnvObj(env), d_cb(cb)
{
}

std::shared_ptr<ProofNode> ProofNodeConverter::process(
    std::shared_ptr<ProofNode> pf)
{
  // The list of proof nodes we are currently traversing beneath. This is used
  // for checking for cycles in the overall proof.
  std::vector<std::shared_ptr<ProofNode>> traversing;
  // Map from formulas to (closed) proof nodes that prove that fact
  std::map<Node, std::shared_ptr<ProofNode>> resCache;
  // Map from formulas to non-closed proof nodes that prove that fact. These
  // are replaced by proofs in the above map when applicable.
  std::map<Node, std::vector<std::shared_ptr<ProofNode>>> resCacheNcWaiting;
  // Map from proof nodes to whether they contain assumptions
  std::unordered_map<const ProofNode*, bool> cfaMap;
  std::unordered_set<Node> cfaAllowed;
  cfaAllowed.insert(fa.begin(), fa.end());
  std::shared_ptr<ProofNode> pft = pf;
  while (pft->getRule() == ProofRule::SCOPE)
  {
    const std::vector<Node>& args = pft->getArguments();
    cfaAllowed.insert(args.begin(), args.end());
    pft = pft->getChildren()[0];
  }
  Trace("pf-process") << "ProofNodeUpdater::process" << std::endl;
  std::unordered_map<std::shared_ptr<ProofNode>, std::shared_ptr<ProofNode>>
      visited;
  std::unordered_map<std::shared_ptr<ProofNode>,
                     std::shared_ptr<ProofNode>>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  std::shared_ptr<ProofNode> cur;
  visit.push_back(pf);
  std::map<Node, std::shared_ptr<ProofNode>>::iterator itc;
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      visited[cur] = nullptr;
      traversing.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      // now, process children
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        if (std::find(traversing.begin(), traversing.end(), cp)
            != traversing.end())
        {
          Unhandled()
              << "ProofNodeUpdater::processInternal: cyclic proof! (use "
                 "--proof-check=eager)"
              << std::endl;
        }
        visit.push_back(cp);
      }
      continue;
    }
    visit.pop_back();
    if (it->second == nullptr)
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      visited[cur] = true;
      const std::vector<std::shared_ptr<ProofNode>>& ccp = cur->getChildren();
      std::vector<std::shared_ptr<ProofNode>> pchildren;
      for (const std::shared_ptr<ProofNode>& cp : ccp)
      {
        it = visited.find(cp);
        Assert(it != visited.end());
        pchildren.push_back(it->second);
      }
      std::shared_ptr<ProofNode> ret = processInternal(cur);
    }
  } while (!visit.empty());
  Trace("pf-process") << "ProofNodeUpdater::process: finished" << std::endl;
}

std::shared_ptr<ProofNode> ProofNodeConverter::processInternal(
    std::shared_ptr<ProofNode> pf,
    const std::vector<std::shared_ptr<ProofNode>>& pchildren)
{
  ProofRule id = cur->getRule();
  // use CDProof to open a scope for which the callback updates
  CDProof cpf(d_env, nullptr, "ProofNodeUpdater::CDProof", d_autoSym);

  // TODO
  return pf;
}

}  // namespace cvc5::internal

#endif
