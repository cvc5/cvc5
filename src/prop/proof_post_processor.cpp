/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the module for processing proof nodes in the prop engine.
 */

#include "prop/proof_post_processor.h"

#include "proof/proof.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace prop {

ProofPostprocessCallback::ProofPostprocessCallback(
    Env& env, ProofGenerator* proofCnfStream)
    : EnvObj(env), d_pg(proofCnfStream), d_blocked(userContext())
{
}

void ProofPostprocessCallback::initializeUpdate() { d_assumpToProof.clear(); }

bool ProofPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                            const std::vector<Node>& fa,
                                            bool& continueUpdate)
{
  bool result =
      pn->getRule() == ProofRule::ASSUME && d_pg->hasProofFor(pn->getResult());
  if (TraceIsOn("prop-proof-pp") && !result
      && pn->getRule() == ProofRule::ASSUME)
  {
    Trace("prop-proof-pp") << "- Ignoring no-proof assumption "
                           << pn->getResult() << "\n";
  }
  // check if should continue traversing
  if (isBlocked(pn))
  {
    continueUpdate = false;
    result = false;
  }
  return result;
}

bool ProofPostprocessCallback::update(Node res,
                                      ProofRule id,
                                      const std::vector<Node>& children,
                                      const std::vector<Node>& args,
                                      CDProof* cdp,
                                      bool& continueUpdate)
{
  Trace("prop-proof-pp") << "- Post process " << id << " " << res << " : "
                         << children << " / " << args << "\n"
                         << push;
  Assert(id == ProofRule::ASSUME);
  // we cache based on the assumption node, not the proof node, since there
  // may be multiple occurrences of the same node.
  Node f = args[0];
  std::shared_ptr<ProofNode> pfn;
  std::map<Node, std::shared_ptr<ProofNode>>::iterator it =
      d_assumpToProof.find(f);
  if (it != d_assumpToProof.end())
  {
    Trace("prop-proof-pp") << "...already computed" << std::endl;
    pfn = it->second;
  }
  else
  {
    Assert(d_pg != nullptr);
    // get proof from proof cnf stream
    pfn = d_pg->getProofFor(f);
    Assert(pfn != nullptr && pfn->getResult() == f);
    if (TraceIsOn("prop-proof-pp"))
    {
      Trace("prop-proof-pp") << "=== Connect CNF proof for: " << f << "\n";
      Trace("prop-proof-pp") << *pfn.get() << "\n";
    }
    d_assumpToProof[f] = pfn;
  }
  Trace("prop-proof-pp") << pop;
  // connect the proof
  cdp->addProof(pfn);
  // do not recursively process the result
  continueUpdate = false;
  // moreover block the fact f so that its proof node is not traversed if we run
  // this post processor again (which can happen in incremental benchmarks)
  addBlocked(pfn);
  return true;
}

void ProofPostprocessCallback::addBlocked(std::shared_ptr<ProofNode> pfn)
{
  d_blocked.insert(pfn);
}

bool ProofPostprocessCallback::isBlocked(std::shared_ptr<ProofNode> pfn)
{
  return d_blocked.contains(pfn);
}

ProofPostprocess::ProofPostprocess(Env& env, ProofGenerator* pg)
    : EnvObj(env), d_cb(env, pg)
{
}

ProofPostprocess::~ProofPostprocess() {}

void ProofPostprocess::process(std::shared_ptr<ProofNode> pf)
{
  // Initialize the callback, which computes necessary static information about
  // how to process, including how to process assumptions in pf.
  d_cb.initializeUpdate();
  // now, process
  ProofNodeUpdater updater(d_env, d_cb);
  updater.process(pf);
}

}  // namespace prop
}  // namespace cvc5::internal
