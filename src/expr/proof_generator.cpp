/*********************                                                        */
/*! \file proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof generator utility
 **/

#include "expr/proof_generator.h"

#include "expr/proof.h"
#include "expr/proof_node_algorithm.h"
#include "options/smt_options.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, CDPOverwrite opol)
{
  switch (opol)
  {
    case CDPOverwrite::ALWAYS: out << "ALWAYS"; break;
    case CDPOverwrite::ASSUME_ONLY: out << "ASSUME_ONLY"; break;
    case CDPOverwrite::NEVER: out << "NEVER"; break;
    default: out << "CDPOverwrite:unknown"; break;
  }
  return out;
}

ProofGenerator::ProofGenerator() {}

ProofGenerator::~ProofGenerator() {}

std::shared_ptr<ProofNode> ProofGenerator::getProofFor(Node f)
{
  Unreachable() << "ProofGenerator::getProofFor: " << identify()
                << " has no implementation" << std::endl;
  return nullptr;
}

bool ProofGenerator::addProofTo(Node f,
                                CDProof* pf,
                                CDPOverwrite opolicy,
                                bool doCopy)
{
  Trace("pfgen") << "ProofGenerator::addProofTo: " << f << "..." << std::endl;
  Assert(pf != nullptr);
  // plug in the proof provided by the generator, if it exists
  std::shared_ptr<ProofNode> apf = getProofFor(f);
  if (apf != nullptr)
  {
    Trace("pfgen") << "...got proof " << *apf.get() << std::endl;
    if (pf->addProof(apf, opolicy, doCopy))
    {
      Trace("pfgen") << "...success!" << std::endl;
      return true;
    }
    Trace("pfgen") << "...failed to add proof" << std::endl;
  }
  else
  {
    Trace("pfgen") << "...failed, no proof" << std::endl;
    Assert(false) << "Failed to get proof from generator for fact " << f;
  }
  return false;
}

/**
 * Ensure closed with respect to assumptions, internal version, which
 * generalizes the check for a proof generator or a proof node.
 */
void ensureClosedWrtInternal(Node proven,
                             ProofGenerator* pg,
                             ProofNode* pnp,
                             const std::vector<Node>& assumps,
                             const char* c,
                             const char* ctx,
                             bool reqGen)
{
  if (!options::proofNew())
  {
    // proofs not enabled, do not do check
    return;
  }
  bool isTraceDebug = Trace.isOn(c);
  if (!options::proofNewEagerChecking() && !isTraceDebug)
  {
    // trace is off and proof new eager checking is off, do not do check
    return;
  }
  std::stringstream sdiag;
  bool isTraceOn = Trace.isOn(c);
  if (!isTraceOn)
  {
    sdiag << ", use -t " << c << " for details";
  }
  bool dumpProofTraceOn = Trace.isOn("dump-proof-error");
  if (!dumpProofTraceOn)
  {
    sdiag << ", use -t dump-proof-error for details on proof";
  }
  // get the proof node in question, which is either provided or built by the
  // proof generator
  std::shared_ptr<ProofNode> pn;
  std::stringstream ss;
  if (pnp != nullptr)
  {
    Assert(pg == nullptr);
    ss << "ProofNode in context " << ctx;
  }
  else
  {
    ss << "ProofGenerator: " << (pg == nullptr ? "null" : pg->identify())
       << " in context " << ctx;
    if (pg == nullptr)
    {
      // only failure if flag is true
      if (reqGen)
      {
        Unreachable() << "...ensureClosed: no generator in context " << ctx
                      << sdiag.str();
      }
    }
    else
    {
      Assert(!proven.isNull());
      pn = pg->getProofFor(proven);
      pnp = pn.get();
    }
  }
  Trace(c) << "=== ensureClosed: " << ss.str() << std::endl;
  Trace(c) << "Proven: " << proven << std::endl;
  if (pnp == nullptr)
  {
    if (pg == nullptr)
    {
      // did not require generator
      Assert(!reqGen);
      Trace(c) << "...ensureClosed: no generator in context " << ctx
               << std::endl;
      return;
    }
  }
  // if we don't have a proof node, a generator failed
  if (pnp == nullptr)
  {
    Assert(pg != nullptr);
    AlwaysAssert(false) << "...ensureClosed: null proof from " << ss.str()
                        << sdiag.str();
  }
  std::vector<Node> fassumps;
  expr::getFreeAssumptions(pnp, fassumps);
  bool isClosed = true;
  std::stringstream ssf;
  for (const Node& fa : fassumps)
  {
    if (std::find(assumps.begin(), assumps.end(), fa) == assumps.end())
    {
      isClosed = false;
      ssf << "- " << fa << std::endl;
    }
  }
  if (!isClosed)
  {
    Trace(c) << "Free assumptions:" << std::endl;
    Trace(c) << ssf.str();
    if (!assumps.empty())
    {
      Trace(c) << "Expected assumptions:" << std::endl;
      for (const Node& a : assumps)
      {
        Trace(c) << "- " << a << std::endl;
      }
    }
    if (dumpProofTraceOn)
    {
      Trace("dump-proof-error") << " Proof: " << *pnp << std::endl;
    }
  }
  AlwaysAssert(isClosed) << "...ensureClosed: open proof from " << ss.str()
                         << sdiag.str();
  Trace(c) << "...ensureClosed: success" << std::endl;
  Trace(c) << "====" << std::endl;
}

void pfgEnsureClosed(Node proven,
                     ProofGenerator* pg,
                     const char* c,
                     const char* ctx,
                     bool reqGen)
{
  Assert(!proven.isNull());
  // proof generator may be null
  std::vector<Node> assumps;
  ensureClosedWrtInternal(proven, pg, nullptr, assumps, c, ctx, reqGen);
}

void pfgEnsureClosedWrt(Node proven,
                        ProofGenerator* pg,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx,
                        bool reqGen)
{
  Assert(!proven.isNull());
  // proof generator may be null
  ensureClosedWrtInternal(proven, pg, nullptr, assumps, c, ctx, reqGen);
}

void pfnEnsureClosed(ProofNode* pn, const char* c, const char* ctx)
{
  ensureClosedWrtInternal(Node::null(), nullptr, pn, {}, c, ctx, false);
}

void pfnEnsureClosedWrt(ProofNode* pn,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx)
{
  ensureClosedWrtInternal(Node::null(), nullptr, pn, assumps, c, ctx, false);
}

}  // namespace CVC4
