/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of debug checks for ensuring proofs are closed.
 */

#include "proof/proof_ensure_closed.h"

#include <sstream>

#include "options/proof_options.h"
#include "options/smt_options.h"
#include "proof/proof_generator.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"

namespace cvc5::internal {

/**
 * Ensure closed with respect to assumptions, internal version, which
 * generalizes the check for a proof generator or a proof node.
 */
void ensureClosedWrtInternal(const Options& opts,
                             Node proven,
                             ProofGenerator* pg,
                             ProofNode* pnp,
                             const std::vector<Node>& assumps,
                             const char* c,
                             const char* ctx,
                             bool reqGen)
{
  if (!opts.smt.produceProofs)
  {
    // proofs not enabled, do not do check
    return;
  }
  bool isTraceDebug = TraceIsOn(c);
  if (opts.proof.proofCheck != options::ProofCheckMode::EAGER && !isTraceDebug)
  {
    // trace is off and proof new eager checking is off, do not do check
    return;
  }
  std::stringstream sdiag;
  bool isTraceOn = TraceIsOn(c);
  if (!isTraceOn)
  {
    sdiag << ", use -t " << c << " for details";
  }
  bool dumpProofTraceOn = TraceIsOn("dump-proof-error");
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

void pfgEnsureClosed(const Options& opts,
                     Node proven,
                     ProofGenerator* pg,
                     const char* c,
                     const char* ctx,
                     bool reqGen)
{
  Assert(!proven.isNull());
  // proof generator may be null
  std::vector<Node> assumps;
  ensureClosedWrtInternal(opts, proven, pg, nullptr, assumps, c, ctx, reqGen);
}

void pfgEnsureClosedWrt(const Options& opts,
                        Node proven,
                        ProofGenerator* pg,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx,
                        bool reqGen)
{
  Assert(!proven.isNull());
  // proof generator may be null
  ensureClosedWrtInternal(opts, proven, pg, nullptr, assumps, c, ctx, reqGen);
}

void pfnEnsureClosed(const Options& opts,
                     ProofNode* pn,
                     const char* c,
                     const char* ctx)
{
  ensureClosedWrtInternal(opts, Node::null(), nullptr, pn, {}, c, ctx, false);
}

void pfnEnsureClosedWrt(const Options& opts,
                        ProofNode* pn,
                        const std::vector<Node>& assumps,
                        const char* c,
                        const char* ctx)
{
  ensureClosedWrtInternal(
      opts, Node::null(), nullptr, pn, assumps, c, ctx, false);
}

}  // namespace cvc5::internal
