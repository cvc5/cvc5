/*********************                                                        */
/*! \file preprocess_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The implementation of the module for proofs for preprocessing in an
 ** SMT engine.
 **/

#include "smt/preprocess_proof_generator.h"

#include "expr/proof.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace smt {

PreprocessProofGenerator::PreprocessProofGenerator(ProofNodeManager* pnm)
    : d_pnm(pnm)
{
}

void PreprocessProofGenerator::notifyNewAssert(Node n, ProofGenerator* pg)
{
  Trace("smt-proof-pp-debug") << "- notifyNewAssert: " << n << std::endl;
  d_src[n] = theory::TrustNode::mkTrustLemma(n, pg);
}

void PreprocessProofGenerator::notifyPreprocessed(Node n,
                                                  Node np,
                                                  ProofGenerator* pg)
{
  // only keep if indeed it rewrote
  if (n != np)
  {
    Trace("smt-proof-pp-debug")
        << "- notifyPreprocessed: " << n << "..." << np << std::endl;
    d_src[np] = theory::TrustNode::mkTrustRewrite(n, np, pg);
  }
}

std::shared_ptr<ProofNode> PreprocessProofGenerator::getProofFor(Node f)
{
  std::map<Node, theory::TrustNode>::iterator it = d_src.find(f);
  if (it == d_src.end())
  {
    // could be an assumption, return nullptr
    return nullptr;
  }
  // make CDProof to construct the proof below
  CDProof cdp(d_pnm);

  Node curr = f;
  std::vector<Node> transChildren;
  bool success;
  do
  {
    success = false;
    if (it != d_src.end())
    {
      Assert(it->second.getNode() == curr);
      bool proofStepProcessed = false;
      std::shared_ptr<ProofNode> pfr = it->second.toProofNode();
      if (pfr != nullptr)
      {
        Assert(pfr->getResult() == it->second.getProven());
        cdp.addProof(pfr);
        proofStepProcessed = true;
      }

      if (it->second.getKind() == theory::TrustNodeKind::REWRITE)
      {
        Node eq = it->second.getProven();
        Assert(eq.getKind() == kind::EQUAL);
        if (!proofStepProcessed)
        {
          // maybe its just a simple rewrite?
          if (eq[1] == theory::Rewriter::rewrite(eq[0]))
          {
            cdp.addStep(eq, PfRule::REWRITE, {}, {eq[0]});
            proofStepProcessed = true;
          }
        }
        transChildren.push_back(eq);
        // continue with source
        curr = eq[0];
        success = true;
        // find the next node
        it = d_src.find(curr);
      }
      else
      {
        Assert(it->second.getKind() == theory::TrustNodeKind::LEMMA);
      }

      if (!proofStepProcessed)
      {
        // add trusted step
        Node proven = it->second.getProven();
        cdp.addStep(proven, PfRule::PREPROCESS, {}, {proven});
      }
    }
  } while (success);

  Assert(curr != f);
  // prove ( curr == f )
  Node fullRewrite = curr.eqNode(f);
  if (transChildren.size() >= 2)
  {
    cdp.addStep(fullRewrite, PfRule::TRANS, transChildren, {});
  }
  // prove f
  cdp.addStep(f, PfRule::EQ_RESOLVE, {curr, fullRewrite}, {});

  // overall, proof is:
  //        --------- from proof generator       ---------- from proof generator
  //        F_1 = F_2          ...               F_{n-1} = F_n
  // ---?   -------------------------------------------------- TRANS
  // F_1    F_1 = F_n
  // ---------------- EQ_RESOLVE
  // F_n
  // Note F_1 may have been given a proof if it was not an input assumption.

  return cdp.getProofFor(f);
}

std::string PreprocessProofGenerator::identify() const
{
  return "PreprocessProofGenerator";
}

}  // namespace smt
}  // namespace CVC4
