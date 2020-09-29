/*********************                                                        */
/*! \file preprocess_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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

PreprocessProofGenerator::PreprocessProofGenerator(context::UserContext* u,
                                                   ProofNodeManager* pnm)
    : d_pnm(pnm), d_src(u), d_helperProofs(u)
{
}

void PreprocessProofGenerator::notifyNewAssert(Node n, ProofGenerator* pg)
{
  Trace("smt-proof-pp-debug")
      << "PreprocessProofGenerator::notifyNewAssert: " << n << std::endl;
  if (d_src.find(n) == d_src.end())
  {
    d_src[n] = theory::TrustNode::mkTrustLemma(n, pg);
  }
  else
  {
    Trace("smt-proof-pp-debug") << "...already proven" << std::endl;
  }
}

void PreprocessProofGenerator::notifyPreprocessed(Node n,
                                                  Node np,
                                                  ProofGenerator* pg)
{
  // only keep if indeed it rewrote
  if (n != np)
  {
    Trace("smt-proof-pp-debug")
        << "PreprocessProofGenerator::notifyPreprocessed: " << n << "..." << np
        << std::endl;
    if (d_src.find(np) == d_src.end())
    {
      d_src[np] = theory::TrustNode::mkTrustRewrite(n, np, pg);
    }
    else
    {
      Trace("smt-proof-pp-debug") << "...already proven" << std::endl;
    }
  }
}

std::shared_ptr<ProofNode> PreprocessProofGenerator::getProofFor(Node f)
{
  NodeTrustNodeMap::iterator it = d_src.find(f);
  if (it == d_src.end())
  {
    // could be an assumption, return nullptr
    return nullptr;
  }
  // make CDProof to construct the proof below
  CDProof cdp(d_pnm);

  Trace("smt-pppg") << "PreprocessProofGenerator::getProofFor: input " << f
                    << std::endl;
  Node curr = f;
  std::vector<Node> transChildren;
  std::unordered_set<Node, NodeHashFunction> processed;
  bool success;
  // we connect the proof of f to its source via the map d_src until we
  // discover that its source is a preprocessing lemma (a lemma stored in d_src)
  // or otherwise it is assumed to be an input assumption.
  do
  {
    success = false;
    if (it != d_src.end())
    {
      Assert((*it).second.getNode() == curr);
      // get the proven node
      Node proven = (*it).second.getProven();
      Assert(!proven.isNull());
      Trace("smt-pppg") << "...process proven " << proven << std::endl;
      if (processed.find(proven) != processed.end())
      {
        Unhandled() << "Cyclic steps in preprocess proof generator";
        continue;
      }
      processed.insert(proven);
      bool proofStepProcessed = false;

      // if a generator for the step was provided, it is stored in the proof
      Trace("smt-pppg") << "...get provided proof" << std::endl;
      std::shared_ptr<ProofNode> pfr = (*it).second.toProofNode();
      if (pfr != nullptr)
      {
        Trace("smt-pppg") << "...add provided" << std::endl;
        Assert(pfr->getResult() == proven);
        cdp.addProof(pfr);
        proofStepProcessed = true;
      }

      Trace("smt-pppg") << "...update" << std::endl;
      theory::TrustNodeKind tnk = (*it).second.getKind();
      if (tnk == theory::TrustNodeKind::REWRITE)
      {
        Trace("smt-pppg") << "...rewritten from " << proven[0] << std::endl;
        Assert(proven.getKind() == kind::EQUAL);
        if (!proofStepProcessed)
        {
          // maybe its just a simple rewrite?
          if (proven[1] == theory::Rewriter::rewrite(proven[0]))
          {
            cdp.addStep(proven, PfRule::REWRITE, {}, {proven[0]});
            proofStepProcessed = true;
          }
        }
        transChildren.push_back(proven);
        // continue with source
        curr = proven[0];
        success = true;
        // find the next node
        it = d_src.find(curr);
      }
      else
      {
        Trace("smt-pppg") << "...lemma" << std::endl;
        Assert(tnk == theory::TrustNodeKind::LEMMA);
      }

      if (!proofStepProcessed)
      {
        Trace("smt-pppg") << "...add missing step" << std::endl;
        // add trusted step, the rule depends on the kind of trust node
        cdp.addStep(proven,
                    tnk == theory::TrustNodeKind::LEMMA
                        ? PfRule::PREPROCESS_LEMMA
                        : PfRule::PREPROCESS,
                    {},
                    {proven});
      }
    }
  } while (success);

  // prove ( curr == f ), which is not necessary if they are the same
  // modulo symmetry.
  if (!CDProof::isSame(f, curr))
  {
    Node fullRewrite = curr.eqNode(f);
    if (transChildren.size() >= 2)
    {
      Trace("smt-pppg") << "...apply trans to get " << fullRewrite << std::endl;
      std::reverse(transChildren.begin(), transChildren.end());
      cdp.addStep(fullRewrite, PfRule::TRANS, transChildren, {});
    }
    Trace("smt-pppg") << "...eq_resolve to prove" << std::endl;
    // prove f
    cdp.addStep(f, PfRule::EQ_RESOLVE, {curr, fullRewrite}, {});
    Trace("smt-pppg") << "...finished" << std::endl;
  }

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

ProofNodeManager* PreprocessProofGenerator::getManager() { return d_pnm; }

LazyCDProof* PreprocessProofGenerator::allocateHelperProof()
{
  std::shared_ptr<LazyCDProof> helperPf = std::make_shared<LazyCDProof>(d_pnm);
  d_helperProofs.push_back(helperPf);
  return helperPf.get();
}

std::string PreprocessProofGenerator::identify() const
{
  return "PreprocessProofGenerator";
}

}  // namespace smt
}  // namespace CVC4
