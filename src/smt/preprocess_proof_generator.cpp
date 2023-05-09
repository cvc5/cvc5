/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The implementation of the module for proofs for preprocessing in an
 * SMT engine.
 */

#include "smt/preprocess_proof_generator.h"

#include <sstream>

#include "options/proof_options.h"
#include "proof/method_id.h"
#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/quantifiers/extended_rewrite.h"

namespace cvc5::internal {
namespace smt {

PreprocessProofGenerator::PreprocessProofGenerator(
    Env& env, context::Context* c, std::string name, PfRule ra, PfRule rpp)
    : EnvObj(env),
      d_ctx(c ? c : &d_context),
      d_src(d_ctx),
      d_helperProofs(env, d_ctx),
      d_inputPf(env, c, "InputProof"),
      d_name(name),
      d_ra(ra),
      d_rpp(rpp)
{
}

void PreprocessProofGenerator::notifyInput(Node n)
{
  notifyNewAssert(n, &d_inputPf);
}

void PreprocessProofGenerator::notifyNewAssert(Node n, ProofGenerator* pg)
{
  if (n.isConst() && n.getConst<bool>())
  {
    // ignore true assertions
    return;
  }
  Trace("smt-proof-pp-debug")
      << "PreprocessProofGenerator::notifyNewAssert: " << identify() << " " << n
      << " from " << (pg == nullptr ? "null" : pg->identify()) << std::endl;
  if (d_src.find(n) == d_src.end())
  {
    // if no proof generator provided for (non-true) assertion
    if (pg == nullptr)
    {
      checkEagerPedantic(d_ra);
    }
    d_src[n] = TrustNode::mkTrustLemma(n, pg);
  }
  else
  {
    Trace("smt-proof-pp-debug") << "...already proven" << std::endl;
  }
}

void PreprocessProofGenerator::notifyNewTrustedAssert(TrustNode tn)
{
  notifyNewAssert(tn.getProven(), tn.getGenerator());
}

void PreprocessProofGenerator::notifyPreprocessed(Node n,
                                                  Node np,
                                                  ProofGenerator* pg)
{
  // only do anything if indeed it rewrote
  if (n == np)
  {
    return;
  }
  // call the trusted version
  notifyTrustedPreprocessed(TrustNode::mkTrustRewrite(n, np, pg));
}

void PreprocessProofGenerator::notifyTrustedPreprocessed(TrustNode tnp)
{
  if (tnp.isNull())
  {
    // no rewrite, nothing to do
    return;
  }
  Assert(tnp.getKind() == TrustNodeKind::REWRITE);
  Node np = tnp.getNode();
  Trace("smt-proof-pp-debug")
      << "PreprocessProofGenerator::notifyPreprocessed: " << tnp << std::endl;
  if (d_src.find(np) == d_src.end())
  {
    if (tnp.getGenerator() == nullptr)
    {
      checkEagerPedantic(d_rpp);
    }
    d_src[np] = tnp;
  }
  else
  {
    Trace("smt-proof-pp-debug") << "...already proven" << std::endl;
  }
}

std::shared_ptr<ProofNode> PreprocessProofGenerator::getProofFor(Node f)
{
  Trace("smt-pppg") << "PreprocessProofGenerator::getProofFor: (" << d_name
                    << ") input " << f << std::endl;
  NodeTrustNodeMap::iterator it = d_src.find(f);
  if (it == d_src.end())
  {
    Trace("smt-pppg") << "...no proof for " << identify() << " " << f
                      << std::endl;
    // could be an assumption, return nullptr
    return nullptr;
  }
  // make CDProof to construct the proof below
  CDProof cdp(d_env);

  Node curr = f;
  std::vector<Node> transChildren;
  std::unordered_set<Node> processed;
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
      Trace("smt-pppg-debug")
          << "...get provided proof " << (*it).second << std::endl;
      std::shared_ptr<ProofNode> pfr = (*it).second.toProofNode();
      if (pfr != nullptr)
      {
        Trace("smt-pppg-debug") << "...add provided " << *pfr << std::endl;
        Assert(pfr->getResult() == proven);
        cdp.addProof(pfr);
        proofStepProcessed = true;
      }

      Trace("smt-pppg-debug") << "...update" << std::endl;
      TrustNodeKind tnk = (*it).second.getKind();
      if (tnk == TrustNodeKind::REWRITE)
      {
        Trace("smt-pppg-debug")
            << "...rewritten from " << proven[0] << std::endl;
        Assert(proven.getKind() == kind::EQUAL);
        if (!proofStepProcessed)
        {
          // maybe its just an (extended) rewrite?
          Node pr = extendedRewrite(proven[0]);
          if (proven[1] == pr)
          {
            Node idr = mkMethodId(MethodId::RW_EXT_REWRITE);
            Trace("smt-pppg-debug") << "...add simple rewrite" << std::endl;
            cdp.addStep(proven, PfRule::REWRITE, {}, {proven[0], idr});
            proofStepProcessed = true;
          }
        }
        transChildren.push_back(proven);
        // continue with source
        curr = proven[0];
        success = true;
        // find the next node
        Trace("smt-pppg") << "...continue " << curr << std::endl;
        it = d_src.find(curr);
      }
      else
      {
        Trace("smt-pppg") << "...lemma" << std::endl;
        Assert(tnk == TrustNodeKind::LEMMA);
      }

      if (!proofStepProcessed)
      {
        Trace("smt-pppg-debug")
            << "...justify missing step with "
            << (tnk == TrustNodeKind::LEMMA ? d_ra : d_rpp) << std::endl;
        // add trusted step, the rule depends on the kind of trust node
        cdp.addStep(
            proven, tnk == TrustNodeKind::LEMMA ? d_ra : d_rpp, {}, {proven});
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

LazyCDProof* PreprocessProofGenerator::allocateHelperProof()
{
  return d_helperProofs.allocateProof(nullptr, d_ctx);
}

std::string PreprocessProofGenerator::identify() const { return d_name; }

void PreprocessProofGenerator::checkEagerPedantic(PfRule r)
{
  if (options().proof.proofCheck == options::ProofCheckMode::EAGER)
  {
    // catch a pedantic failure now, which otherwise would not be
    // triggered since we are doing lazy proof generation
    ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
    std::stringstream serr;
    if (pc->isPedanticFailure(r, serr))
    {
      Unhandled() << "PreprocessProofGenerator::checkEagerPedantic: "
                  << serr.str();
    }
  }
}

}  // namespace smt
}  // namespace cvc5::internal
