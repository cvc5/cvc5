/*********************                                                        */
/*! \file theory_engine_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine proof generator
 **/

#include "theory/theory_engine_proof_generator.h"

using namespace CVC4::kind;

namespace CVC4 {

TheoryEngineProofGenerator::TheoryEngineProofGenerator(ProofNodeManager* pnm,
                                                       context::UserContext* u)
    : d_pnm(pnm), d_proofs(u)
{
}

theory::TrustNode TheoryEngineProofGenerator::mkTrustExplain(
    TNode lit, Node exp, std::shared_ptr<LazyCDProof> lpf)
{
  theory::TrustNode trn = theory::TrustNode::mkTrustPropExp(lit, exp, this);
  Node p = trn.getProven();
  Assert(p.getKind() == IMPLIES && p.getNumChildren() == 2);
  // should not already be proven
  NodeLazyCDProofMap::iterator it = d_proofs.find(p);
  if (it == d_proofs.end())
  {
    // we will prove the fact p using the proof from lpf.
    d_proofs.insert(p, lpf);
  }
  return trn;
}

std::shared_ptr<ProofNode> TheoryEngineProofGenerator::getProofFor(Node f)
{
  // should only ask this generator for proofs of implications
  Assert(f.getKind() == IMPLIES && f.getNumChildren() == 2);
  NodeLazyCDProofMap::iterator it = d_proofs.find(f);
  if (it == d_proofs.end())
  {
    return nullptr;
  }
  std::shared_ptr<LazyCDProof> lcp = (*it).second;
  // finalize it via scope
  std::vector<Node> scopeAssumps;
  if (f[0].getKind() == AND)
  {
    for (const Node& fc : f[0])
    {
      scopeAssumps.push_back(fc);
    }
  }
  else
  {
    scopeAssumps.push_back(f[0]);
  }
  Node conclusion = f[1];

  // get the proof for conclusion
  std::shared_ptr<ProofNode> pfb = lcp->getProofFor(conclusion);
  // call the scope method of proof node manager
  std::shared_ptr<ProofNode> pf = d_pnm->mkScope(pfb, scopeAssumps);
  return pf;
}

std::string TheoryEngineProofGenerator::identify() const
{
  return "TheoryEngineProofGenerator";
}

}  // namespace CVC4
