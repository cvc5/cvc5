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
  d_false = NodeManager::currentNM()->mkConst(false);
}

theory::TrustNode TheoryEngineProofGenerator::mkTrustExplain(
    TNode lit, Node exp, std::shared_ptr<LazyCDProof> lpf)
{
  Node p;
  theory::TrustNode trn;
  if (lit == d_false)
  {
    // propagation of false is a conflict
    trn = theory::TrustNode::mkTrustConflict(exp, this);
    p = trn.getProven();
    Assert(p.getKind() == NOT);
  }
  else
  {
    trn = theory::TrustNode::mkTrustPropExp(lit, exp, this);
    p = trn.getProven();
    Assert(p.getKind() == IMPLIES && p.getNumChildren() == 2);
  }
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
  Trace("tepg-debug") << "TheoryEngineProofGenerator::getProofFor: " << f
                      << std::endl;
  NodeLazyCDProofMap::iterator it = d_proofs.find(f);
  if (it == d_proofs.end())
  {
    Trace("tepg-debug") << "...null" << std::endl;
    return nullptr;
  }
  std::shared_ptr<LazyCDProof> lcp = (*it).second;
  // finalize it via scope
  std::vector<Node> scopeAssumps;
  // should only ask this generator for proofs of implications, or conflicts
  Node exp;
  Node conclusion;
  if (f.getKind() == IMPLIES && f.getNumChildren() == 2)
  {
    exp = f[0];
    conclusion = f[1];
  }
  else if (f.getKind() == NOT)
  {
    exp = f[0];
    conclusion = d_false;
  }
  else
  {
    Unhandled() << "TheoryEngineProofGenerator::getProofFor: unexpected fact "
                << f << std::endl;
    return nullptr;
  }
  // get the assumptions to assume in a scope
  if (exp.getKind() == AND)
  {
    for (const Node& fc : exp)
    {
      scopeAssumps.push_back(fc);
    }
  }
  else
  {
    scopeAssumps.push_back(exp);
  }
  Trace("tepg-debug") << "...get proof body" << std::endl;
  // get the proof for conclusion
  std::shared_ptr<ProofNode> pfb = lcp->getProofFor(conclusion);
  Trace("tepg-debug") << "...mkScope" << std::endl;
  // call the scope method of proof node manager
  std::shared_ptr<ProofNode> pf = d_pnm->mkScope(pfb, scopeAssumps);

  if (pf->getResult() != f)
  {
    std::stringstream serr;
    serr << "TheoryEngineProofGenerator::getProofFor: Proof: " << std::endl;
    serr << *pf << std::endl;
    serr << "TheoryEngineProofGenerator::getProofFor: unexpected return proof"
         << std::endl;
    serr << "  Expected: " << f << std::endl;
    serr << "       Got: " << pf->getResult() << std::endl;
    Unhandled() << serr.str();
  }
  Trace("tepg-debug") << "...finished" << std::endl;
  return pf;
}

std::string TheoryEngineProofGenerator::identify() const
{
  return "TheoryEngineProofGenerator";
}

}  // namespace CVC4
