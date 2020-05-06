/*********************                                                        */
/*! \file lazy_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof utility
 **/

#include "expr/lazy_proof.h"

using namespace CVC4::kind;

namespace CVC4 {

LazyCDProof::LazyCDProof(ProofNodeManager* pnm, context::Context* c)
    : CDProof(pnm, c)
{
}

LazyCDProof::~LazyCDProof() {}

std::shared_ptr<ProofNode> LazyCDProof::mkLazyProof(Node fact)
{
  // make the proof, which should always be non-null, since we construct an
  // assumption in the worst case.
  std::shared_ptr<ProofNode> opf = mkProof(fact);
  Assert(opf != nullptr);
  if (d_gens.empty())
  {
    // optimization: no generators, we are done
    return opf;
  }
  // otherwise, we traverse the proof opf and fill in the ASSUME leafs that
  // have generators
  std::unordered_set<ProofNode*> visited;
  std::unordered_set<ProofNode*>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  visit.push_back(opf.get());
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      if (cur->getRule() == PfRule::ASSUME)
      {
        Node afact = cur->getResult();
        bool isSym = false;
        ProofGenerator* pg = getGeneratorFor(afact, isSym);
        if (pg != nullptr)
        {
          Assert(!isSym || afact.getKind() == EQUAL);
          Node afactGen = isSym ? afact[1].eqNode(afact[0]) : afact;
          // use the addProofTo interface
          if (!pg->addProofTo(afactGen, this))
          {
            Assert(false) << "Proof generator could not add proof for fact "
                          << afactGen << std::endl;
          }
        }
        // Notice that we do not traverse the proofs that have been generated
        // lazily by the proof generators here.  In other words, we assume that
        // the proofs from provided proof generators are "complete" and need
        // no further modification by this class.
      }
      else
      {
        const std::vector<std::shared_ptr<ProofNode>>& cc = cur->getChildren();
        for (const std::shared_ptr<ProofNode>& cp : cc)
        {
          visit.push_back(cp.get());
        }
      }
    }
  } while (!visit.empty());
  // we have now updated the ASSUME leafs of opf, return it
  return opf;
}

void LazyCDProof::addLazyStep(Node expected,
                              ProofGenerator* pg,
                              bool forceOverwrite)
{
  Assert(pg != nullptr);
  std::unordered_map<Node, ProofGenerator*, NodeHashFunction>::const_iterator
      it = d_gens.find(expected);
  if (it != d_gens.end() && !forceOverwrite)
  {
    // don't overwrite something that is already there
    return;
  }
  // just store now
  d_gens[expected] = pg;

  if (forceOverwrite)
  {
    // TODO: if we stored expected via a normal call to CDProof::addStep, then
    // we should overwrite the step in d_nodes with an ASSUME?
  }
}

ProofGenerator* LazyCDProof::getGeneratorFor(Node fact, bool& isSym)
{
  isSym = false;
  std::unordered_map<Node, ProofGenerator*, NodeHashFunction>::const_iterator
      it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return it->second;
  }
  // FIXME
  return nullptr;
  // could be symmetry
  if (fact.getKind() != EQUAL || fact[0] == fact[1])
  {
    return nullptr;
  }
  Node factSym = fact[1].eqNode(fact[0]);
  it = d_gens.find(factSym);
  if (it != d_gens.end())
  {
    isSym = true;
    return it->second;
  }
  return nullptr;
}

}  // namespace CVC4
