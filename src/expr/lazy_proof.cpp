/*********************                                                        */
/*! \file lazy_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of lazy proof utility
 **/

#include "expr/lazy_proof.h"

using namespace CVC4::kind;

namespace CVC4 {

LazyCDProof::LazyCDProof(ProofNodeManager* pnm,
                         ProofGenerator* dpg,
                         context::Context* c)
    : CDProof(pnm, c), d_gens(c ? c : &d_context), d_defaultGen(dpg)
{
}

LazyCDProof::~LazyCDProof() {}

std::shared_ptr<ProofNode> LazyCDProof::getProofFor(Node fact)
{
  Trace("lazy-cdproof") << "LazyCDProof::mkLazyProof " << fact << std::endl;
  // make the proof, which should always be non-null, since we construct an
  // assumption in the worst case.
  std::shared_ptr<ProofNode> opf = CDProof::getProofFor(fact);
  Assert(opf != nullptr);
  if (!hasGenerators())
  {
    Trace("lazy-cdproof") << "...no generators, finished" << std::endl;
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
          Trace("lazy-cdproof") << "LazyCDProof: Call generator for assumption "
                                << afact << std::endl;
          Node afactGen = isSym ? CDProof::getSymmFact(afact) : afact;
          Assert(!afactGen.isNull());
          // use the addProofTo interface
          if (!pg->addProofTo(afactGen, this))
          {
            Trace("lazy-cdproof") << "LazyCDProof: Failed added fact for "
                                  << afactGen << std::endl;
            Assert(false) << "Proof generator " << pg->identify()
                          << " could not add proof for fact " << afactGen
                          << std::endl;
          }
          else
          {
            Trace("lazy-cdproof") << "LazyCDProof: Successfully added fact for "
                                  << afactGen << std::endl;
          }
        }
        else
        {
          Trace("lazy-cdproof")
              << "LazyCDProof: No generator for " << afact << std::endl;
        }
        // Notice that we do not traverse the proofs that have been generated
        // lazily by the proof generators here.  In other words, we assume that
        // the proofs from provided proof generators are final and need
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
  Trace("lazy-cdproof") << "...finished" << std::endl;
  return opf;
}

void LazyCDProof::addLazyStep(Node expected,
                              ProofGenerator* pg,
                              bool forceOverwrite)
{
  Assert(pg != nullptr);
  if (!forceOverwrite)
  {
    NodeProofGeneratorMap::const_iterator it = d_gens.find(expected);
    if (it != d_gens.end())
    {
      // don't overwrite something that is already there
      return;
    }
  }
  // just store now
  d_gens.insert(expected, pg);
}

ProofGenerator* LazyCDProof::getGeneratorFor(Node fact,
                                             bool& isSym)
{
  isSym = false;
  NodeProofGeneratorMap::const_iterator it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return (*it).second;
  }
  Node factSym = CDProof::getSymmFact(fact);
  // could be symmetry
  if (factSym.isNull())
  {
    // can't be symmetry, return the default generator
    return d_defaultGen;
  }
  it = d_gens.find(factSym);
  if (it != d_gens.end())
  {
    isSym = true;
    return (*it).second;
  }
  // return the default generator
  return d_defaultGen;
}

bool LazyCDProof::hasGenerators() const
{
  return !d_gens.empty() || d_defaultGen != nullptr;
}

bool LazyCDProof::hasGenerator(Node fact) const
{
  if (d_defaultGen != nullptr)
  {
    return true;
  }
  NodeProofGeneratorMap::const_iterator it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return true;
  }
  // maybe there is a symmetric fact?
  Node factSym = CDProof::getSymmFact(fact);
  if (!factSym.isNull())
  {
    it = d_gens.find(factSym);
  }
  return it != d_gens.end();
}

std::string LazyCDProof::identify() const { return "LazyCDProof"; }

}  // namespace CVC4
