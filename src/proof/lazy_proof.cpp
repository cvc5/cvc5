/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lazy proof utility.
 */

#include "proof/lazy_proof.h"

#include "proof/proof_ensure_closed.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

LazyCDProof::LazyCDProof(Env& env,
                         ProofGenerator* dpg,
                         context::Context* c,
                         const std::string& name,
                         bool autoSym,
                         bool doCache)
    : CDProof(env, c, name, autoSym),
      d_gens(c ? c : &d_context),
      d_defaultGen(dpg),
      d_doCache(doCache),
      d_allVisited(c ? c : &d_context)
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
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  visit.push_back(opf.get());
  bool alreadyVisited;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (d_doCache)
    {
      alreadyVisited = d_allVisited.find(cur) != d_allVisited.end();
    }
    else
    {
      alreadyVisited = visited.find(cur) != visited.end();
    }

    if (!alreadyVisited)
    {
      if (d_doCache)
      {
        d_allVisited.insert(cur);
      }
      else
      {
        visited.insert(cur);
      }
      Node cfact = cur->getResult();
      if (getProof(cfact).get() != cur)
      {
        // We don't own this proof, skip it. This is to ensure that this method
        // is idempotent, since it may be the case that a previous call to
        // getProofFor connected a proof from a proof generator as a child of
        // a ProofNode in the range of the map in CDProof. Thus, this ensures
        // we don't touch such proofs.
        Trace("lazy-cdproof") << "...skip unowned proof" << std::endl;
      }
      else if (cur->getRule() == PfRule::ASSUME)
      {
        bool isSym = false;
        ProofGenerator* pg = getGeneratorFor(cfact, isSym);
        if (pg != nullptr)
        {
          Trace("lazy-cdproof")
              << "LazyCDProof: Call generator " << pg->identify()
              << " for assumption " << cfact << std::endl;
          Node cfactGen = isSym ? CDProof::getSymmFact(cfact) : cfact;
          Assert(!cfactGen.isNull());
          // Do not use the addProofTo interface, instead use the update node
          // interface, since this ensures that we don't take ownership for
          // the current proof. Instead, it is only linked, and ignored on
          // future calls to getProofFor due to the check above.
          std::shared_ptr<ProofNode> pgc = pg->getProofFor(cfactGen);
          // If the proof was null, then the update is not performed. This is
          // not considered an error, since this behavior is equivalent to
          // if pg had provided the proof (ASSUME cfactGen). Ensuring the
          // proper behavior wrt closed proofs should be done outside this
          // method.
          if (pgc != nullptr)
          {
            Trace("lazy-cdproof-gen")
                << "LazyCDProof: stored proof: " << *pgc.get() << std::endl;

            if (isSym)
            {
              if (pgc->getRule() == PfRule::SYMM)
              {
                getManager()->updateNode(cur, pgc->getChildren()[0].get());
              }
              else
              {
                getManager()->updateNode(cur, PfRule::SYMM, {pgc}, {});
              }
            }
            else
            {
              getManager()->updateNode(cur, pgc.get());
            }
            Trace("lazy-cdproof") << "LazyCDProof: Successfully added fact for "
                                  << cfactGen << std::endl;
          }
        }
        else
        {
          Trace("lazy-cdproof") << "LazyCDProof: " << identify()
                                << " : No generator for " << cfact << std::endl;
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
  Assert(opf->getResult() == fact);
  return opf;
}

void LazyCDProof::addLazyStep(Node expected,
                              ProofGenerator* pg,
                              PfRule idNull,
                              bool isClosed,
                              const char* ctx,
                              bool forceOverwrite)
{
  if (pg == nullptr)
  {
    // null generator, should have given a proof rule
    if (idNull == PfRule::ASSUME)
    {
      Unreachable() << "LazyCDProof::addLazyStep: " << identify()
                    << ": failed to provide proof generator for " << expected;
      return;
    }
    Trace("lazy-cdproof") << "LazyCDProof::addLazyStep: " << expected
                          << " set (trusted) step " << idNull << "\n";
    addStep(expected, idNull, {}, {expected});
    return;
  }
  Trace("lazy-cdproof") << "LazyCDProof::addLazyStep: " << expected
                        << " set to generator " << pg->identify() << "\n";
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
  // debug checking
  if (isClosed)
  {
    Trace("lazy-cdproof-debug") << "Checking closed..." << std::endl;
    pfgEnsureClosed(options(), expected, pg, "lazy-cdproof-debug", ctx);
  }
}

ProofGenerator* LazyCDProof::getGeneratorFor(Node fact, bool& isSym)
{
  isSym = false;
  NodeProofGeneratorMap::const_iterator it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return (*it).second;
  }
  if (d_autoSymm)
  {
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

}  // namespace cvc5::internal
