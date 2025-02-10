/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Diamonds proof generator utility.
 */

#include "theory/uf/diamonds_proof_generator.h"

#include "proof/proof.h"

namespace cvc5::internal {

DiamondsProofGenerator::DiamondsProofGenerator(Env& env) : EnvObj(env) {}

DiamondsProofGenerator::~DiamondsProofGenerator() {}

void DiamondsProofGenerator::ppStaticLearn(TNode n,
                                           std::vector<TrustNode>& learned)
{
  std::vector<TNode> workList;
  workList.push_back(n);
  std::unordered_set<TNode> processed;

  while (!workList.empty())
  {
    n = workList.back();

    if (n.isClosure())
    {
      // unsafe to go under quantifiers; we might pull bound vars out of scope!
      processed.insert(n);
      workList.pop_back();
      continue;
    }

    bool unprocessedChildren = false;
    for (TNode::iterator i = n.begin(), iend = n.end(); i != iend; ++i)
    {
      if (processed.find(*i) == processed.end())
      {
        // unprocessed child
        workList.push_back(*i);
        unprocessedChildren = true;
      }
    }

    if (unprocessedChildren)
    {
      continue;
    }

    workList.pop_back();
    // has node n been processed in the meantime ?
    if (processed.find(n) != processed.end())
    {
      continue;
    }
    processed.insert(n);

    // == DIAMONDS ==

    Trace("diamonds") << "===================== looking at" << std::endl
                      << n << std::endl;

    // binary OR of binary ANDs of EQUALities
    if (n.getKind() == Kind::OR && n.getNumChildren() == 2
        && n[0].getKind() == Kind::AND && n[0].getNumChildren() == 2
        && n[1].getKind() == Kind::AND && n[1].getNumChildren() == 2
        && (n[0][0].getKind() == Kind::EQUAL)
        && (n[0][1].getKind() == Kind::EQUAL)
        && (n[1][0].getKind() == Kind::EQUAL)
        && (n[1][1].getKind() == Kind::EQUAL))
    {
      // now we have (a = b && c = d) || (e = f && g = h)

      Trace("diamonds") << "has form of a diamond!" << std::endl;

      TNode a = n[0][0][0], b = n[0][0][1], c = n[0][1][0], d = n[0][1][1],
            e = n[1][0][0], f = n[1][0][1], g = n[1][1][0], h = n[1][1][1];

      // test that one of {a, b} = one of {c, d}, and make "b" the
      // shared node (i.e. put in the form (a = b && b = d))
      // note we don't actually care about the shared ones, so the
      // "swaps" below are one-sided, ignoring b and c
      if (a == c)
      {
        a = b;
      }
      else if (a == d)
      {
        a = b;
        d = c;
      }
      else if (b == c)
      {
        // nothing to do
      }
      else if (b == d)
      {
        d = c;
      }
      else
      {
        // condition not satisfied
        Trace("diamonds") << "+ A fails" << std::endl;
        continue;
      }

      Trace("diamonds") << "+ A holds" << std::endl;

      // same: one of {e, f} = one of {g, h}, and make "f" the
      // shared node (i.e. put in the form (e = f && f = h))
      if (e == g)
      {
        e = f;
      }
      else if (e == h)
      {
        e = f;
        h = g;
      }
      else if (f == g)
      {
        // nothing to do
      }
      else if (f == h)
      {
        h = g;
      }
      else
      {
        // condition not satisfied
        Trace("diamonds") << "+ B fails" << std::endl;
        continue;
      }

      Trace("diamonds") << "+ B holds" << std::endl;

      // now we have (a = b && b = d) || (e = f && f = h)
      // test that {a, d} == {e, h}
      if ((a == e && d == h) || (a == h && d == e))
      {
        // learn: n implies a == d
        Trace("diamonds") << "+ C holds" << std::endl;
        Node newEquality = a.eqNode(d);
        Trace("diamonds") << "  ==> " << newEquality << std::endl;
        Node lem = n.impNode(newEquality);
        TrustNode trn = TrustNode::mkTrustLemma(lem, this);
        learned.emplace_back(trn);
      }
      else
      {
        Trace("diamonds") << "+ C fails" << std::endl;
      }
    }
  }
}

std::shared_ptr<ProofNode> DiamondsProofGenerator::getProofFor(Node fact)
{
  Trace("valid-witness") << "Prove " << fact << std::endl;
  // proofs not yet supported
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::DIAMONDS, {}, {});
  return cdp.getProofFor(fact);
}

std::string DiamondsProofGenerator::identify() const
{
  return "DiamondsProofGenerator";
}

}  // namespace cvc5::internal
