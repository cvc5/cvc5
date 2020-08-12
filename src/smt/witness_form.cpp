/*********************                                                        */
/*! \file witness_form.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for managing witness form conversion in proofs
 **/

#include "smt/witness_form.h"

#include "expr/skolem_manager.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace smt {

WitnessFormGenerator::WitnessFormGenerator(ProofNodeManager* pnm)
    : d_tcpg(pnm,
             nullptr,
             TConvPolicy::FIXPOINT,
             TConvCachePolicy::NEVER,
             "WfGenerator::TConvProofGenerator"),
      d_wintroPf(pnm, nullptr, nullptr, "WfGenerator::LazyCDProof")
{
}

std::shared_ptr<ProofNode> WitnessFormGenerator::getProofFor(Node eq)
{
  if (eq.getKind() != kind::EQUAL)
  {
    // expecting an equality
    return nullptr;
  }
  Node lhs = eq[0];
  Node rhs = convertToWitnessForm(eq[0]);
  if (rhs != eq[1])
  {
    // expecting witness form
    return nullptr;
  }
  std::shared_ptr<ProofNode> pn = d_tcpg.getProofFor(eq);
  Assert(pn != nullptr);
  return pn;
}

std::string WitnessFormGenerator::identify() const
{
  return "WitnessFormGenerator";
}

Node WitnessFormGenerator::convertToWitnessForm(Node t)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* skm = nm->getSkolemManager();
  Node tw = SkolemManager::getWitnessForm(t);
  if (t == tw)
  {
    // trivial case
    return tw;
  }
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  TNode curw;
  visit.push_back(t);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_visited.find(cur);
    if (it == d_visited.end())
    {
      d_visited.insert(cur);
      curw = SkolemManager::getWitnessForm(cur);
      // if its witness form is different
      if (cur != curw)
      {
        if (cur.isVar())
        {
          Node eq = cur.eqNode(curw);
          // equality between a variable and its witness form
          d_eqs.insert(eq);
          Assert(curw.getKind() == kind::WITNESS);
          Node skBody = SkolemManager::getSkolemForm(curw[1]);
          Node exists = nm->mkNode(kind::EXISTS, curw[0], skBody);
          ProofGenerator* pg = skm->getProofGenerator(exists);
          // --------------------------- from pg
          // (exists ((x T)) (P x))
          // --------------------------- WITNESS_INTRO
          // k = (witness ((x T)) (P x))
          d_wintroPf.addLazyStep(
              exists,
              pg,
              true,
              "WitnessFormGenerator::convertToWitnessForm:witness_axiom",
              false,
              PfRule::WITNESS_AXIOM);
          d_wintroPf.addStep(eq, PfRule::WITNESS_INTRO, {exists}, {});
          d_tcpg.addRewriteStep(cur, curw, &d_wintroPf);
        }
        else
        {
          // A term whose witness form is different from itself, recurse.
          // It should be the case that cur has children, since the witness
          // form of constants are themselves.
          Assert(cur.getNumChildren() > 0);
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    }
  } while (!visit.empty());
  return tw;
}

bool WitnessFormGenerator::requiresWitnessFormTransform(Node t, Node s) const
{
  return theory::Rewriter::rewrite(t) != theory::Rewriter::rewrite(s);
}

bool WitnessFormGenerator::requiresWitnessFormIntro(Node t) const
{
  Node tr = theory::Rewriter::rewrite(t);
  return !tr.isConst() || !tr.getConst<bool>();
}

const std::unordered_set<Node, NodeHashFunction>&
WitnessFormGenerator::getWitnessFormEqs() const
{
  return d_eqs;
}

}  // namespace smt
}  // namespace CVC4
