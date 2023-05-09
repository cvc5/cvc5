/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for managing witness form conversion in proofs.
 */

#include "smt/witness_form.h"

#include "expr/skolem_manager.h"
#include "smt/env.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace smt {

WitnessFormGenerator::WitnessFormGenerator(Env& env)
    : d_rewriter(env.getRewriter()),
      d_tcpg(env,
             nullptr,
             TConvPolicy::FIXPOINT,
             TConvCachePolicy::NEVER,
             "WfGenerator::TConvProofGenerator",
             nullptr,
             true),
      d_wintroPf(env, nullptr, nullptr, "WfGenerator::LazyCDProof"),
      d_pskPf(env, nullptr, "WfGenerator::PurifySkolemProof")
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
  Node tw = SkolemManager::getOriginalForm(t);
  if (t == tw)
  {
    // trivial case
    return tw;
  }
  std::unordered_set<Node>::iterator it;
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
      curw = SkolemManager::getOriginalForm(cur);
      // if its original form is different
      if (cur != curw)
      {
        if (cur.isVar())
        {
          curw = SkolemManager::getUnpurifiedForm(cur);
          Node eq = cur.eqNode(curw);
          // equality between a variable and its unpurified form
          d_eqs.insert(eq);
          // ------- SKOLEM_INTRO
          // k = t
          d_wintroPf.addStep(eq, PfRule::SKOLEM_INTRO, {}, {cur});
          d_tcpg.addRewriteStep(
              cur, curw, &d_wintroPf, true, PfRule::ASSUME, true);
          // recursively transform
          visit.push_back(curw);
        }
        else
        {
          // A term whose original form is different from itself, recurse.
          // It should be the case that cur has children, since the original
          // form of constants are themselves.
          Assert(cur.getNumChildren() > 0);
          if (cur.hasOperator())
          {
            visit.push_back(cur.getOperator());
          }
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    }
  } while (!visit.empty());
  return tw;
}

bool WitnessFormGenerator::requiresWitnessFormTransform(Node t, Node s) const
{
  return d_rewriter->rewrite(t) != d_rewriter->rewrite(s);
}

bool WitnessFormGenerator::requiresWitnessFormIntro(Node t) const
{
  Node tr = d_rewriter->rewrite(t);
  return !tr.isConst() || !tr.getConst<bool>();
}

const std::unordered_set<Node>& WitnessFormGenerator::getWitnessFormEqs() const
{
  return d_eqs;
}

}  // namespace smt
}  // namespace cvc5::internal
