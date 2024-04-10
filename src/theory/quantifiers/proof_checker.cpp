/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of quantifiers proof checker.
 */

#include "theory/quantifiers/proof_checker.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "theory/builtin/proof_checker.h"
#include "theory/quantifiers/skolemize.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersProofRuleChecker::QuantifiersProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void QuantifiersProofRuleChecker::registerTo(ProofChecker* pc)
{
  // add checkers
  pc->registerChecker(ProofRule::SKOLEM_INTRO, this);
  pc->registerChecker(ProofRule::SKOLEMIZE, this);
  pc->registerChecker(ProofRule::INSTANTIATE, this);
  pc->registerChecker(ProofRule::ALPHA_EQUIV, this);
}

Node QuantifiersProofRuleChecker::checkInternal(
    ProofRule id,
    const std::vector<Node>& children,
    const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (id == ProofRule::SKOLEM_INTRO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = SkolemManager::getUnpurifiedForm(args[0]);
    return args[0].eqNode(t);
  }
  else if (id == ProofRule::SKOLEMIZE)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    // can use either negated FORALL or EXISTS
    if (children[0].getKind() != Kind::EXISTS
        && (children[0].getKind() != Kind::NOT
            || children[0][0].getKind() != Kind::FORALL))
    {
      return Node::null();
    }
    Node exists;
    if (children[0].getKind() == Kind::EXISTS)
    {
      exists = children[0];
    }
    else
    {
      std::vector<Node> echildren(children[0][0].begin(), children[0][0].end());
      echildren[1] = echildren[1].notNode();
      exists = nm->mkNode(Kind::EXISTS, echildren);
    }
    std::vector<Node> vars(exists[0].begin(), exists[0].end());
    std::vector<Node> skolems = Skolemize::getSkolemConstants(exists);
    Node res = exists[1].substitute(
        vars.begin(), vars.end(), skolems.begin(), skolems.end());
    return res;
  }
  else if (id == ProofRule::INSTANTIATE)
  {
    Assert(children.size() == 1);
    // note we may have more arguments than just the term vector
    if (children[0].getKind() != Kind::FORALL || args.empty())
    {
      return Node::null();
    }
    Node body = children[0][1];
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (size_t i = 0, nc = children[0][0].getNumChildren(); i < nc; i++)
    {
      vars.push_back(children[0][0][i]);
      subs.push_back(args[0][i]);
    }
    Node inst =
        body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    return inst;
  }
  else if (id == ProofRule::ALPHA_EQUIV)
  {
    Assert(children.empty());
    Assert(args.size() == 3);
    // must be lists of the same length
    if (args[1].getKind() != Kind::SEXPR || args[2].getKind() != Kind::SEXPR
        || args[1].getNumChildren() != args[2].getNumChildren())
    {
      return Node::null();
    }
    // arguments must be lists of bound variables that are pairwise unique
    std::unordered_set<Node> allVars[2];
    std::vector<Node> vars;
    std::vector<Node> newVars;
    for (size_t i = 0, nargs = args[1].getNumChildren(); i < nargs; i++)
    {
      for (size_t j = 1; j <= 2; j++)
      {
        Node v = args[j][i];
        std::unordered_set<Node>& av = allVars[j - 1];
        if (v.getKind() != Kind::BOUND_VARIABLE || av.find(v) != av.end())
        {
          return Node::null();
        }
        av.insert(v);
      }
      vars.push_back(args[1][i]);
      newVars.push_back(args[2][i]);
    }
    Node renamedBody = args[0].substitute(
        vars.begin(), vars.end(), newVars.begin(), newVars.end());
    return args[0].eqNode(renamedBody);
  }

  // no rule
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
