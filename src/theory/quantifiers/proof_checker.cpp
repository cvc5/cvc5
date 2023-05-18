/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

void QuantifiersProofRuleChecker::registerTo(ProofChecker* pc)
{
  // add checkers
  pc->registerChecker(PfRule::SKOLEM_INTRO, this);
  pc->registerChecker(PfRule::SKOLEMIZE, this);
  pc->registerChecker(PfRule::INSTANTIATE, this);
  pc->registerChecker(PfRule::ALPHA_EQUIV, this);
  // trusted rules
  pc->registerTrustedChecker(PfRule::QUANTIFIERS_PREPROCESS, this, 3);
}

Node QuantifiersProofRuleChecker::checkInternal(
    PfRule id, const std::vector<Node>& children, const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  if (id == PfRule::SKOLEM_INTRO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = SkolemManager::getUnpurifiedForm(args[0]);
    return args[0].eqNode(t);
  }
  else if (id == PfRule::SKOLEMIZE)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    // can use either negated FORALL or EXISTS
    if (children[0].getKind() != EXISTS
        && (children[0].getKind() != NOT || children[0][0].getKind() != FORALL))
    {
      return Node::null();
    }
    Node exists;
    if (children[0].getKind() == EXISTS)
    {
      exists = children[0];
    }
    else
    {
      std::vector<Node> echildren(children[0][0].begin(), children[0][0].end());
      echildren[1] = echildren[1].notNode();
      exists = nm->mkNode(EXISTS, echildren);
    }
    std::vector<Node> vars(exists[0].begin(), exists[0].end());
    std::vector<Node> skolems = Skolemize::getSkolemConstants(exists);
    Node res = exists[1].substitute(
        vars.begin(), vars.end(), skolems.begin(), skolems.end());
    return res;
  }
  else if (id == PfRule::INSTANTIATE)
  {
    Assert(children.size() == 1);
    // note we may have more arguments than just the term vector
    if (children[0].getKind() != FORALL
        || args.size() < children[0][0].getNumChildren())
    {
      return Node::null();
    }
    Node body = children[0][1];
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (size_t i = 0, nc = children[0][0].getNumChildren(); i < nc; i++)
    {
      vars.push_back(children[0][0][i]);
      subs.push_back(args[i]);
    }
    Node inst =
        body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    return inst;
  }
  else if (id == PfRule::ALPHA_EQUIV)
  {
    Assert(children.empty());
    if (args[0].getKind() != kind::FORALL)
    {
      return Node::null();
    }
    // arguments must be equalities that are bound variables that are
    // pairwise unique
    std::unordered_set<Node> allVars[2];
    std::vector<Node> vars;
    std::vector<Node> newVars;
    for (size_t i = 1, nargs = args.size(); i < nargs; i++)
    {
      if (args[i].getKind() != kind::EQUAL)
      {
        return Node::null();
      }
      for (size_t j = 0; j < 2; j++)
      {
        Node v = args[i][j];
        if (v.getKind() != kind::BOUND_VARIABLE
            || allVars[j].find(v) != allVars[j].end())
        {
          return Node::null();
        }
        allVars[j].insert(v);
      }
      vars.push_back(args[i][0]);
      newVars.push_back(args[i][1]);
    }
    Node renamedBody = args[0].substitute(
        vars.begin(), vars.end(), newVars.begin(), newVars.end());
    return args[0].eqNode(renamedBody);
  }
  else if (id == PfRule::QUANTIFIERS_PREPROCESS)
  {
    Assert(!args.empty());
    Assert(args[0].getType().isBoolean());
    return args[0];
  }

  // no rule
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
