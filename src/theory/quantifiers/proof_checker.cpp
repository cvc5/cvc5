/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

void QuantifiersProofRuleChecker::registerTo(ProofChecker* pc)
{
  // add checkers
  pc->registerChecker(PfRule::SKOLEM_INTRO, this);
  pc->registerChecker(PfRule::EXISTS_INTRO, this);
  pc->registerChecker(PfRule::SKOLEMIZE, this);
  pc->registerChecker(PfRule::INSTANTIATE, this);
}

Node QuantifiersProofRuleChecker::checkInternal(
    PfRule id, const std::vector<Node>& children, const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // compute what was proven
  if (id == PfRule::EXISTS_INTRO)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    Node p = children[0];
    Node exists = args[0];
    if (exists.getKind() != kind::EXISTS || exists[0].getNumChildren() != 1)
    {
      return Node::null();
    }
    std::unordered_map<Node, Node> subs;
    if (!expr::match(exists[1], p, subs))
    {
      return Node::null();
    }
    // substitution must contain only the variable of the existential
    for (const std::pair<const Node, Node>& s : subs)
    {
      if (s.first != exists[0][0])
      {
        return Node::null();
      }
    }
    return exists;
  }
  else if (id == PfRule::SKOLEM_INTRO)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = SkolemManager::getOriginalForm(args[0]);
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
    std::vector<Node> skolems;
    Node res = sm->mkSkolemize(exists, skolems, "k");
    return res;
  }
  else if (id == PfRule::INSTANTIATE)
  {
    Assert(children.size() == 1);
    if (children[0].getKind() != FORALL
        || args.size() != children[0][0].getNumChildren())
    {
      return Node::null();
    }
    Node body = children[0][1];
    std::vector<Node> vars;
    std::vector<Node> subs;
    for (unsigned i = 0, nargs = args.size(); i < nargs; i++)
    {
      vars.push_back(children[0][0][i]);
      subs.push_back(args[i]);
    }
    Node inst =
        body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    return inst;
  }

  // no rule
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
