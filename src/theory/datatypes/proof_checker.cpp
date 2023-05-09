/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of datatypes proof checker.
 */

#include "theory/datatypes/proof_checker.h"

#include "expr/dtype_cons.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {

void DatatypesProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::DT_UNIF, this);
  pc->registerChecker(PfRule::DT_INST, this);
  pc->registerChecker(PfRule::DT_COLLAPSE, this);
  pc->registerChecker(PfRule::DT_SPLIT, this);
  pc->registerChecker(PfRule::DT_CLASH, this);
}

Node DatatypesProofRuleChecker::checkInternal(PfRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  if (id == PfRule::DT_UNIF)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != kind::EQUAL
        || children[0][0].getKind() != kind::APPLY_CONSTRUCTOR
        || children[0][1].getKind() != kind::APPLY_CONSTRUCTOR
        || children[0][0].getOperator() != children[0][1].getOperator()
        || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0][0].getNumChildren())
    {
      return Node::null();
    }
    Assert(children[0][0].getNumChildren() == children[0][1].getNumChildren());
    return children[0][0][i].eqNode(children[0][1][i]);
  }
  else if (id == PfRule::DT_INST)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Node t = args[0];
    TypeNode tn = t.getType();
    uint32_t i;
    if (!tn.isDatatype() || !getUInt32(args[1], i))
    {
      return Node::null();
    }
    const DType& dt = tn.getDType();
    if (i >= dt.getNumConstructors())
    {
      return Node::null();
    }
    Node tester = utils::mkTester(t, i, dt);
    Node ticons = utils::getInstCons(t, dt, i, d_sharedSel);
    return tester.eqNode(t.eqNode(ticons));
  }
  else if (id == PfRule::DT_COLLAPSE)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = args[0];
    if (t.getKind() != kind::APPLY_SELECTOR
        || t[0].getKind() != kind::APPLY_CONSTRUCTOR)
    {
      return Node::null();
    }
    Node selector = t.getOperator();
    size_t constructorIndex = utils::indexOf(t[0].getOperator());
    const DType& dt = utils::datatypeOf(selector);
    const DTypeConstructor& dtc = dt[constructorIndex];
    int selectorIndex = dtc.getSelectorIndexInternal(selector);
    Node r =
        selectorIndex < 0 ? nm->mkGroundTerm(t.getType()) : t[0][selectorIndex];
    return t.eqNode(r);
  }
  else if (id == PfRule::DT_SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    TypeNode tn = args[0].getType();
    if (!tn.isDatatype())
    {
      return Node::null();
    }
    const DType& dt = tn.getDType();
    return utils::mkSplit(args[0], dt);
  }
  else if (id == PfRule::DT_CLASH)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[0].getKind() != kind::APPLY_TESTER
        || children[1].getKind() != kind::APPLY_TESTER
        || children[0][0] != children[1][0] || children[0] == children[1])
    {
      return Node::null();
    }
    return nm->mkConst(false);
  }
  // no rule
  return Node::null();
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
