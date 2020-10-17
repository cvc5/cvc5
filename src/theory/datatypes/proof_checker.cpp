/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of datatypes proof checker
 **/

#include "theory/datatypes/proof_checker.h"

#include "theory/datatypes/theory_datatypes_utils.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

void DatatypesProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::DT_UNIF, this);
  pc->registerChecker(PfRule::DT_INST, this);
  pc->registerChecker(PfRule::DT_SPLIT, this);
  pc->registerChecker(PfRule::DT_CLASH, this);
  // trusted rules
  pc->registerTrustedChecker(PfRule::DT_TRUST, this, 2);
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
        || children[0][0][0].getOperator() != children[0][1].getOperator()
        || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    return children[0][0][i].eqNode(children[0][1][i]);
  }
  else if (id == PfRule::DT_INST)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    if (children[0].getKind() != kind::APPLY_TESTER)
    {
      return Node::null();
    }
    size_t i = utils::indexOf(children[0].getOperator());
    Node t = children[0][0];
    const DType& dt = t.getType().getDType();
    Node ticons = utils::getInstCons(t, dt, i);
    return t.eqNode(ticons);
  }
  else if (id == PfRule::DT_SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    TypeNode t = args[0].getType();
    if (!t.isDatatype())
    {
      return Node::null();
    }
    const DType& dt = t.getDType();
    return utils::mkSplit(args[0], dt);
  }
  else if (id == PfRule::DT_CLASH)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[0].getKind() != kind::APPLY_TESTER
        || children[1].getKind() != kind::APPLY_TESTER
               || children[0][0] != children[1][0]
               || children[0] == children[1])
    {
      return Node::null();
    }
    return nm->mkConst(false);
  }
  else if (id == PfRule::DT_TRUST)
  {
    Assert(!args.empty());
    Assert(args[0].getType().isBoolean());
    return args[0];
  }
  // no rule
  return Node::null();
}

}  // namespace datatypes
}  // namespace theory
}  // namespace CVC4
