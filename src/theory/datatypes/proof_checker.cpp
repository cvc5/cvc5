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
 * Implementation of datatypes proof checker.
 */

#include "theory/datatypes/proof_checker.h"

#include "expr/dtype_cons.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace datatypes {

DatatypesProofRuleChecker::DatatypesProofRuleChecker(NodeManager* nm,
                                                     bool sharedSel)
    : ProofRuleChecker(nm), d_sharedSel(sharedSel)
{
}

void DatatypesProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::DT_UNIF, this);
  pc->registerChecker(ProofRule::DT_SPLIT, this);
  pc->registerChecker(ProofRule::DT_CLASH, this);
}

Node DatatypesProofRuleChecker::checkInternal(ProofRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (id == ProofRule::DT_UNIF)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != Kind::EQUAL
        || children[0][0].getKind() != Kind::APPLY_CONSTRUCTOR
        || children[0][1].getKind() != Kind::APPLY_CONSTRUCTOR
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
  else if (id == ProofRule::DT_SPLIT)
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
  else if (id == ProofRule::DT_CLASH)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[0].getKind() != Kind::APPLY_TESTER
        || children[1].getKind() != Kind::APPLY_TESTER
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
