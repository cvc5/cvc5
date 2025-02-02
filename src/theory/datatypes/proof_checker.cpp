/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

DatatypesProofRuleChecker::DatatypesProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void DatatypesProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::DT_SPLIT, this);
  pc->registerChecker(ProofRule::DT_CLASH, this);
}

Node DatatypesProofRuleChecker::checkInternal(ProofRule id,
                                              const std::vector<Node>& children,
                                              const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (id == ProofRule::DT_SPLIT)
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
