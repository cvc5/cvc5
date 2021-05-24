/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node utility.
 */

#include "expr/proof_node.h"

#include "expr/proof_node_algorithm.h"
#include "expr/proof_node_to_sexpr.h"

namespace cvc5 {

ProofNode::ProofNode(PfRule id,
                     const std::vector<std::shared_ptr<ProofNode>>& children,
                     const std::vector<Node>& args)
{
  setValue(id, children, args);
}

PfRule ProofNode::getRule() const { return d_rule; }

const std::vector<std::shared_ptr<ProofNode>>& ProofNode::getChildren() const
{
  return d_children;
}

const std::vector<Node>& ProofNode::getArguments() const { return d_args; }

Node ProofNode::getResult() const { return d_proven; }

bool ProofNode::isClosed()
{
  std::vector<Node> assumps;
  expr::getFreeAssumptions(this, assumps);
  return assumps.empty();
}

void ProofNode::setValue(
    PfRule id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  d_rule = id;
  d_children = children;
  d_args = args;
}

void ProofNode::printDebug(std::ostream& os) const
{
  // convert to sexpr and print
  ProofNodeToSExpr pnts;
  Node ps = pnts.convertToSExpr(this);
  os << ps;
}

std::ostream& operator<<(std::ostream& out, const ProofNode& pn)
{
  pn.printDebug(out);
  return out;
}

}  // namespace cvc5
