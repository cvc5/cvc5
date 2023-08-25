/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/builtin/theory_builtin_rewriter.h"

#include <cmath>

#include "expr/attribute.h"
#include "expr/elim_shadow_converter.h"
#include "expr/node_algorithm.h"
#include "theory/builtin/generic_op.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace builtin {

Node TheoryBuiltinRewriter::blastDistinct(TNode in)
{
  Assert(in.getKind() == kind::DISTINCT);

  NodeManager* nm = NodeManager::currentNM();

  if (in[0].getType().isCardinalityLessThan(in.getNumChildren()))
  {
    // Cardinality of type does not allow to find distinct values for all
    // children of this node.
    return nm->mkConst<bool>(false);
  }

  if (in.getNumChildren() == 2)
  {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    return nm->mkNode(kind::NOT, nm->mkNode(kind::EQUAL, in[0], in[1]));
  }

  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = nm->mkNode(kind::EQUAL, *i, *j);
      Node neq = nm->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  return nm->mkNode(kind::AND, diseqs);
}

RewriteResponse TheoryBuiltinRewriter::postRewrite(TNode node) {
  // otherwise, do the default call
  return doRewrite(node);
}

RewriteResponse TheoryBuiltinRewriter::doRewrite(TNode node)
{
  switch (node.getKind())
  {
    case kind::WITNESS:
    {
      // it is important to run this rewriting at prerewrite and postrewrite,
      // since e.g. arithmetic rewrites equalities in ways that may make an
      // equality not in solved form syntactically, e.g. (= x (+ 1 a)) rewrites
      // to (= a (- x 1)), where x no longer is in solved form.
      Node rnode = rewriteWitness(node);
      return RewriteResponse(REWRITE_DONE, rnode);
    }
    case kind::DISTINCT:
      return RewriteResponse(REWRITE_DONE, blastDistinct(node));
    case kind::APPLY_INDEXED_SYMBOLIC:
    {
      Node rnode = rewriteApplyIndexedSymbolic(node);
      if (rnode != node)
      {
        return RewriteResponse(REWRITE_AGAIN_FULL, rnode);
      }
    }
    break;
    default: break;
  }
  return RewriteResponse(REWRITE_DONE, node);
}

Node TheoryBuiltinRewriter::rewriteWitness(TNode node)
{
  Assert(node.getKind() == kind::WITNESS);
  if (node[1].getKind() == kind::EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      // (witness ((x T)) (= x t)) ---> t
      if (node[1][i] == node[0][0])
      {
        Trace("builtin-rewrite") << "Witness rewrite: " << node << " --> "
                                 << node[1][1 - i] << std::endl;
        // also must be a legal elimination: the other side of the equality
        // cannot contain the variable, and it must be the same type as the
        // variable
        if (!expr::hasSubterm(node[1][1 - i], node[0][0])
            && node[1][i].getType() == node[0][0].getType())
        {
          return node[1][1 - i];
        }
      }
    }
  }
  else if (node[1] == node[0][0])
  {
    // (witness ((x Bool)) x) ---> true
    return NodeManager::currentNM()->mkConst(true);
  }
  else if (node[1].getKind() == kind::NOT && node[1][0] == node[0][0])
  {
    // (witness ((x Bool)) (not x)) ---> false
    return NodeManager::currentNM()->mkConst(false);
  }
  // eliminate shadowing
  return ElimShadowNodeConverter::eliminateShadow(node);
}

Node TheoryBuiltinRewriter::rewriteApplyIndexedSymbolic(TNode node)
{
  Assert(node.getKind() == kind::APPLY_INDEXED_SYMBOLIC);
  Assert(node.getNumChildren() > 1);
  // if all arguments are constant, we return the non-symbolic version
  // of the operator, e.g. (extract 2 1 #b0000) ---> ((_ extract 2 1) #b0000)
  for (const Node& nc : node)
  {
    if (!nc.isConst())
    {
      return node;
    }
  }
  Trace("builtin-rewrite") << "rewriteApplyIndexedSymbolic: " << node
                           << std::endl;
  // use the utility
  return GenericOp::getConcreteApp(node);
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal
