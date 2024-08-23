/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory UF rewriter
 */

#include "theory/uf/theory_uf_rewriter.h"

#include "expr/elim_shadow_converter.h"
#include "expr/function_array_const.h"
#include "expr/node_algorithm.h"
#include "theory/arith/arith_utilities.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/uf/function_const.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

TheoryUfRewriter::TheoryUfRewriter(NodeManager* nm, Rewriter* rr)
    : TheoryRewriter(nm), d_rr(rr)
{
  registerProofRewriteRule(ProofRewriteRule::BETA_REDUCE,
                           TheoryRewriteCtx::PRE_DSL);
}

RewriteResponse TheoryUfRewriter::postRewrite(TNode node)
{
  Kind k = node.getKind();
  if (k == Kind::EQUAL)
  {
    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      // uninterpreted constants are all distinct
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(false));
    }
    if (node[0] > node[1])
    {
      Node newNode = nodeManager()->mkNode(k, node[1], node[0]);
      return RewriteResponse(REWRITE_DONE, newNode);
    }
  }
  if (k == Kind::APPLY_UF)
  {
    Node lambda = FunctionConst::toLambda(node.getOperator());
    if (!lambda.isNull())
    {
      // Note that the rewriter does not rewrite inside of operators, so the
      // lambda we receive here may not be in rewritten form, and thus may
      // contain variable shadowing. We rewrite the operator explicitly here.
      Node lambdaRew = d_rr->rewrite(lambda);
      // We compare against the original operator, if it is different, then
      // we rewrite again.
      if (lambdaRew != node.getOperator())
      {
        std::vector<TNode> args;
        args.push_back(lambdaRew);
        args.insert(args.end(), node.begin(), node.end());
        NodeManager* nm = NodeManager::currentNM();
        Node ret = nm->mkNode(Kind::APPLY_UF, args);
        Assert(ret != node);
        return RewriteResponse(REWRITE_AGAIN_FULL, ret);
      }
      Trace("uf-ho-beta") << "uf-ho-beta : beta-reducing all args of : "
                          << lambda << " for " << node << "\n";
      std::vector<TNode> vars(lambda[0].begin(), lambda[0].end());
      std::vector<TNode> subs(node.begin(), node.end());
      std::unordered_set<Node> fvs;
      for (TNode s : subs)
      {
        expr::getFreeVariables(s, fvs);
      }
      Node new_body = lambda[1];
      Trace("uf-ho-beta") << "... body is " << new_body << std::endl;
      if (!fvs.empty())
      {
        ElimShadowNodeConverter esnc(nodeManager(), node, fvs);
        new_body = esnc.convert(new_body);
        Trace("uf-ho-beta")
            << "... elim shadow body is " << new_body << std::endl;
      }
      else
      {
        Trace("uf-ho-beta") << "... no free vars in substitution for " << vars
                            << " -> " << subs << std::endl;
      }
      Node ret = new_body.substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());

      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    if (!canUseAsApplyUfOperator(node.getOperator()))
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, getHoApplyForApplyUf(node));
    }
  }
  else if (k == Kind::HO_APPLY)
  {
    Node lambda = FunctionConst::toLambda(node[0]);
    if (!lambda.isNull())
    {
      // resolve one argument of the lambda
      Trace("uf-ho-beta") << "uf-ho-beta : beta-reducing one argument of : "
                          << lambda << " with " << node[1] << "\n";

      // reconstruct the lambda first to avoid variable shadowing
      Node new_body = lambda[1];
      if (lambda[0].getNumChildren() > 1)
      {
        std::vector<Node> new_vars(lambda[0].begin() + 1, lambda[0].end());
        std::vector<Node> largs;
        largs.push_back(nodeManager()->mkNode(Kind::BOUND_VAR_LIST, new_vars));
        largs.push_back(new_body);
        new_body = nodeManager()->mkNode(Kind::LAMBDA, largs);
        Trace("uf-ho-beta")
            << "uf-ho-beta : ....new lambda : " << new_body << "\n";
      }

      TNode arg = node[1];
      std::unordered_set<Node> fvs;
      expr::getFreeVariables(arg, fvs);
      if (!fvs.empty())
      {
        ElimShadowNodeConverter esnc(nodeManager(), node, fvs);
        new_body = esnc.convert(new_body);
      }
      TNode var = lambda[0][0];
      new_body = new_body.substitute(var, arg);
      Trace("uf-ho-beta") << "uf-ho-beta : ..new body : " << new_body << "\n";
      return RewriteResponse(REWRITE_AGAIN_FULL, new_body);
    }
  }
  else if (k == Kind::LAMBDA)
  {
    Node ret = rewriteLambda(node);
    if (ret != node)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }
  else if (k == Kind::BITVECTOR_TO_NAT)
  {
    return rewriteBVToNat(node);
  }
  else if (k == Kind::INT_TO_BITVECTOR)
  {
    return rewriteIntToBV(node);
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryUfRewriter::preRewrite(TNode node)
{
  if (node.getKind() == Kind::EQUAL)
  {
    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      // uninterpreted constants are all distinct
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(false));
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}

Node TheoryUfRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::BETA_REDUCE:
    {
      if (n.getKind() != Kind::APPLY_UF
          || n.getOperator().getKind() != Kind::LAMBDA)
      {
        return Node::null();
      }
      Node lambda = n.getOperator();
      std::vector<TNode> vars(lambda[0].begin(), lambda[0].end());
      std::vector<TNode> subs(n.begin(), n.end());
      if (vars.size() != subs.size())
      {
        return Node::null();
      }
      // Note that we do not check for variable shadowing in the lambda here.
      // This rule will only be used to express valid instances of beta
      // reduction. If a beta reduction had to eliminate shadowing, then it
      // will not be inferred by this rule as is.
      Node ret = lambda[1].substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
      return ret;
    }
    break;
    default: break;
  }
  return Node::null();
}

Node TheoryUfRewriter::getHoApplyForApplyUf(TNode n)
{
  Assert(n.getKind() == Kind::APPLY_UF);
  Node curr = n.getOperator();
  for (unsigned i = 0; i < n.getNumChildren(); i++)
  {
    curr = NodeManager::currentNM()->mkNode(Kind::HO_APPLY, curr, n[i]);
  }
  return curr;
}
Node TheoryUfRewriter::getApplyUfForHoApply(TNode n)
{
  std::vector<TNode> children;
  TNode curr = decomposeHoApply(n, children, true);
  // if operator is standard
  if (canUseAsApplyUfOperator(curr))
  {
    return NodeManager::currentNM()->mkNode(Kind::APPLY_UF, children);
  }
  // cannot construct APPLY_UF if operator is partially applied or is not
  // standard
  return Node::null();
}
Node TheoryUfRewriter::decomposeHoApply(TNode n,
                                        std::vector<TNode>& args,
                                        bool opInArgs)
{
  TNode curr = n;
  while (curr.getKind() == Kind::HO_APPLY)
  {
    args.push_back(curr[1]);
    curr = curr[0];
  }
  if (opInArgs)
  {
    args.push_back(curr);
  }
  std::reverse(args.begin(), args.end());
  return curr;
}
bool TheoryUfRewriter::canUseAsApplyUfOperator(TNode n) { return n.isVar(); }

Node TheoryUfRewriter::rewriteLambda(Node node)
{
  Assert(node.getKind() == Kind::LAMBDA);
  // The following code ensures that if node is equivalent to a constant
  // lambda, then we return the canonical representation for the lambda, which
  // in turn ensures that two constant lambdas are equivalent if and only
  // if they are the same node.
  // We canonicalize lambdas by turning them into array constants, applying
  // normalization on array constants, and then converting the array constant
  // back to a lambda.
  Trace("builtin-rewrite") << "Rewriting lambda " << node << "..." << std::endl;
  // eliminate shadowing, prior to handling whether the lambda is constant
  // below.
  Node retElimShadow = ElimShadowNodeConverter::eliminateShadow(node);
  if (retElimShadow != node)
  {
    return retElimShadow;
  }
  Node anode = FunctionConst::toArrayConst(node);
  // Only rewrite constant array nodes, since these are the only cases
  // where we require canonicalization of lambdas. Moreover, applying the
  // below code is not correct if the arguments to the lambda occur
  // in return values. For example, lambda x. ite( x=1, f(x), c ) would
  // be converted to (store (storeall ... c) 1 f(x)), and then converted
  // to lambda y. ite( y=1, f(x), c), losing the relation between x and y.
  if (!anode.isNull() && anode.isConst())
  {
    Assert(anode.getType().isArray());
    Node retNode =
        nodeManager()->mkConst(FunctionArrayConst(node.getType(), anode));
    Assert(anode.isConst() == retNode.isConst());
    Assert(retNode.getType() == node.getType());
    Assert(expr::hasFreeVar(node) == expr::hasFreeVar(retNode));
    return retNode;
  }
  Trace("builtin-rewrite-debug")
      << "...failed to get array representation." << std::endl;
  // see if it can be eliminated, (lambda ((x T)) (f x)) ---> f
  if (node[1].getKind() == Kind::APPLY_UF)
  {
    size_t nvar = node[0].getNumChildren();
    if (node[1].getNumChildren() == nvar)
    {
      bool matchesList = true;
      for (size_t i = 0; i < nvar; i++)
      {
        if (node[0][i] != node[1][i])
        {
          matchesList = false;
          break;
        }
      }
      if (matchesList)
      {
        return node[1].getOperator();
      }
    }
  }
  return node;
}

RewriteResponse TheoryUfRewriter::rewriteBVToNat(TNode node)
{
  Assert(node.getKind() == Kind::BITVECTOR_TO_NAT);
  NodeManager* nm = nodeManager();
  if (node[0].isConst())
  {
    Node resultNode = nm->mkConstInt(node[0].getConst<BitVector>().toInteger());
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }
  else if (node[0].getKind() == Kind::INT_TO_BITVECTOR)
  {
    // (bv2nat ((_ int2bv w) x)) ----> (mod x 2^w)
    const uint32_t size =
        node[0].getOperator().getConst<IntToBitVector>().d_size;
    Node sn = nm->mkConstInt(Rational(Integer(2).pow(size)));
    Node resultNode = nm->mkNode(Kind::INTS_MODULUS_TOTAL, node[0][0], sn);
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryUfRewriter::rewriteIntToBV(TNode node)
{
  Assert(node.getKind() == Kind::INT_TO_BITVECTOR);
  if (node[0].isConst())
  {
    NodeManager* nm = nodeManager();
    const uint32_t size = node.getOperator().getConst<IntToBitVector>().d_size;
    Node resultNode = nm->mkConst(
        BitVector(size, node[0].getConst<Rational>().getNumerator()));
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }
  else if (node[0].getKind() == Kind::BITVECTOR_TO_NAT)
  {
    TypeNode otype = node.getType();
    TypeNode itype = node[0][0].getType();
    if (otype == itype)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, node[0][0]);
    }
    size_t osize = otype.getBitVectorSize();
    size_t isize = itype.getBitVectorSize();
    if (osize > isize)
    {
      // ((_ int2bv w) (bv2nat x)) ---> (concat (_ bv0 v) x)
      Node zero = bv::utils::mkZero(osize - isize);
      Node concat =
          nodeManager()->mkNode(Kind::BITVECTOR_CONCAT, zero, node[0][0]);
      return RewriteResponse(REWRITE_AGAIN_FULL, concat);
    }
    else
    {
      // ((_ int2bv w) (bv2nat x)) ---> ((_ extract w-1 0) x)
      Assert(osize < isize);
      Node extract = bv::utils::mkExtract(node[0][0], osize-1, 0);
      return RewriteResponse(REWRITE_AGAIN_FULL, extract);
    }
  }
  return RewriteResponse(REWRITE_DONE, node);
}
}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
