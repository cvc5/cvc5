/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

TheoryUfRewriter::TheoryUfRewriter(NodeManager* nm) : TheoryRewriter(nm)
{
  registerProofRewriteRule(ProofRewriteRule::BETA_REDUCE,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::LAMBDA_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::UBV_TO_INT_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::INT_TO_BV_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID,
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
      // see if we need to eliminate shadowing
      Node nes =
          rewriteViaRule(ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID, node);
      if (!nes.isNull())
      {
        Trace("uf-ho-beta") << "uf-ho-beta : eliminate shadowing : " << nes
                            << " for " << node << "\n";
        return RewriteResponse(REWRITE_AGAIN_FULL, nes);
      }
      Trace("uf-ho-beta") << "uf-ho-beta : beta-reducing all args of : "
                          << lambda << " for " << node << "\n";
      std::vector<TNode> vars(lambda[0].begin(), lambda[0].end());
      std::vector<TNode> subs(node.begin(), node.end());
      Node new_body = lambda[1];
      Trace("uf-ho-beta") << "... body is " << new_body << std::endl;
      Node ret = new_body.substitute(
          vars.begin(), vars.end(), subs.begin(), subs.end());
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    // note that for sanity we ensure that partially applied APPLY_UF (those
    // with function return type) are rewritten here, although these should
    // in general be avoided e.g. during parsing.
    if (!canUseAsApplyUfOperator(node.getOperator())
        || node.getType().isFunction())
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

      // see if we need to eliminate shadowing
      Node nes =
          rewriteViaRule(ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID, node);
      if (!nes.isNull())
      {
        return RewriteResponse(REWRITE_AGAIN_FULL, nes);
      }

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
  else if (k == Kind::BITVECTOR_UBV_TO_INT)
  {
    return rewriteBVToInt(node);
  }
  else if (k == Kind::INT_TO_BITVECTOR)
  {
    return rewriteIntToBV(node);
  }
  else if (k == Kind::BITVECTOR_SBV_TO_INT)
  {
    NodeManager* nm = nodeManager();
    Node r = nm->mkNode(Kind::BITVECTOR_UBV_TO_INT, node[0]);
    const uint32_t size = node[0].getType().getBitVectorSize();
    Node ttm = nm->mkConstInt(Rational(Integer(2).pow(size)));
    Node ex = bv::utils::mkExtract(node[0], size - 1, size - 1);
    Node cond = nm->mkNode(Kind::EQUAL, ex, bv::utils::mkZero(nm, 1));
    Node rite = nm->mkNode(Kind::ITE, cond, r, nm->mkNode(Kind::SUB, r, ttm));
    return RewriteResponse(REWRITE_AGAIN_FULL, rite);
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
      Kind k = n.getKind();
      Node lambda;
      if (k == Kind::APPLY_UF)
      {
        lambda = uf::FunctionConst::toLambda(n.getOperator());
      }
      else if (k == Kind::HO_APPLY)
      {
        lambda = uf::FunctionConst::toLambda(n[0]);
      }
      if (lambda.isNull())
      {
        return Node::null();
      }
      std::vector<Node> vars;
      std::vector<Node> subs;
      Node body = lambda[1];
      if (k == Kind::APPLY_UF)
      {
        vars.insert(vars.end(), lambda[0].begin(), lambda[0].end());
        subs.insert(subs.end(), n.begin(), n.end());
        if (vars.size() != subs.size())
        {
          return Node::null();
        }
      }
      else
      {
        Assert(k == Kind::HO_APPLY);
        vars.push_back(lambda[0][0]);
        subs.push_back(n[1]);
        if (lambda[0].getNumChildren() > 1)
        {
          std::vector<Node> newVars(lambda[0].begin() + 1, lambda[0].end());
          Node bvl = d_nm->mkNode(Kind::BOUND_VAR_LIST, newVars);
          body = d_nm->mkNode(Kind::LAMBDA, bvl, body);
        }
      }
      // Note that we do not check for variable shadowing in the lambda here.
      // This rule will only be used to express valid instances of beta
      // reduction. If a beta reduction had to eliminate shadowing, then it
      // will not be inferred by this rule as is.
      Node ret =
          body.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      return ret;
    }
    break;
    case ProofRewriteRule::LAMBDA_ELIM:
    {
      if (n.getKind() == Kind::LAMBDA)
      {
        Node felim = canEliminateLambda(nodeManager(), n);
        if (!felim.isNull())
        {
          return felim;
        }
      }
    }
    break;
    case ProofRewriteRule::UBV_TO_INT_ELIM:
    {
      if (n.getKind() == Kind::BITVECTOR_UBV_TO_INT)
      {
        return arith::eliminateBv2Nat(n);
      }
    }
    break;
    case ProofRewriteRule::INT_TO_BV_ELIM:
    {
      if (n.getKind() == Kind::INT_TO_BITVECTOR)
      {
        return arith::eliminateInt2Bv(n);
      }
    }
    break;
    case ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID:
    {
      // This ensures we won't have variable capturing during beta reduction.
      // Examples of this rule:
      // (_ (lambda x. forall x. P(x)) a) ---> (_ (lambda y. forall x. P(x)) a).
      // (_ (lambda y. forall x. P(y)) (f x)) --->
      //   (_ (lambda y. forall z. P(y)) (f x)).
      // (_ (lambda y. forall xu. P(y, u)) (f x)) --->
      //   (_ (lambda y. forall zu. P(y, u)) (f x)).
      // (_ (lambda y. forall x. P(y) ^ forall x. Q(y)) (f x)) --->
      //   (_ (lambda y. forall u. P(y) ^ forall v. Q(y)) (f x)).
      Kind k = n.getKind();
      Node lambda;
      std::vector<TNode> args;
      NodeManager* nm = nodeManager();
      if (k == Kind::APPLY_UF)
      {
        lambda = uf::FunctionConst::toLambda(n.getOperator());
        args.insert(args.end(), n.begin(), n.end());
        // First, see if we need to eliminate shadowing in the lambda itself
        if (!lambda.isNull())
        {
          // We compare against the original lambda, if it is different, then
          // we use the version (lambdaElimS) where shadowing is eliminated.
          Node lambdaElimS = ElimShadowNodeConverter::eliminateShadow(lambda);
          // Note that a more comprehensive test here would be to check if the
          // lambda rewrites at all and convert to HO_APPLY for uniformity.
          // This is not necessary as we only need to be sure that the topmost
          // variables are not shadowed. Moreover, we avoid "value
          // normalization" for lambdas in first-order logics by allowing beta
          // reduction to apply to non-rewritten lambdas. This makes solving
          // and proofs more complex, as it rewrites user provided define-fun
          // in unintuitive ways e.g. lambda x. (or (= x 0) (= x 1)) -->
          // lambda x. (ite (and (= x 0) (= x 1)) true false).
          if (lambdaElimS != lambda)
          {
            std::vector<Node> newChildren;
            newChildren.push_back(lambdaElimS);
            newChildren.insert(newChildren.end(), n.begin(), n.end());
            return nm->mkNode(Kind::APPLY_UF, newChildren);
          }
        }
      }
      else if (k == Kind::HO_APPLY)
      {
        lambda = uf::FunctionConst::toLambda(n[0]);
        args.push_back(n[1]);
        // We assume lambda is rewritten, and thus a similar check is not
        // necessary.
      }
      if (lambda.isNull())
      {
        return Node::null();
      }
      Node body = lambda[1];
      if (k == Kind::HO_APPLY && lambda[0].getNumChildren() > 1)
      {
        // compute the partial beta reduction
        std::vector<Node> nvars(lambda[0].begin() + 1, lambda[0].end());
        std::vector<Node> largs;
        largs.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, nvars));
        largs.push_back(body);
        body = nm->mkNode(Kind::LAMBDA, largs);
      }
      // get the free variables of the arguments
      std::unordered_set<Node> fvs;
      for (TNode a : args)
      {
        expr::getFreeVariables(a, fvs);
      }
      // if any free variables, see if we need to eliminate shadowing in the
      // lambda.
      if (!fvs.empty())
      {
        ElimShadowNodeConverter esnc(nm, n, fvs);
        Node bodyc = esnc.convert(body);
        // if shadow elimination was necessary for the body of the lambda
        if (bodyc != body)
        {
          Node lambdac;
          if (k == Kind::HO_APPLY && lambda[0].getNumChildren() > 1)
          {
            // body was a partial beta reduction computed above, reconstruct
            // the original lambda.
            Assert(bodyc.getKind() == Kind::LAMBDA);
            std::vector<Node> nvars;
            nvars.push_back(lambda[0][0]);
            nvars.insert(nvars.end(), bodyc[0].begin(), bodyc[0].end());
            std::vector<Node> largs;
            largs.push_back(nm->mkNode(Kind::BOUND_VAR_LIST, nvars));
            largs.push_back(bodyc[1]);
            lambdac = nm->mkNode(Kind::LAMBDA, largs);
          }
          else
          {
            lambdac = nm->mkNode(Kind::LAMBDA, lambda[0], bodyc);
          }
          Assert(lambdac != lambda);
          std::vector<Node> aargs;
          aargs.push_back(lambdac);
          aargs.insert(aargs.end(), args.begin(), args.end());
          Node ret = nm->mkNode(k, aargs);
          Trace("uf-elim-shadow")
              << "Elim shadow " << n << " to " << ret << std::endl;
          return ret;
        }
      }
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
    curr = NodeManager::mkNode(Kind::HO_APPLY, curr, n[i]);
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
    return n.getNodeManager()->mkNode(Kind::APPLY_UF, children);
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
    Trace("builtin-rewrite") << "...rewrites to " << retElimShadow << std::endl;
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
  // we only do this if the resulting eliminated term is a variable
  Node felim = canEliminateLambda(nodeManager(), node);
  if (!felim.isNull() && felim.isVar())
  {
    return felim;
  }
  return node;
}

RewriteResponse TheoryUfRewriter::rewriteBVToInt(TNode node)
{
  Assert(node.getKind() == Kind::BITVECTOR_UBV_TO_INT);
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
  NodeManager* nm = nodeManager();
  if (node[0].isConst())
  {
    const uint32_t size = node.getOperator().getConst<IntToBitVector>().d_size;
    Node resultNode = nm->mkConst(
        BitVector(size, node[0].getConst<Rational>().getNumerator()));
    return RewriteResponse(REWRITE_AGAIN_FULL, resultNode);
  }
  else if (node[0].getKind() == Kind::BITVECTOR_UBV_TO_INT)
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
      Node zero = bv::utils::mkZero(nm, osize - isize);
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

Node TheoryUfRewriter::canEliminateLambda(NodeManager* nm, const Node& node)
{
  Assert(node.getKind() == Kind::LAMBDA);
  if (node[1].getKind() == Kind::APPLY_UF)
  {
    size_t nvar = node[0].getNumChildren();
    size_t nargs = node[1].getNumChildren();
    if (nargs >= nvar)
    {
      bool matchesList = true;
      for (size_t i = 0; i < nvar; i++)
      {
        if (node[0][(nvar - 1) - i] != node[1][(nargs - 1) - i])
        {
          matchesList = false;
          break;
        }
      }
      if (matchesList)
      {
        Node ret = node[1].getOperator();
        if (nargs > nvar)
        {
          size_t diff = nargs - nvar;
          for (size_t i = 0; i < diff; i++)
          {
            ret = nm->mkNode(Kind::HO_APPLY, ret, node[1][i]);
          }
          // For instance we cannot eliminate (lambda ((x Int)) (f x x)) to
          // (f x).
          std::vector<Node> vars(node[0].begin(), node[0].end());
          if (expr::hasSubterm(ret, vars))
          {
            return Node::null();
          }
        }
        return ret;
      }
    }
  }
  return Node::null();
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
