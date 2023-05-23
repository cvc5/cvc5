/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for function constants
 */

#include "theory/uf/function_const.h"

#include "expr/array_store_all.h"
#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/function_array_const.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/rewriter.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/**
 * Attribute for constructing a unique bound variable list for the lambda
 * corresponding to an array constant.
 */
struct FunctionBoundVarListTag
{
};
using FunctionBoundVarListAttribute =
    expr::Attribute<FunctionBoundVarListTag, Node>;
/**
 * An attribute to cache the conversion between array constants and lambdas.
 */
struct ArrayToLambdaTag
{
};
using ArrayToLambdaAttribute = expr::Attribute<ArrayToLambdaTag, Node>;

Node FunctionConst::toLambda(TNode n)
{
  Kind nk = n.getKind();
  if (nk == kind::LAMBDA)
  {
    return n;
  }
  else if (nk == kind::FUNCTION_ARRAY_CONST)
  {
    ArrayToLambdaAttribute atla;
    if (n.hasAttribute(atla))
    {
      return n.getAttribute(atla);
    }
    const FunctionArrayConst& fc = n.getConst<FunctionArrayConst>();
    Node avalue = fc.getArrayValue();
    TypeNode tn = fc.getType();
    Assert(tn.isFunction());
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    std::vector<Node> bvs;
    NodeManager* nm = NodeManager::currentNM();
    BoundVarManager* bvm = nm->getBoundVarManager();
    // associate a unique bound variable list with the value
    for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
    {
      Node cacheVal =
          BoundVarManager::getCacheValue(n, nm->mkConstInt(Rational(i)));
      Node v =
          bvm->mkBoundVar<FunctionBoundVarListAttribute>(cacheVal, argTypes[i]);
      bvs.push_back(v);
    }
    Node bvl = nm->mkNode(kind::BOUND_VAR_LIST, bvs);
    Node lam = getLambdaForArrayRepresentation(avalue, bvl);
    n.setAttribute(atla, lam);
    return lam;
  }
  return Node::null();
}

TypeNode FunctionConst::getFunctionTypeForArrayType(TypeNode atn, Node bvl)
{
  std::vector<TypeNode> children;
  for (unsigned i = 0; i < bvl.getNumChildren(); i++)
  {
    Assert(atn.isArray());
    Assert(bvl[i].getType() == atn.getArrayIndexType());
    children.push_back(atn.getArrayIndexType());
    atn = atn.getArrayConstituentType();
  }
  children.push_back(atn);
  return NodeManager::currentNM()->mkFunctionType(children);
}

TypeNode FunctionConst::getArrayTypeForFunctionType(TypeNode ftn)
{
  Assert(ftn.isFunction());
  // construct the curried array type
  size_t nchildren = ftn.getNumChildren();
  TypeNode ret = ftn[nchildren - 1];
  for (size_t i = 0; i < nchildren - 1; i++)
  {
    size_t ii = nchildren - i - 2;
    ret = NodeManager::currentNM()->mkArrayType(ftn[ii], ret);
  }
  return ret;
}

Node FunctionConst::getLambdaForArrayRepresentationRec(
    TNode a,
    TNode bvl,
    unsigned bvlIndex,
    std::unordered_map<TNode, Node>& visited)
{
  std::unordered_map<TNode, Node>::iterator it = visited.find(a);
  if (it != visited.end())
  {
    return it->second;
  }
  Node ret;
  if (bvlIndex < bvl.getNumChildren())
  {
    Assert(a.getType().isArray());
    if (a.getKind() == kind::STORE)
    {
      // convert the array recursively
      Node body =
          getLambdaForArrayRepresentationRec(a[0], bvl, bvlIndex, visited);
      if (!body.isNull())
      {
        // convert the value recursively (bounded by the number of arguments
        // in bvl)
        Node val = getLambdaForArrayRepresentationRec(
            a[2], bvl, bvlIndex + 1, visited);
        if (!val.isNull())
        {
          Assert(a[1].getType() == bvl[bvlIndex].getType());
          Assert(val.getType() == body.getType());
          Node cond = bvl[bvlIndex].eqNode(a[1]);
          ret = NodeManager::currentNM()->mkNode(kind::ITE, cond, val, body);
        }
      }
    }
    else if (a.getKind() == kind::STORE_ALL)
    {
      ArrayStoreAll storeAll = a.getConst<ArrayStoreAll>();
      Node sa = storeAll.getValue();
      // convert the default value recursively (bounded by the number of
      // arguments in bvl)
      ret = getLambdaForArrayRepresentationRec(sa, bvl, bvlIndex + 1, visited);
    }
  }
  else
  {
    ret = a;
  }
  visited[a] = ret;
  return ret;
}

Node FunctionConst::getLambdaForArrayRepresentation(TNode a, TNode bvl)
{
  Assert(a.getType().isArray());
  std::unordered_map<TNode, Node> visited;
  Trace("builtin-rewrite-debug")
      << "Get lambda for : " << a << ", with variables " << bvl << std::endl;
  Node body = getLambdaForArrayRepresentationRec(a, bvl, 0, visited);
  if (!body.isNull())
  {
    Trace("builtin-rewrite-debug")
        << "...got lambda body " << body << std::endl;
    return NodeManager::currentNM()->mkNode(kind::LAMBDA, bvl, body);
  }
  Trace("builtin-rewrite-debug") << "...failed to get lambda body" << std::endl;
  return Node::null();
}

Node FunctionConst::getArrayRepresentationForLambdaRec(TNode n,
                                                       TypeNode retType)
{
  Assert(n.getKind() == kind::LAMBDA);
  NodeManager* nm = NodeManager::currentNM();
  Trace("builtin-rewrite-debug")
      << "Get array representation for : " << n << std::endl;

  Node first_arg = n[0][0];
  Node rec_bvl;
  size_t size = n[0].getNumChildren();
  if (size > 1)
  {
    std::vector<Node> args;
    for (size_t i = 1; i < size; i++)
    {
      args.push_back(n[0][i]);
    }
    rec_bvl = nm->mkNode(kind::BOUND_VAR_LIST, args);
  }

  Trace("builtin-rewrite-debug2") << "  process body..." << std::endl;
  std::vector<Node> conds;
  std::vector<Node> vals;
  Node curr = n[1];
  Kind ck = curr.getKind();
  while (ck == kind::ITE || ck == kind::OR || ck == kind::AND
         || ck == kind::EQUAL || ck == kind::NOT || ck == kind::BOUND_VARIABLE)
  {
    Node index_eq;
    Node curr_val;
    Node next;
    // Each iteration of this loop infers an entry in the function, e.g. it
    // has a value under some condition.

    // [1] We infer that the entry has value "curr_val" under condition
    // "index_eq". We set "next" to the node that is the remainder of the
    // function to process.
    if (ck == kind::ITE)
    {
      Trace("builtin-rewrite-debug2")
          << "  process condition : " << curr[0] << std::endl;
      index_eq = curr[0];
      curr_val = curr[1];
      next = curr[2];
    }
    else if (ck == kind::OR || ck == kind::AND)
    {
      Trace("builtin-rewrite-debug2")
          << "  process base : " << curr << std::endl;
      // Complex Boolean return cases, in which
      //  (1) lambda x. (= x v1) v ... becomes
      //      lambda x. (ite (= x v1) true [...])
      //
      //  (2) lambda x. (not (= x v1)) ^ ... becomes
      //      lambda x. (ite (= x v1) false [...])
      //
      // Note the negated cases of the lhs of the OR/AND operators above are
      // handled by pushing the recursion to the then-branch, with the
      // else-branch being the constant value. For example, the negated (1)
      // would be
      //  (1') lambda x. (not (= x v1)) v ... becomes
      //       lambda x. (ite (= x v1) [...] true)
      // thus requiring the rest of the disjunction to be further processed in
      // the then-branch as the current value.
      bool pol = curr[0].getKind() != kind::NOT;
      bool inverted = (pol == (ck == kind::AND));
      index_eq = pol ? curr[0] : curr[0][0];
      // processed : the value that is determined by the first child of curr
      // remainder : the remaining children of curr
      Node processed, remainder;
      // the value is the polarity of the first child or its inverse if we are
      // in the inverted case
      processed = nm->mkConst(!inverted ? pol : !pol);
      // build an OR/AND with the remaining components
      if (curr.getNumChildren() == 2)
      {
        remainder = curr[1];
      }
      else
      {
        std::vector<Node> remainderNodes{curr.begin() + 1, curr.end()};
        remainder = nm->mkNode(ck, remainderNodes);
      }
      if (inverted)
      {
        curr_val = remainder;
        next = processed;
        // If the lambda contains more variables than the one being currently
        // processed, the current value can be non-constant, since it'll be
        // processed recursively below. Otherwise we fail.
        if (rec_bvl.isNull() && !curr_val.isConst())
        {
          Trace("builtin-rewrite-debug2")
              << "...non-const curr_val " << curr_val << "\n";
          return Node::null();
        }
      }
      else
      {
        curr_val = processed;
        next = remainder;
      }
      Trace("builtin-rewrite-debug2") << "  index_eq : " << index_eq << "\n";
      Trace("builtin-rewrite-debug2") << "  curr_val : " << curr_val << "\n";
      Trace("builtin-rewrite-debug2") << "  next : " << next << std::endl;
    }
    else
    {
      Trace("builtin-rewrite-debug2")
          << "  process base : " << curr << std::endl;
      // Simple Boolean return cases, in which
      //  (1) lambda x. (= x v) becomes lambda x. (ite (= x v) true false)
      //  (2) lambda x. x becomes lambda x. (ite (= x true) true false)
      // Note the negateg cases of the bodies above are also handled.
      bool pol = ck != kind::NOT;
      index_eq = pol ? curr : curr[0];
      curr_val = nm->mkConst(pol);
      next = nm->mkConst(!pol);
    }

    // [2] We ensure that "index_eq" is an equality, if possible.
    if (index_eq.getKind() != kind::EQUAL)
    {
      bool pol = index_eq.getKind() != kind::NOT;
      Node indexEqAtom = pol ? index_eq : index_eq[0];
      if (indexEqAtom.getKind() == kind::BOUND_VARIABLE)
      {
        if (!indexEqAtom.getType().isBoolean())
        {
          // Catches default case of non-Boolean variable, e.g.
          // lambda x : Int. x. In this case, it is not canonical and we fail.
          Trace("builtin-rewrite-debug2")
              << "  ...non-Boolean variable." << std::endl;
          return Node::null();
        }
        // Boolean argument case, e.g. lambda x. ite( x, t, s ) is processed as
        // lambda x. (ite (= x true) t s)
        index_eq = indexEqAtom.eqNode(nm->mkConst(pol));
      }
      else
      {
        // non-equality condition
        Trace("builtin-rewrite-debug2")
            << "  ...non-equality condition." << std::endl;
        return Node::null();
      }
    }

    // [3] We ensure that "index_eq" is an equality that is equivalent to
    // "first_arg" = "curr_index", where curr_index is a constant, and
    // "first_arg" is the current argument we are processing, if possible.
    Node curr_index;
    for (unsigned r = 0; r < 2; r++)
    {
      Node arg = index_eq[r];
      Node val = index_eq[1 - r];
      if (arg == first_arg)
      {
        curr_index = val;
        Trace("builtin-rewrite-debug2")
            << "  arg " << arg << " -> " << val << std::endl;
        break;
      }
    }
    if (curr_index.isNull())
    {
      Trace("builtin-rewrite-debug2")
          << "  ...could not infer index value." << std::endl;
      // it could correspond to the default value that does not involve the
      // current argument, hence we break and take curr as the default value
      // below. For example, if we are processing lambda xy. (not y) for x,
      // we have index_eq is (= y true), which does not match for x, hence
      // (not y) is taken as the default value below.
      break;
    }

    // [4] Recurse to ensure that "curr_val" has been normalized w.r.t. the
    // remaining arguments (rec_bvl).
    if (!rec_bvl.isNull())
    {
      curr_val = nm->mkNode(kind::LAMBDA, rec_bvl, curr_val);
      Trace("builtin-rewrite-debug") << push;
      Trace("builtin-rewrite-debug2") << push;
      curr_val = getArrayRepresentationForLambdaRec(curr_val, retType);
      Trace("builtin-rewrite-debug") << pop;
      Trace("builtin-rewrite-debug2") << pop;
      if (curr_val.isNull())
      {
        Trace("builtin-rewrite-debug2")
            << "  ...failed to recursively find value." << std::endl;
        return Node::null();
      }
    }
    Trace("builtin-rewrite-debug2")
        << "  ...condition is index " << curr_val << std::endl;

    // [5] Add the entry
    Assert(!curr_index.isNull());
    Assert(!curr_val.isNull());
    if (!curr_index.isConst() || !curr_val.isConst())
    {
      // non-constant value
      Trace("builtin-rewrite-debug2") << "  ...non-constant value for entry\n.";
      return Node::null();
    }
    conds.push_back(curr_index);
    vals.push_back(curr_val);

    // we will now process the remainder
    curr = next;
    ck = curr.getKind();
    Trace("builtin-rewrite-debug2")
        << "  process remainder : " << curr << std::endl;
  }
  if (!rec_bvl.isNull())
  {
    curr = nm->mkNode(kind::LAMBDA, rec_bvl, curr);
    Trace("builtin-rewrite-debug") << push;
    Trace("builtin-rewrite-debug2") << push;
    curr = getArrayRepresentationForLambdaRec(curr, retType);
    Trace("builtin-rewrite-debug") << pop;
    Trace("builtin-rewrite-debug2") << pop;
  }
  if (!curr.isNull() && curr.isConst())
  {
    // compute the return type
    TypeNode array_type = retType;
    for (size_t i = 0; i < size; i++)
    {
      size_t index = (size - 1) - i;
      array_type = nm->mkArrayType(n[0][index].getType(), array_type);
    }
    Trace("builtin-rewrite-debug2")
        << "  make array store all " << curr.getType()
        << " annotated : " << array_type << " from " << curr << std::endl;
    Assert(curr.getType() == array_type.getArrayConstituentType());
    curr = nm->mkConst(ArrayStoreAll(array_type, curr));
    Trace("builtin-rewrite-debug2") << "  build array..." << std::endl;
    // can only build if default value is constant (since array store all must
    // be constant)
    Trace("builtin-rewrite-debug2")
        << "  got constant base " << curr << std::endl;
    Trace("builtin-rewrite-debug2") << "  conditions " << conds << std::endl;
    Trace("builtin-rewrite-debug2") << "  values " << vals << std::endl;
    // construct store chain
    for (size_t i = 0, numCond = conds.size(); i < numCond; i++)
    {
      size_t ii = (numCond - 1) - i;
      Assert(conds[ii].getType() == first_arg.getType());
      curr = nm->mkNode(kind::STORE, curr, conds[ii], vals[ii]);
      // normalize it using the array rewriter utility, which must be done at
      // each iteration of this loop
      curr = arrays::TheoryArraysRewriter::normalizeConstant(curr);
    }
    Trace("builtin-rewrite-debug")
        << "...got array " << curr << " for " << n << std::endl;
    return curr;
  }
  Trace("builtin-rewrite-debug")
      << "...failed to get array (cannot get constant default value)"
      << std::endl;
  return Node::null();
}

Node FunctionConst::toArrayConst(TNode n)
{
  Kind nk = n.getKind();
  if (nk == kind::FUNCTION_ARRAY_CONST)
  {
    const FunctionArrayConst& fc = n.getConst<FunctionArrayConst>();
    return fc.getArrayValue();
  }
  else if (nk == kind::LAMBDA)
  {
    // must carry the overall return type to deal with cases like (lambda ((x
    // Int) (y Int)) (ite (= x _) 0.5 0.0)), where the inner construction for
    // the else case above should be (arraystoreall (Array Int Real) 0.0)
    return getArrayRepresentationForLambdaRec(n, n[1].getType());
  }
  return Node::null();
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
