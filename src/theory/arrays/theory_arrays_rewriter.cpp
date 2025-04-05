/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Clark Barrett, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include "theory/arrays/theory_arrays_rewriter.h"

#include "expr/array_store_all.h"
#include "expr/attribute.h"
#include "proof/conv_proof_generator.h"
#include "proof/eager_proof_generator.h"
#include "smt/env.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/type_enumerator.h"
#include "util/cardinality.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

namespace attr {
struct ArrayConstantMostFrequentValueTag
{
};
struct ArrayConstantMostFrequentValueCountTag
{
};
}  // namespace attr

using ArrayConstantMostFrequentValueCountAttr =
    expr::Attribute<attr::ArrayConstantMostFrequentValueCountTag, uint64_t>;
using ArrayConstantMostFrequentValueAttr =
    expr::Attribute<attr::ArrayConstantMostFrequentValueTag, Node>;

Node getMostFrequentValue(TNode store)
{
  return store.getAttribute(ArrayConstantMostFrequentValueAttr());
}
uint64_t getMostFrequentValueCount(TNode store)
{
  return store.getAttribute(ArrayConstantMostFrequentValueCountAttr());
}

void setMostFrequentValue(TNode store, TNode value)
{
  return store.setAttribute(ArrayConstantMostFrequentValueAttr(), value);
}
void setMostFrequentValueCount(TNode store, uint64_t count)
{
  return store.setAttribute(ArrayConstantMostFrequentValueCountAttr(), count);
}

TheoryArraysRewriter::TheoryArraysRewriter(NodeManager* nm, Rewriter* r)
    : TheoryRewriter(nm), d_rewriter(r)
{
  registerProofRewriteRule(ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_CONSTANT,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::ARRAYS_SELECT_CONST,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::ARRAYS_EQ_RANGE_EXPAND,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_OP,
                           TheoryRewriteCtx::PRE_DSL);
}

Node TheoryArraysRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_CONSTANT:
    {
      if (n.getKind() == Kind::STORE && n[0].isConst() && n[1].isConst()
          && n[2].isConst())
      {
        Node nn = normalizeConstant(nodeManager(), n);
        if (nn != n)
        {
          return nn;
        }
      }
    }
    break;
    case ProofRewriteRule::ARRAYS_SELECT_CONST:
    {
      if (n.getKind() == Kind::SELECT && n[0].getKind() == Kind::STORE_ALL)
      {
        ArrayStoreAll storeAll = n[0].getConst<ArrayStoreAll>();
        return storeAll.getValue();
      }
    }
    break;
    case ProofRewriteRule::ARRAYS_EQ_RANGE_EXPAND:
    {
      if (n.getKind() == Kind::EQ_RANGE)
      {
        return expandEqRange(d_nm, n);
      }
    }
    break;
    case ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_OP:
    {
      Kind k = n.getKind();
      if (k != Kind::SELECT && k != Kind::STORE)
      {
        return Node::null();
      }
      return computeNormalizeOp(n);
    }
    break;
    default: break;
  }
  return Node::null();
}

Node TheoryArraysRewriter::computeNormalizeOp(const Node& n,
                                              TConvProofGenerator* pg) const
{
  NodeManager* nm = nodeManager();
  Kind k = n.getKind();
  Assert(k == Kind::SELECT || k == Kind::STORE);
  Node index = n[1];
  bool iconst = index.isConst();
  Node arr = n[0];
  std::vector<Node> indices;
  std::vector<Node> elems;
  bool success = false;
  std::vector<Node> ctermc;
  Node currTerm = n;
  if (pg != nullptr)
  {
    ctermc.insert(ctermc.begin(), n.begin(), n.end());
  }
  while (arr.getKind() == Kind::STORE)
  {
    if (arr[1] == index)
    {
      // process being equal:
      // if store, we are redundant, remove and break
      // if select, we return the element directly
      Node ret = k == Kind::STORE ? arr[0] : arr[2];
      if (pg != nullptr)
      {
        Node rewTerm = ret;
        if (k == Kind::STORE)
        {
          rewTerm = nm->mkNode(Kind::STORE, rewTerm, n[1], n[2]);
        }
        Trace("array-norm-op-rcons")
            << "- rewrite " << currTerm << " -> " << rewTerm << std::endl;
        // proven by RARE rule array-store-overwrite or array-read-over-write
        pg->addRewriteStep(currTerm,
                           rewTerm,
                           nullptr,
                           false,
                           TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
      }
      if (k == Kind::STORE)
      {
        arr = ret;
      }
      else
      {
        return ret;
      }
      break;
    }
    // store orders indices only
    if (k == Kind::STORE && arr[1] < index)
    {
      break;
    }
    // success if we can move past
    success = false;
    if (iconst)
    {
      success = arr[1].isConst();
    }
    else
    {
      Node eq = mkEqNode(arr[1], index);
      success = (eq.isConst() && !eq.getConst<bool>());
    }
    if (success)
    {
      indices.push_back(arr[1]);
      elems.push_back(arr[2]);
      arr = arr[0];
      if (pg != nullptr)
      {
        ctermc[0] = arr;
        // proven by RARE rule array-read-over-write2 or array-store-swap
        Node prevTerm = currTerm;
        currTerm = nm->mkNode(k, ctermc);
        // the rewrite for the store is a swap, temporarily construct the rhs
        Node rewTerm = currTerm;
        if (k == Kind::STORE)
        {
          rewTerm =
              nm->mkNode(Kind::STORE, rewTerm, prevTerm[0][1], prevTerm[0][2]);
        }
        Trace("array-norm-op-rcons")
            << "- rewrite " << prevTerm << " -> " << rewTerm << std::endl;
        pg->addRewriteStep(prevTerm,
                           rewTerm,
                           nullptr,
                           false,
                           TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
      }
    }
    else
    {
      break;
    }
  }
  if (indices.empty())
  {
    return Node::null();
  }
  Node ret;
  if (k == Kind::STORE)
  {
    ret = nm->mkNode(Kind::STORE, arr, n[1], n[2]);
    // add back those we traversed over
    while (!indices.empty())
    {
      ret = nm->mkNode(Kind::STORE, ret, indices.back(), elems.back());
      indices.pop_back();
      elems.pop_back();
    }
  }
  else
  {
    Assert(k == Kind::SELECT);
    ret = nm->mkNode(Kind::SELECT, arr, n[1]);
  }
  return ret;
}

Node TheoryArraysRewriter::normalizeConstant(NodeManager* nm, TNode node)
{
  if (node.isConst())
  {
    return node;
  }
  Node ret;
  TypeNode tn = node[1].getType();
  CardinalityClass tcc = tn.getCardinalityClass();
  if (tcc == CardinalityClass::FINITE || tcc == CardinalityClass::ONE)
  {
    ret = normalizeConstant(nm, node, tn.getCardinality());
  }
  else
  {
    ret = normalizeConstant(nm, node, Cardinality::INTEGERS);
  }
  Assert(ret.isConst()) << "Non-constant after normalization: " << ret;
  return ret;
}

// this function is called by printers when using the option "--model-u-dt-enum"
Node TheoryArraysRewriter::normalizeConstant(NodeManager* nm,
                                             TNode node,
                                             Cardinality indexCard)
{
  TNode store = node[0];
  TNode index = node[1];
  TNode value = node[2];

  std::vector<TNode> indices;
  std::vector<TNode> elements;

  // Normal form for nested stores is just ordering by index - but also need
  // to check if we are writing to default value

  // Go through nested stores looking for where to insert index
  // Also check whether we are replacing an existing store
  TNode replacedValue;
  uint32_t depth = 1;
  uint32_t valCount = 1;
  while (store.getKind() == Kind::STORE)
  {
    if (index == store[1])
    {
      replacedValue = store[2];
      store = store[0];
      break;
    }
    else if (index >= store[1])
    {
      break;
    }
    if (value == store[2])
    {
      valCount += 1;
    }
    depth += 1;
    indices.push_back(store[1]);
    elements.push_back(store[2]);
    store = store[0];
  }
  Node n = store;

  // Get the default value at the bottom of the nested stores
  while (store.getKind() == Kind::STORE)
  {
    if (value == store[2])
    {
      valCount += 1;
    }
    depth += 1;
    store = store[0];
  }
  Assert(store.getKind() == Kind::STORE_ALL);
  ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
  Node defaultValue = storeAll.getValue();

  // Check if we are writing to default value - if so the store
  // to index can be ignored
  if (value == defaultValue)
  {
    if (replacedValue.isNull())
    {
      // Quick exit - if writing to default value and nothing was
      // replaced, we can just return node[0]
      return node[0];
    }
    // else rebuild the store without the replaced write and then exit
  }
  else
  {
    n = nm->mkNode(Kind::STORE, n, index, value);
  }

  // Build the rest of the store after inserting/deleting
  while (!indices.empty())
  {
    n = nm->mkNode(Kind::STORE, n, indices.back(), elements.back());
    indices.pop_back();
    elements.pop_back();
  }

  // Ready to exit if write was to the default value (see previous comment)
  if (value == defaultValue)
  {
    return n;
  }

  if (indexCard.isInfinite())
  {
    return n;
  }

  // When index sort is finite, we have to check whether there is any value
  // that is written to more than the default value.  If so, it must become
  // the new default value

  TNode mostFrequentValue;
  uint32_t mostFrequentValueCount = 0;
  store = node[0];
  if (store.getKind() == Kind::STORE)
  {
    mostFrequentValue = getMostFrequentValue(store);
    mostFrequentValueCount = getMostFrequentValueCount(store);
  }

  // Compute the most frequently written value for n
  if (valCount > mostFrequentValueCount
      || (valCount == mostFrequentValueCount && value < mostFrequentValue))
  {
    mostFrequentValue = value;
    mostFrequentValueCount = valCount;
  }

  // Need to make sure the default value count is larger, or the same and the
  // default value is expression-order-less-than nextValue
  Cardinality::CardinalityComparison compare =
      indexCard.compare(mostFrequentValueCount + depth);
  Assert(compare != Cardinality::UNKNOWN);
  if (compare == Cardinality::GREATER
      || (compare == Cardinality::EQUAL && (defaultValue < mostFrequentValue)))
  {
    return n;
  }

  // Bad case: have to recompute value counts and/or possibly switch out
  // default value
  store = n;
  std::unordered_set<TNode> indexSet;
  std::unordered_map<TNode, uint32_t> elementsMap;
  std::unordered_map<TNode, uint32_t>::iterator it;
  uint32_t count;
  uint32_t max = 0;
  TNode maxValue;
  while (store.getKind() == Kind::STORE)
  {
    indices.push_back(store[1]);
    indexSet.insert(store[1]);
    elements.push_back(store[2]);
    it = elementsMap.find(store[2]);
    if (it != elementsMap.end())
    {
      (*it).second = (*it).second + 1;
      count = (*it).second;
    }
    else
    {
      elementsMap[store[2]] = 1;
      count = 1;
    }
    if (count > max || (count == max && store[2] < maxValue))
    {
      max = count;
      maxValue = store[2];
    }
    store = store[0];
  }

  Assert(depth == indices.size());
  compare = indexCard.compare(max + depth);
  Assert(compare != Cardinality::UNKNOWN);
  if (compare == Cardinality::GREATER
      || (compare == Cardinality::EQUAL && (defaultValue < maxValue)))
  {
    Assert(!replacedValue.isNull() && mostFrequentValue == replacedValue);
    return n;
  }

  // Out of luck: have to swap out default value

  // Enumerate values from index type into newIndices and sort
  std::vector<Node> newIndices;
  TypeEnumerator te(index.getType());
  bool needToSort = false;
  uint32_t numTe = 0;
  while (!te.isFinished()
         && (!indexCard.isFinite()
             || numTe < indexCard.getFiniteCardinality().toUnsignedInt()))
  {
    if (indexSet.find(*te) == indexSet.end())
    {
      if (!newIndices.empty() && (!(newIndices.back() < (*te))))
      {
        needToSort = true;
      }
      newIndices.push_back(*te);
    }
    ++numTe;
    ++te;
  }
  Assert(indexCard.compare(newIndices.size() + depth) == Cardinality::EQUAL);
  if (needToSort)
  {
    std::sort(newIndices.begin(), newIndices.end());
  }

  n = nm->mkConst(ArrayStoreAll(node.getType(), maxValue));
  std::vector<Node>::iterator itNew = newIndices.begin(),
                              it_end = newIndices.end();
  while (itNew != it_end || !indices.empty())
  {
    if (itNew != it_end && (indices.empty() || (*itNew) < indices.back()))
    {
      n = nm->mkNode(Kind::STORE, n, (*itNew), defaultValue);
      ++itNew;
    }
    else if (itNew == it_end || indices.back() < (*itNew))
    {
      if (elements.back() != maxValue)
      {
        n = nm->mkNode(Kind::STORE, n, indices.back(), elements.back());
      }
      indices.pop_back();
      elements.pop_back();
    }
  }
  return n;
}

Node TheoryArraysRewriter::expandEqRange(NodeManager* nm, TNode node)
{
  Assert(node.getKind() == Kind::EQ_RANGE);

  TNode a = node[0];
  TNode b = node[1];
  TNode i = node[2];
  TNode j = node[3];
  Node k = SkolemCache::getEqRangeVar(nm, node);
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, k);
  TypeNode type = k.getType();

  Kind kle;
  Node range;
  if (type.isBitVector())
  {
    kle = Kind::BITVECTOR_ULE;
  }
  else if (type.isFloatingPoint())
  {
    kle = Kind::FLOATINGPOINT_LEQ;
  }
  else if (type.isRealOrInt())
  {
    kle = Kind::LEQ;
  }
  else
  {
    Unimplemented() << "Type " << type << " is not supported for predicate "
                    << node.getKind();
  }

  range = nm->mkNode(Kind::AND, nm->mkNode(kle, i, k), nm->mkNode(kle, k, j));

  Node eq = nm->mkNode(Kind::EQUAL,
                       nm->mkNode(Kind::SELECT, a, k),
                       nm->mkNode(Kind::SELECT, b, k));
  Node implies = nm->mkNode(Kind::IMPLIES, range, eq);
  return nm->mkNode(Kind::FORALL, bvl, implies);
}

RewriteResponse TheoryArraysRewriter::postRewrite(TNode node)
{
  Trace("arrays-postrewrite")
      << "Arrays::postRewrite start " << node << std::endl;
  switch (node.getKind())
  {
    case Kind::SELECT:
    {
      TNode store = node[0];
      TNode index = node[1];
      Node n;
      bool val;
      while (store.getKind() == Kind::STORE)
      {
        if (index == store[1])
        {
          val = true;
        }
        else if (index.isConst() && store[1].isConst())
        {
          val = false;
        }
        else
        {
          n = mkEqNode(store[1], index);
          if (n.getKind() != Kind::CONST_BOOLEAN)
          {
            break;
          }
          val = n.getConst<bool>();
        }
        if (val)
        {
          // select(store(a,i,v),j) = v if i = j
          Trace("arrays-postrewrite")
              << "Arrays::postRewrite returning " << store[2] << std::endl;
          return RewriteResponse(REWRITE_DONE, store[2]);
        }
        // select(store(a,i,v),j) = select(a,j) if i /= j
        store = store[0];
      }
      if (store.getKind() == Kind::STORE_ALL)
      {
        // select(store_all(v),i) = v
        ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
        n = storeAll.getValue();
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning " << n << std::endl;
        Assert(n.isConst());
        return RewriteResponse(REWRITE_DONE, n);
      }
      else if (store != node[0])
      {
        n = nodeManager()->mkNode(Kind::SELECT, store, index);
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning " << n << std::endl;
        return RewriteResponse(REWRITE_DONE, n);
      }
      break;
    }
    case Kind::STORE:
    {
      TNode store = node[0];
      TNode value = node[2];
      // store(a,i,select(a,i)) = a
      if (value.getKind() == Kind::SELECT && value[0] == store
          && value[1] == node[1])
      {
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning " << store << std::endl;
        return RewriteResponse(REWRITE_DONE, store);
      }
      TNode index = node[1];
      if (store.isConst() && index.isConst() && value.isConst())
      {
        // normalize constant
        Node n = normalizeConstant(d_nm, node);
        Assert(n.isConst());
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning " << n << std::endl;
        return RewriteResponse(REWRITE_DONE, n);
      }
      if (store.getKind() == Kind::STORE)
      {
        // store(store(a,i,v),j,w)
        bool val;
        if (index == store[1])
        {
          val = true;
        }
        else if (index.isConst() && store[1].isConst())
        {
          val = false;
        }
        else
        {
          Node eqRewritten = mkEqNode(store[1], index);
          if (eqRewritten.getKind() != Kind::CONST_BOOLEAN)
          {
            Trace("arrays-postrewrite")
                << "Arrays::postRewrite returning " << node << std::endl;
            return RewriteResponse(REWRITE_DONE, node);
          }
          val = eqRewritten.getConst<bool>();
        }
        NodeManager* nm = nodeManager();
        if (val)
        {
          // store(store(a,i,v),i,w) = store(a,i,w)
          Node result = nm->mkNode(Kind::STORE, store[0], index, value);
          Trace("arrays-postrewrite")
              << "Arrays::postRewrite returning " << result << std::endl;
          return RewriteResponse(REWRITE_AGAIN, result);
        }
        else if (index < store[1])
        {
          // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
          //    IF i != j and j comes before i in the ordering
          std::vector<TNode> indices;
          std::vector<TNode> elements;
          indices.push_back(store[1]);
          elements.push_back(store[2]);
          store = store[0];
          Node n;
          while (store.getKind() == Kind::STORE)
          {
            if (index == store[1])
            {
              val = true;
            }
            else if (index.isConst() && store[1].isConst())
            {
              val = false;
            }
            else
            {
              n = mkEqNode(store[1], index);
              if (n.getKind() != Kind::CONST_BOOLEAN)
              {
                break;
              }
              val = n.getConst<bool>();
            }
            if (val)
            {
              store = store[0];
              break;
            }
            else if (!(index < store[1]))
            {
              break;
            }
            indices.push_back(store[1]);
            elements.push_back(store[2]);
            store = store[0];
          }
          if (value.getKind() == Kind::SELECT && value[0] == store
              && value[1] == index)
          {
            n = store;
          }
          else
          {
            n = nm->mkNode(Kind::STORE, store, index, value);
          }
          while (!indices.empty())
          {
            n = nm->mkNode(Kind::STORE, n, indices.back(), elements.back());
            indices.pop_back();
            elements.pop_back();
          }
          Assert(n != node);
          Trace("arrays-postrewrite")
              << "Arrays::postRewrite returning " << n << std::endl;
          return RewriteResponse(REWRITE_AGAIN_FULL, n);
        }
      }
      break;
    }
    case Kind::EQUAL:
    {
      if (node[0] == node[1])
      {
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning true" << std::endl;
        return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning false" << std::endl;
        return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(false));
      }
      if (node[0] > node[1])
      {
        Node newNode = nodeManager()->mkNode(node.getKind(), node[1], node[0]);
        Trace("arrays-postrewrite")
            << "Arrays::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default: break;
  }
  Trace("arrays-postrewrite")
      << "Arrays::postRewrite returning " << node << std::endl;
  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheoryArraysRewriter::preRewrite(TNode node)
{
  Trace("arrays-prerewrite")
      << "Arrays::preRewrite start " << node << std::endl;
  switch (node.getKind())
  {
    case Kind::SELECT:
    {
      TNode store = node[0];
      TNode index = node[1];
      Node n;
      bool val;
      while (store.getKind() == Kind::STORE)
      {
        if (index == store[1])
        {
          val = true;
        }
        else if (index.isConst() && store[1].isConst())
        {
          val = false;
        }
        else
        {
          break;
        }
        if (val)
        {
          // select(store(a,i,v),j) = v if i = j
          Trace("arrays-prerewrite")
              << "Arrays::preRewrite returning " << store[2] << std::endl;
          return RewriteResponse(REWRITE_AGAIN, store[2]);
        }
        // select(store(a,i,v),j) = select(a,j) if i /= j
        store = store[0];
      }
      if (store.getKind() == Kind::STORE_ALL)
      {
        // select(store_all(v),i) = v
        ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
        n = storeAll.getValue();
        Trace("arrays-prerewrite")
            << "Arrays::preRewrite returning " << n << std::endl;
        Assert(n.isConst());
        return RewriteResponse(REWRITE_DONE, n);
      }
      else if (store != node[0])
      {
        n = nodeManager()->mkNode(Kind::SELECT, store, index);
        Trace("arrays-prerewrite")
            << "Arrays::preRewrite returning " << n << std::endl;
        return RewriteResponse(REWRITE_DONE, n);
      }
      break;
    }
    case Kind::STORE:
    {
      TNode store = node[0];
      TNode value = node[2];
      // store(a,i,select(a,i)) = a
      if (value.getKind() == Kind::SELECT && value[0] == store
          && value[1] == node[1])
      {
        Trace("arrays-prerewrite")
            << "Arrays::preRewrite returning " << store << std::endl;
        return RewriteResponse(REWRITE_AGAIN, store);
      }
      if (store.getKind() == Kind::STORE)
      {
        // store(store(a,i,v),j,w)
        TNode index = node[1];
        bool val;
        if (index == store[1])
        {
          val = true;
        }
        else if (index.isConst() && store[1].isConst())
        {
          val = false;
        }
        else
        {
          break;
        }
        NodeManager* nm = nodeManager();
        if (val)
        {
          // store(store(a,i,v),i,w) = store(a,i,w)
          Node newNode = nm->mkNode(Kind::STORE, store[0], index, value);
          Trace("arrays-prerewrite")
              << "Arrays::preRewrite returning " << newNode << std::endl;
          // We may have more than two nested stores to the same index or the
          // rule above (store(a,i,select(a,i)) ---> a) may apply after this
          // rewrite, so we return REWRITE_AGAIN here.
          return RewriteResponse(REWRITE_AGAIN, newNode);
        }
      }
      break;
    }
    case Kind::EQUAL:
    {
      if (node[0] == node[1])
      {
        Trace("arrays-prerewrite")
            << "Arrays::preRewrite returning true" << std::endl;
        return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
      }
      break;
    }
    default: break;
  }

  Trace("arrays-prerewrite")
      << "Arrays::preRewrite returning " << node << std::endl;
  return RewriteResponse(REWRITE_DONE, node);
}

Node TheoryArraysRewriter::expandDefinition(Node node)
{
  Kind kind = node.getKind();

  if (kind == Kind::EQ_RANGE)
  {
    return expandEqRange(d_nm, node);
  }

  return Node::null();
}

Node TheoryArraysRewriter::mkEqNode(const Node& a, const Node& b) const
{
  Node eq = a.eqNode(b);
  return d_rewriter->rewrite(eq);
}
  
}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal
