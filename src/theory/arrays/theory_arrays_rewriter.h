/*********************                                                        */
/*! \file theory_arrays_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H
#define CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H

#include <unordered_map>
#include <unordered_set>

#include "theory/rewriter.h"
#include "theory/theory_rewriter.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {
namespace arrays {

Node getMostFrequentValue(TNode store);
uint64_t getMostFrequentValueCount(TNode store);
void setMostFrequentValue(TNode store, TNode value);
void setMostFrequentValueCount(TNode store, uint64_t count);

static inline Node mkEqNode(Node a, Node b) {
  return a.eqNode(b);
}

class TheoryArraysRewriter : public TheoryRewriter
{
  static Node normalizeConstant(TNode node) {
    return normalizeConstant(node, node[1].getType().getCardinality());
  }

 public:
  //this function is called by printers when using the option "--model-u-dt-enum"
  static Node normalizeConstant(TNode node, Cardinality indexCard) {
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
    unsigned depth = 1;
    unsigned valCount = 1;
    while (store.getKind() == kind::STORE) {
      if (index == store[1]) {
        replacedValue = store[2];
        store = store[0];
        break;
      }
      else if (!(index < store[1])) {
        break;
      }
      if (value == store[2]) {
        valCount += 1;
      }
      depth += 1;
      indices.push_back(store[1]);
      elements.push_back(store[2]);
      store = store[0];
    }
    Node n = store;

    // Get the default value at the bottom of the nested stores
    while (store.getKind() == kind::STORE) {
      if (value == store[2]) {
        valCount += 1;
      }
      depth += 1;
      store = store[0];
    }
    Assert(store.getKind() == kind::STORE_ALL);
    ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
    Node defaultValue = storeAll.getValue();
    NodeManager* nm = NodeManager::currentNM();

    // Check if we are writing to default value - if so the store
    // to index can be ignored
    if (value == defaultValue) {
      if (replacedValue.isNull()) {
        // Quick exit - if writing to default value and nothing was
        // replaced, we can just return node[0]
        return node[0];
      }
      // else rebuild the store without the replaced write and then exit
    }
    else {
      n = nm->mkNode(kind::STORE, n, index, value);
    }

    // Build the rest of the store after inserting/deleting
    while (!indices.empty()) {
      n = nm->mkNode(kind::STORE, n, indices.back(), elements.back());
      indices.pop_back();
      elements.pop_back();
    }

    // Ready to exit if write was to the default value (see previous comment)
    if (value == defaultValue) {
      return n;
    }

    if (indexCard.isInfinite()) {
      return n;
    }

    // When index sort is finite, we have to check whether there is any value
    // that is written to more than the default value.  If so, it must become
    // the new default value

    TNode mostFrequentValue;
    unsigned mostFrequentValueCount = 0;
    store = node[0];
    if (store.getKind() == kind::STORE) {
      mostFrequentValue = getMostFrequentValue(store);
      mostFrequentValueCount = getMostFrequentValueCount(store);
    }

    // Compute the most frequently written value for n
    if (valCount > mostFrequentValueCount ||
        (valCount == mostFrequentValueCount && value < mostFrequentValue)) {
      mostFrequentValue = value;
      mostFrequentValueCount = valCount;
    }

    // Need to make sure the default value count is larger, or the same and the default value is expression-order-less-than nextValue
    Cardinality::CardinalityComparison compare = indexCard.compare(mostFrequentValueCount + depth);
    Assert(compare != Cardinality::UNKNOWN);
    if (compare == Cardinality::GREATER ||
        (compare == Cardinality::EQUAL && (defaultValue < mostFrequentValue))) {
      return n;
    }

    // Bad case: have to recompute value counts and/or possibly switch out
    // default value
    store = n;
    std::unordered_set<TNode, TNodeHashFunction> indexSet;
    std::unordered_map<TNode, unsigned, TNodeHashFunction> elementsMap;
    std::unordered_map<TNode, unsigned, TNodeHashFunction>::iterator it;
    unsigned count;
    unsigned max = 0;
    TNode maxValue;
    while (store.getKind() == kind::STORE) {
      indices.push_back(store[1]);
      indexSet.insert(store[1]);
      elements.push_back(store[2]);
      it = elementsMap.find(store[2]);
      if (it != elementsMap.end()) {
        (*it).second = (*it).second + 1;
        count = (*it).second;
      }
      else {
        elementsMap[store[2]] = 1;
        count = 1;
      }
      if (count > max ||
          (count == max && store[2] < maxValue)) {
        max = count;
        maxValue = store[2];
      }
      store = store[0];
    }

    Assert(depth == indices.size());
    compare = indexCard.compare(max + depth);
    Assert(compare != Cardinality::UNKNOWN);
    if (compare == Cardinality::GREATER ||
        (compare == Cardinality::EQUAL && (defaultValue < maxValue))) {
      Assert(!replacedValue.isNull() && mostFrequentValue == replacedValue);
      return n;
    }

    // Out of luck: have to swap out default value

    // Enumerate values from index type into newIndices and sort
    std::vector<Node> newIndices;
    TypeEnumerator te(index.getType());
    bool needToSort = false;
    unsigned numTe = 0;
    while (!te.isFinished() && (!indexCard.isFinite() || numTe<indexCard.getFiniteCardinality().toUnsignedInt())) {
      if (indexSet.find(*te) == indexSet.end()) {
        if (!newIndices.empty() && (!(newIndices.back() < (*te)))) {
          needToSort = true;
        }
        newIndices.push_back(*te);
      }
      ++numTe;
      ++te;
    }
    Assert(indexCard.compare(newIndices.size() + depth) == Cardinality::EQUAL);
    if (needToSort) {
      std::sort(newIndices.begin(), newIndices.end());
    }

    n = nm->mkConst(ArrayStoreAll(node.getType(), maxValue));
    std::vector<Node>::iterator itNew = newIndices.begin(), it_end = newIndices.end();
    while (itNew != it_end || !indices.empty()) {
      if (itNew != it_end && (indices.empty() || (*itNew) < indices.back())) {
        n = nm->mkNode(kind::STORE, n, (*itNew), defaultValue);
        ++itNew;
      }
      else if (itNew == it_end || indices.back() < (*itNew)) {
        if (elements.back() != maxValue) {
          n = nm->mkNode(kind::STORE, n, indices.back(), elements.back());
        }
        indices.pop_back();
        elements.pop_back();
      }
    }
    return n;
  }

 public:
  RewriteResponse postRewrite(TNode node) override
  {
    Trace("arrays-postrewrite") << "Arrays::postRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SELECT: {
        TNode store = node[0];
        TNode index = node[1];
        Node n;
        bool val;
        while (store.getKind() == kind::STORE) {
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            n = Rewriter::rewrite(mkEqNode(store[1], index));
            if (n.getKind() != kind::CONST_BOOLEAN) {
              break;
            }
            val = n.getConst<bool>();
          }
          if (val) {
            // select(store(a,i,v),j) = v if i = j
            Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << store[2] << std::endl;
            return RewriteResponse(REWRITE_DONE, store[2]);
          }
          // select(store(a,i,v),j) = select(a,j) if i /= j
          store = store[0];
        }
        if (store.getKind() == kind::STORE_ALL) {
          // select(store_all(v),i) = v
          ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
          n = storeAll.getValue();
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << n << std::endl;
          Assert(n.isConst());
          return RewriteResponse(REWRITE_DONE, n);
        }
        else if (store != node[0]) {
          n = NodeManager::currentNM()->mkNode(kind::SELECT, store, index);
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << n << std::endl;
          return RewriteResponse(REWRITE_DONE, n);
        }
        break;
      }
      case kind::STORE: {
        TNode store = node[0];
        TNode value = node[2];
        // store(a,i,select(a,i)) = a
        if (value.getKind() == kind::SELECT &&
            value[0] == store &&
            value[1] == node[1]) {
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << store << std::endl;
          return RewriteResponse(REWRITE_DONE, store);
        }
        TNode index = node[1];
        if (store.isConst() && index.isConst() && value.isConst()) {
          // normalize constant
          Node n = normalizeConstant(node);
          Assert(n.isConst());
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << n << std::endl;
          return RewriteResponse(REWRITE_DONE, n);
        }
        if (store.getKind() == kind::STORE) {
          // store(store(a,i,v),j,w)
          bool val;
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            Node eqRewritten = Rewriter::rewrite(mkEqNode(store[1], index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << node << std::endl;
              return RewriteResponse(REWRITE_DONE, node);
            }
            val = eqRewritten.getConst<bool>();
          }
          NodeManager* nm = NodeManager::currentNM();
          if (val) {
            // store(store(a,i,v),i,w) = store(a,i,w)
            Node result = nm->mkNode(kind::STORE, store[0], index, value);
            Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << result << std::endl;
            return RewriteResponse(REWRITE_AGAIN, result);
          }
          else if (index < store[1]) {
            // store(store(a,i,v),j,w) = store(store(a,j,w),i,v)
            //    IF i != j and j comes before i in the ordering
            std::vector<TNode> indices;
            std::vector<TNode> elements;
            indices.push_back(store[1]);
            elements.push_back(store[2]);
            store = store[0];
            Node n;
            while (store.getKind() == kind::STORE) {
              if (index == store[1]) {
                val = true;
              }
              else if (index.isConst() && store[1].isConst()) {
                val = false;
              }
              else {
                n = Rewriter::rewrite(mkEqNode(store[1], index));
                if (n.getKind() != kind::CONST_BOOLEAN) {
                  break;
                }
                val = n.getConst<bool>();
              }
              if (val) {
                store = store[0];
                break;
              }
              else if (!(index < store[1])) {
                break;
              }
              indices.push_back(store[1]);
              elements.push_back(store[2]);
              store = store[0];
            }
            if (value.getKind() == kind::SELECT &&
                value[0] == store &&
                value[1] == index) {
              n = store;
            }
            else {
              n = nm->mkNode(kind::STORE, store, index, value);
            }
            while (!indices.empty()) {
              n = nm->mkNode(kind::STORE, n, indices.back(), elements.back());
              indices.pop_back();
              elements.pop_back();
            }
            Assert(n != node);
            Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << n << std::endl;
            return RewriteResponse(REWRITE_AGAIN, n);
          }
        }
        break;
      }
      case kind::EQUAL:{
        if(node[0] == node[1]) {
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning true" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        else if (node[0].isConst() && node[1].isConst()) {
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning false" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
        }
        if (node[0] > node[1]) {
          Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
          Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << newNode << std::endl;
          return RewriteResponse(REWRITE_DONE, newNode);
        }
        break;
      }
      default:
        break;
    }
    Trace("arrays-postrewrite") << "Arrays::postRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse preRewrite(TNode node) override
  {
    Trace("arrays-prerewrite") << "Arrays::preRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SELECT: {
        TNode store = node[0];
        TNode index = node[1];
        Node n;
        bool val;
        while (store.getKind() == kind::STORE) {
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            n = Rewriter::rewrite(mkEqNode(store[1], index));
            if (n.getKind() != kind::CONST_BOOLEAN) {
              break;
            }
            val = n.getConst<bool>();
          }
          if (val) {
            // select(store(a,i,v),j) = v if i = j
            Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << store[2] << std::endl;
            return RewriteResponse(REWRITE_AGAIN, store[2]);
          }
          // select(store(a,i,v),j) = select(a,j) if i /= j
          store = store[0];
        }
        if (store.getKind() == kind::STORE_ALL) {
          // select(store_all(v),i) = v
          ArrayStoreAll storeAll = store.getConst<ArrayStoreAll>();
          n = storeAll.getValue();
          Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << n << std::endl;
          Assert(n.isConst());
          return RewriteResponse(REWRITE_DONE, n);
        }
        else if (store != node[0]) {
          n = NodeManager::currentNM()->mkNode(kind::SELECT, store, index);
          Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << n << std::endl;
          return RewriteResponse(REWRITE_DONE, n);
        }
        break;
      }
      case kind::STORE: {
        TNode store = node[0];
        TNode value = node[2];
        // store(a,i,select(a,i)) = a
        if (value.getKind() == kind::SELECT &&
            value[0] == store &&
            value[1] == node[1]) {
          Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << store << std::endl;
          return RewriteResponse(REWRITE_AGAIN, store);
        }
        if (store.getKind() == kind::STORE) {
          // store(store(a,i,v),j,w)
          TNode index = node[1];
          bool val;
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            Node eqRewritten = Rewriter::rewrite(mkEqNode(store[1], index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              break;
            }
            val = eqRewritten.getConst<bool>();
          }
          NodeManager* nm = NodeManager::currentNM();
          if (val) {
            // store(store(a,i,v),i,w) = store(a,i,w)
            Node newNode = nm->mkNode(kind::STORE, store[0], index, value);
            Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << newNode << std::endl;
            return RewriteResponse(REWRITE_DONE, newNode);
          }
        }
        break;
      }
      case kind::EQUAL:{
        if(node[0] == node[1]) {
          Trace("arrays-prerewrite") << "Arrays::preRewrite returning true" << std::endl;
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        break;
      }
      default:
        break;
    }

    Trace("arrays-prerewrite") << "Arrays::preRewrite returning " << node << std::endl;
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

}; /* class TheoryArraysRewriter */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
