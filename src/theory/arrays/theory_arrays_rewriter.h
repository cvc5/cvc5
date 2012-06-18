/*********************                                                        */
/*! \file theory_arrays_rewriter.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: barrett, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H

#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArraysRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    Trace("arrays-postrewrite") << "Arrays::postRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SELECT: {
        TNode store = node[0];
        if (store.getKind() == kind::STORE) {
          // select(store(a,i,v),j)
          TNode index = node[1];
          bool val;
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            Node eqRewritten = Rewriter::rewrite(store[1].eqNode(index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              break;
            }
            val = eqRewritten.getConst<bool>();
            if (val) {
              // select(store(a,i,v),i) = v
              return RewriteResponse(REWRITE_DONE, store[2]);
            }
            else {
              // select(store(a,i,v),j) = select(a,j) if i /= j
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
                  n = Rewriter::rewrite(store[1].eqNode(index));
                  if (n.getKind() != kind::CONST_BOOLEAN) {
                    break;
                  }
                  val = n.getConst<bool>();
                }
                if (val) {
                  return RewriteResponse(REWRITE_DONE, store[2]);
                }
                store = store[0];
              }
              n = NodeManager::currentNM()->mkNode(kind::SELECT, store, index);
              return RewriteResponse(REWRITE_DONE, n);
            }
          }
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
          return RewriteResponse(REWRITE_DONE, store);
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
            Node eqRewritten = Rewriter::rewrite(store[1].eqNode(index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              return RewriteResponse(REWRITE_DONE, node);
            }
            val = eqRewritten.getConst<bool>();
          }
          NodeManager* nm = NodeManager::currentNM();
          if (val) {
            // store(store(a,i,v),i,w) = store(a,i,w)
            return RewriteResponse(REWRITE_DONE, nm->mkNode(kind::STORE, store[0], index, value));
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
                n = Rewriter::rewrite(store[1].eqNode(index));
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
            n = nm->mkNode(kind::STORE, store, index, value);
            while (!indices.empty()) {
              n = nm->mkNode(kind::STORE, n, indices.back(), elements.back());
              indices.pop_back();
              elements.pop_back();
            }
            return RewriteResponse(REWRITE_DONE, n);
          }
        }
        break;
      }
      case kind::EQUAL:
      case kind::IFF: {
        if(node[0] == node[1]) {
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        if (node[0] > node[1]) {
          Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
          return RewriteResponse(REWRITE_DONE, newNode);
        }
        break;
      }
      default:
        break;
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline RewriteResponse preRewrite(TNode node) {
    Trace("arrays-prerewrite") << "Arrays::preRewrite start " << node << std::endl;
    switch (node.getKind()) {
      case kind::SELECT: {
        TNode store = node[0];
        if (store.getKind() == kind::STORE) {
          // select(store(a,i,v),j)
          TNode index = node[1];
          bool val;
          if (index == store[1]) {
            val = true;
          }
          else if (index.isConst() && store[1].isConst()) {
            val = false;
          }
          else {
            Node eqRewritten = Rewriter::rewrite(store[1].eqNode(index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              break;
            }
            val = eqRewritten.getConst<bool>();
            if (val) {
              // select(store(a,i,v),i) = v
              return RewriteResponse(REWRITE_DONE, store[2]);
            }
            else {
              // select(store(a,i,v),j) = select(a,j) if i /= j
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
                  n = Rewriter::rewrite(store[1].eqNode(index));
                  if (n.getKind() != kind::CONST_BOOLEAN) {
                    break;
                  }
                  val = n.getConst<bool>();
                }
                if (val) {
                  return RewriteResponse(REWRITE_DONE, store[2]);
                }
                store = store[0];
              }
              n = NodeManager::currentNM()->mkNode(kind::SELECT, store, index);
              return RewriteResponse(REWRITE_DONE, n);
            }
          }
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
          return RewriteResponse(REWRITE_DONE, store);
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
            Node eqRewritten = Rewriter::rewrite(store[1].eqNode(index));
            if (eqRewritten.getKind() != kind::CONST_BOOLEAN) {
              return RewriteResponse(REWRITE_DONE, node);
            }
            val = eqRewritten.getConst<bool>();
          }
          NodeManager* nm = NodeManager::currentNM();
          if (val) {
            // store(store(a,i,v),i,w) = store(a,i,w)
            return RewriteResponse(REWRITE_DONE, nm->mkNode(kind::STORE, store[0], index, value));
          }
          else if (index.isConst() && store[1].isConst()) {
            std::map<TNode, TNode> elements;
            elements[index] = value;
            elements[store[1]] = store[2];
            store = store[0];
            Node n;
            while (store.getKind() == kind::STORE) {
              if (!store[1].isConst()) {
                break;
              }
              if (elements.find(store[1]) != elements.end()) {
                elements[store[1]] = store[2];
              }
              store = store[0];
            }
            std::map<TNode, TNode>::iterator it = elements.begin();
            std::map<TNode, TNode>::iterator iend = elements.end();
            for (; it != iend; ++it) {
              n = nm->mkNode(kind::STORE, store, (*it).first, (*it).second);
            }
            return RewriteResponse(REWRITE_DONE, n);
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
                n = Rewriter::rewrite(store[1].eqNode(index));
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
            n = nm->mkNode(kind::STORE, store, index, value);
            while (!indices.empty()) {
              n = nm->mkNode(kind::STORE, n, indices.back(), elements.back());
              indices.pop_back();
              elements.pop_back();
            }
            return RewriteResponse(REWRITE_DONE, n);
          }
        }
        break;
      }
      case kind::EQUAL:
      case kind::IFF: {
        if(node[0] == node[1]) {
          return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
        }
        break;
      }
      default:
        break;
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

};/* class TheoryArraysRewriter */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_REWRITER_H */
