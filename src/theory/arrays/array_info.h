/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Clark Barrett, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains additional classes to store context dependent information
 * for each term of type array.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARRAYS__ARRAY_INFO_H
#define CVC5__THEORY__ARRAYS__ARRAY_INFO_H

#include <tuple>
#include <unordered_map>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

typedef context::CDList<TNode> CTNodeList;
using RowLemmaType = std::tuple<TNode, TNode, TNode, TNode>;

struct RowLemmaTypeHashFunction {
  size_t operator()(const RowLemmaType& q) const {
    TNode n1, n2, n3, n4;
    std::tie(n1, n2, n3, n4) = q;
    return (size_t) (n1.getId()*0x9e3779b9 + n2.getId()*0x30000059 +
        n3.getId()*0x60000005 + n4.getId()*0x07FFFFFF);

  }
};/* struct RowLemmaTypeHashFunction */

void printList (CTNodeList* list);

bool inList(const CTNodeList* l, const TNode el);

/**
 * Small class encapsulating the information
 * in the map. It's a class and not a struct to
 * call the destructor.
 */

class Info {
public:
 context::CDO<bool> isNonLinear;
 context::CDO<bool> rIntro1Applied;
 context::CDO<TNode> modelRep;
 context::CDO<TNode> constArr;
 context::CDO<TNode> weakEquivPointer;
 context::CDO<TNode> weakEquivIndex;
 context::CDO<TNode> weakEquivSecondary;
 context::CDO<TNode> weakEquivSecondaryReason;
 CTNodeList* indices;
 CTNodeList* stores;
 CTNodeList* in_stores;

 Info(context::Context* c);
 ~Info();

 /**
  * prints the information
  */
 void print() const
 {
   Assert(indices != NULL && stores != NULL && in_stores != NULL);
   Trace("arrays-info") << "  indices   ";
   printList(indices);
   Trace("arrays-info") << "  stores ";
   printList(stores);
   Trace("arrays-info") << "  in_stores ";
   printList(in_stores);
 }
};/* class Info */

typedef std::unordered_map<Node, Info*> CNodeInfoMap;

/**
 * Class keeping track of the following information for canonical
 * representatives of type array [a] :
 *    indices at which it is being read (all i for which there is a
 *            term of the form SELECT a i)
 *    all store terms in the congruence class
 *    stores in which it appears (terms of the form STORE a _ _ )
 *
 */
class ArrayInfo {
private:
 context::Context* ct;
 CNodeInfoMap info_map;

 CTNodeList* emptyList;

 /* == STATISTICS == */

 /** time spent in preregisterTerm() */
 TimerStat d_mergeInfoTimer;
 AverageStat d_avgIndexListLength;
 AverageStat d_avgStoresListLength;
 AverageStat d_avgInStoresListLength;
 IntStat d_listsCount;
 IntStat d_callsMergeInfo;
 IntStat d_maxList;
 SizeStat<CNodeInfoMap> d_tableSize;

 /**
  * checks if a certain element is in the list l
  * FIXME: better way to check for duplicates?
  */

 /**
  * helper method that merges two lists into the first
  * without adding duplicates
  */
 void mergeLists(CTNodeList* la, const CTNodeList* lb) const;

public:
  const Info* emptyInfo;

  ArrayInfo(StatisticsRegistry& sr,
            context::Context* c,
            std::string statisticsPrefix = "");

  ~ArrayInfo();

  /**
   * adds the node a to the map if it does not exist
   * and it initializes the info. checks for duplicate i's
   */
  void addIndex(const Node a, const TNode i);
  void addStore(const Node a, const TNode st);
  void addInStore(const TNode a, const TNode st);

  void setNonLinear(const TNode a);
  void setRIntro1Applied(const TNode a);
  void setModelRep(const TNode a, const TNode rep);

  void setConstArr(const TNode a, const TNode constArr);
  void setWeakEquivPointer(const TNode a, const TNode pointer);
  void setWeakEquivIndex(const TNode a, const TNode index);
  void setWeakEquivSecondary(const TNode a, const TNode secondary);
  void setWeakEquivSecondaryReason(const TNode a, const TNode reason);
  /**
   * Returns the information associated with TNode a
   */

  const Info* getInfo(const TNode a) const;

  const bool isNonLinear(const TNode a) const;

  const bool rIntro1Applied(const TNode a) const;

  const TNode getModelRep(const TNode a) const;

  const TNode getConstArr(const TNode a) const;
  const TNode getWeakEquivPointer(const TNode a) const;
  const TNode getWeakEquivIndex(const TNode a) const;
  const TNode getWeakEquivSecondary(const TNode a) const;
  const TNode getWeakEquivSecondaryReason(const TNode a) const;

  const CTNodeList* getIndices(const TNode a) const;

  const CTNodeList* getStores(const TNode a) const;

  const CTNodeList* getInStores(const TNode a) const;

  /**
   * merges the information of  nodes a and b
   * the nodes do not have to actually be in the map.
   * pre-condition
   *  a should be the canonical representative of b
   */
  void mergeInfo(const TNode a, const TNode b);
};/* class ArrayInfo */

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARRAYS__ARRAY_INFO_H */
