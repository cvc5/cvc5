/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A let binding.
 */

#include "cvc5_private.h"

#ifndef CVC5__PRINTER__LET_BINDING_H
#define CVC5__PRINTER__LET_BINDING_H

#include <vector>

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {

/**
 * A flexible let binding class. This class provides functionalities for
 * printing letified terms. A simple use case is the following for Node n
 * and LetBinding lbind:
 * ```
 *   std::vector<Node> letList;
 *   lbind.letify(n, letList);
 * ```
 * Now, letList contains a list of subterms of n that should be letified based
 * on the threshold value passed to this class where a value n>0 indicates that
 * terms with n or more occurrences should be letified.
 *
 * The above is equivalent to:
 * ```
 *   std::vector<Node> letList;
 *   lbind.pushScope();
 *   lbind.process(n);
 *   lbind.letify(letList);
 * ```
 * In fact, multiple terms can be passed to calls to process, in which case the
 * counting is cumulative.
 *
 * All quantified formulas are treated as black boxes. This class can be used
 * to letify terms with quantifiers, where multiple calls to pushScope /
 * popScope can be used. In particular, consider:
 * ```
 *   std::vector<Node> letList1;
 *   lbind.letify(n1, letList1);
 *   std::vector<Node> letList2;
 *   lbind.letify(n2, letList2);
 *   ...
 *   lbind.popScope();
 *   lbind.popScope();
 * ```
 * In a typical use case, n2 is the body of a quantified formula that is a
 * subterm of n1. We have that letList2 is the list of subterms of n2 that
 * should be letified, assuming that we have already have let definitions
 * given by letList1.
 *
 * Internally, a let binding is a list and a map that can be printed as a let
 * expression. In particular, the list d_letList is ordered such that
 * d_letList[i] does not contain subterm d_letList[j] for j>i.
 * It is intended that d_letList contains only unique nodes. Each node
 * in d_letList is mapped to a unique identifier in d_letMap.
 *
 * Notice that this class will *not* use introduced let symbols when converting
 * the bodies of quantified formulas. Consider the formula:
 * (let ((Q (forall ((x Int)) (= x (+ a a))))) (and (= (+ a a) (+ a a)) Q Q))
 * where "let" above is from the user. When this is letified by this class,
 * note that (+ a a) occurs as a subterm of Q, however it is not seen until
 * after we have seen Q twice, since we traverse in reverse topological order.
 * Since we do not traverse underneath quantified formulas, this means that Q
 * may be marked as a term-to-letify before (+ a a), which leads to violation
 * of the above invariant concerning containment. Thus, when converting, if
 * a let symbol is introduced for (+ a a), we will not replace the occurence
 * of (+ a a) within Q. Instead, the user of this class is responsible for
 * letifying the bodies of quantified formulas independently.
 */
class LetBinding
{
  using NodeList = context::CDList<Node>;
  using NodeIdMap = context::CDHashMap<Node, uint32_t>;

 public:
  LetBinding(uint32_t thresh = 2);
  /** Get threshold */
  uint32_t getThreshold() const;
  /**
   * This updates this let binding to consider the counts for node n.
   */
  void process(Node n);
  /**
   * This pushes a scope, computes the letification for n, adds the (new) terms
   * that must be letified in this context to letList.
   *
   * Notice that this method does not traverse inside of closures.
   *
   * @param n The node to letify
   * @param letList The list of terms that should be letified within n. This
   * list is ordered in such a way that letList[i] does not contain subterm
   * letList[j] for j>i.
   */
  void letify(Node n, std::vector<Node>& letList);
  /**
   * Same as above, without a node to letify.
   */
  void letify(std::vector<Node>& letList);
  /** Push scope */
  void pushScope();
  /** Pop scope for n, reverts the state change of the above method */
  void popScope();
  /**
   * @return the identifier for node n, or 0 if it does not have one.
   */
  uint32_t getId(Node n) const;
  /**
   * Convert n based on the state of the let binding. This replaces all
   * letified subterms of n with a fresh variable whose name prefix is the
   * given one.
   *
   * @param n The node to convert
   * @param prefix The prefix of variables to convert
   * @param letTop Whether we letify n itself
   * @return the converted node.
   */
  Node convert(Node n, const std::string& prefix, bool letTop = true) const;

 private:
  /**
   * Compute the count of sub nodes in n, store in d_count. Additionally,
   * store each node in the domain of d_count in an order in d_visitList
   * such that d_visitList[i] does not contain sub d_visitList[j] for j>i.
   */
  void updateCounts(Node n);
  /**
   * Convert a count to a let binding.
   */
  void convertCountToLet();
  /** The dag threshold */
  uint32_t d_thresh;
  /** An internal context */
  context::Context d_context;
  /** Visit list */
  NodeList d_visitList;
  /** Count */
  NodeIdMap d_count;
  /** The let list */
  NodeList d_letList;

 protected:
  /** The let map */
  NodeIdMap d_letMap;
};

}  // namespace cvc5::internal

#endif
