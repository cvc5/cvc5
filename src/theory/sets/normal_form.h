/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Normal form for set constants.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SETS__NORMAL_FORM_H
#define CVC5__THEORY__SETS__NORMAL_FORM_H

#include "expr/emptyset.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

class NormalForm {
 public:
  /**
   * Constructs a set of the form:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * from the set { c1 ... cn }, also handles empty set case, which is why
   * setType is passed to this method.
   */
  template <bool ref_count>
  static Node elementsToSet(const std::set<NodeTemplate<ref_count> >& elements,
                            TypeNode setType)
  {
    typedef typename std::set<NodeTemplate<ref_count> >::const_iterator
        ElementsIterator;
    NodeManager* nm = NodeManager::currentNM();
    if (elements.size() == 0)
    {
      return nm->mkConst(EmptySet(setType));
    }
    else
    {
      ElementsIterator it = elements.begin();
      Node cur = nm->mkNode(kind::SET_SINGLETON, *it);
      while (++it != elements.end())
      {
        Node singleton = nm->mkNode(kind::SET_SINGLETON, *it);
        cur = nm->mkNode(kind::SET_UNION, singleton, cur);
      }
      return cur;
    }
  }

  /**
   * Returns true if n is considered to be a (canonical) constant set value.
   * A canonical set value is one whose AST is:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * where c1 ... cn are constants and the node identifier of these constants
   * are such that:
   *   c1 > ... > cn.
   * Also handles the corner cases of empty set and singleton set.
   */
  static bool checkNormalConstant(TNode n) {
    Trace("sets-checknormal") << "[sets-checknormal] checkNormal " << n << " :"
                              << std::endl;
    if (n.getKind() == kind::SET_EMPTY)
    {
      return true;
    }
    else if (n.getKind() == kind::SET_SINGLETON)
    {
      return n[0].isConst();
    }
    else if (n.getKind() == kind::SET_UNION)
    {
      // assuming (union {SmallestNodeID} ... (union {BiggerNodeId} ...

      Node orig = n;
      TNode prvs;
      // check intermediate nodes
      while (n.getKind() == kind::SET_UNION)
      {
        if (n[0].getKind() != kind::SET_SINGLETON || !n[0][0].isConst())
        {
          // not a constant
          Trace("sets-isconst") << "sets::isConst: " << orig << " not due to "
                                << n[0] << std::endl;
          return false;
        }
        Trace("sets-checknormal")
            << "[sets-checknormal]              element = " << n[0][0] << " "
            << n[0][0].getId() << std::endl;
        if (!prvs.isNull() && n[0][0] >= prvs)
        {
          Trace("sets-isconst")
              << "sets::isConst: " << orig << " not due to compare " << n[0][0]
              << std::endl;
          return false;
        }
        prvs = n[0][0];
        n = n[1];
      }

      // check SmallestNodeID is smallest
      if (n.getKind() != kind::SET_SINGLETON || !n[0].isConst())
      {
        Trace("sets-isconst") << "sets::isConst: " << orig
                              << " not due to final " << n << std::endl;
        return false;
      }
      Trace("sets-checknormal")
          << "[sets-checknormal]              lst element = " << n[0] << " "
          << n[0].getId() << std::endl;
      // compare last ID
      if (n[0] < prvs)
      {
        return true;
      }
      Trace("sets-isconst")
          << "sets::isConst: " << orig << " not due to compare final " << n[0]
          << std::endl;
    }
    return false;
  }

  /**
   * Converts a set term to a std::set of its elements. This expects a set of
   * the form:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * Also handles the corner cases of empty set and singleton set.
   */
  static std::set<Node> getElementsFromNormalConstant(TNode n) {
    Assert(n.isConst());
    std::set<Node> ret;
    if (n.getKind() == kind::SET_EMPTY)
    {
      return ret;
    }
    while (n.getKind() == kind::SET_UNION)
    {
      Assert(n[0].getKind() == kind::SET_SINGLETON);
      ret.insert(ret.begin(), n[0][0]);
      n = n[1];
    }
    Assert(n.getKind() == kind::SET_SINGLETON);
    ret.insert(n[0]);
    return ret;
  }
  
  static Node mkBop( Kind k, std::vector< Node >& els, TypeNode tn, unsigned index = 0 ){
    if( index>=els.size() ){
      return NodeManager::currentNM()->mkConst(EmptySet(tn));
    }else if( index==els.size()-1 ){
      return els[index];
    }else{
      return NodeManager::currentNM()->mkNode( k, els[index], mkBop( k, els, tn, index+1 ) );
    }
  }

};
}
}
}  // namespace cvc5::internal

#endif
