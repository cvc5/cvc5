/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Normal form for set constants.
 **
 ** Normal form for set constants.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__NORMAL_FORM_H
#define CVC4__THEORY__SETS__NORMAL_FORM_H

namespace CVC4 {
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
      Node cur = nm->mkNode(kind::SINGLETON, *it);
      while (++it != elements.end())
      {
        cur = nm->mkNode(kind::UNION, nm->mkNode(kind::SINGLETON, *it), cur);
      }
      return cur;
    }
  }

  /**
   * Returns true if n is considered a to be a (canonical) constant set value.
   * A canonical set value is one whose AST is:
   *   (union (singleton c1) ... (union (singleton c_{n-1}) (singleton c_n))))
   * where c1 ... cn are constants and the node identifier of these constants
   * are such that:
   *   c1 > ... > cn.
   * Also handles the corner cases of empty set and singleton set.
   */
  static bool checkNormalConstant(TNode n) {
    Debug("sets-checknormal") << "[sets-checknormal] checkNormal " << n << " :"
                              << std::endl;
    if (n.getKind() == kind::EMPTYSET) {
      return true;
    } else if (n.getKind() == kind::SINGLETON) {
      return n[0].isConst();
    } else if (n.getKind() == kind::UNION) {
      // assuming (union {SmallestNodeID} ... (union {BiggerNodeId} ...

      Node orig = n;
      TNode prvs;
      // check intermediate nodes
      while (n.getKind() == kind::UNION)
      {
        if (n[0].getKind() != kind::SINGLETON || !n[0][0].isConst())
        {
          // not a constant
          Trace("sets-isconst") << "sets::isConst: " << orig << " not due to "
                                << n[0] << std::endl;
          return false;
        }
        Debug("sets-checknormal")
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
      if (n.getKind() != kind::SINGLETON || !n[0].isConst())
      {
        Trace("sets-isconst") << "sets::isConst: " << orig
                              << " not due to final " << n << std::endl;
        return false;
      }
      Debug("sets-checknormal")
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
    if (n.getKind() == kind::EMPTYSET) {
      return ret;
    }
    while (n.getKind() == kind::UNION) {
      Assert(n[0].getKind() == kind::SINGLETON);
      ret.insert(ret.begin(), n[0][0]);
      n = n[1];
    }
    Assert(n.getKind() == kind::SINGLETON);
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
}

#endif
