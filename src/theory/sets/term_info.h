/*********************                                                        */
/*! \file term_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Term info.
 **
 ** Term info.
 **/

#include "cvc4_private.h"

#pragma once

namespace CVC4 {
namespace theory {
namespace sets {


typedef context::CDList<TNode> CDTNodeList;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;
typedef context::CDHashSet<Node, NodeHashFunction> CDNodeSet;

class TheorySetsTermInfo {
public:
  CDTNodeList* elementsInThisSet;
  CDTNodeList* elementsNotInThisSet;
  CDTNodeList* setsContainingThisElement;
  CDTNodeList* setsNotContainingThisElement;
  CDTNodeList* parents;

  TheorySetsTermInfo(context::Context* c)
  {
    elementsInThisSet = new(true)CDTNodeList(c);
    elementsNotInThisSet = new(true)CDTNodeList(c);
    setsContainingThisElement = new(true)CDTNodeList(c);
    setsNotContainingThisElement = new(true)CDTNodeList(c);
    parents = new(true)CDTNodeList(c);
  }

  void addToElementList(TNode n, bool polarity) {
    if(polarity) elementsInThisSet -> push_back(n);
    else elementsNotInThisSet -> push_back(n);
  }

  void addToSetList(TNode n, bool polarity) {
    if(polarity) setsContainingThisElement -> push_back(n);
    else setsNotContainingThisElement -> push_back(n);
  }

  ~TheorySetsTermInfo() {
    elementsInThisSet -> deleteSelf();
    elementsNotInThisSet -> deleteSelf();
    setsContainingThisElement -> deleteSelf();
    setsNotContainingThisElement -> deleteSelf();
    parents -> deleteSelf();
  }

};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
