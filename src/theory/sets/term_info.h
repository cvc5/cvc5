/*********************                                                        */
/*! \file term_info.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
  CDTNodeList* parents;

  TheorySetsTermInfo(context::Context* c)
  {
    elementsInThisSet = new(true)CDTNodeList(c);
    elementsNotInThisSet = new(true)CDTNodeList(c);
    parents = new(true)CDTNodeList(c);
  }

  void addToElementList(TNode n, bool polarity) {
    if(polarity) elementsInThisSet -> push_back(n);
    else elementsNotInThisSet -> push_back(n);
  }

  ~TheorySetsTermInfo() {
    elementsInThisSet -> deleteSelf();
    elementsNotInThisSet -> deleteSelf();
    parents -> deleteSelf();
  }
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
