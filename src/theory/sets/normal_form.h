/*********************                                                        */
/*! \file normal_form.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Normal form for set constants.
 **
 ** Normal form for set constants.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__NORMAL_FORM_H
#define __CVC4__THEORY__SETS__NORMAL_FORM_H

namespace CVC4 {
namespace theory {
namespace sets {

class NormalForm {
public:

  static Node elementsToSet(std::set<TNode> elements, TypeNode setType)
  {
    NodeManager* nm = NodeManager::currentNM();

    if(elements.size() == 0) {
      return nm->mkConst(EmptySet(nm->toType(setType)));
    } else {
      typeof(elements.begin()) it = elements.begin();
      Node cur = nm->mkNode(kind::SINGLETON, *it);
      while( ++it != elements.end() ) {
        cur = nm->mkNode(kind::UNION, cur,
                         nm->mkNode(kind::SINGLETON, *it));
      }
      return cur;
    }
  }

};

}
}
}

#endif
