/*********************                                                        */
/*! \file basic.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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


#include "expr/node.h"
#include "expr/attribute.h"


#ifndef __CVC4__THEORY__ARITH__BASIC_H
#define __CVC4__THEORY__ARITH__BASIC_H

namespace CVC4 {
namespace theory {
namespace arith {

struct IsBasicAttrID;

typedef expr::Attribute<IsBasicAttrID, bool> IsBasic;


inline bool isBasic(TNode x){
  return x.getAttribute(IsBasic());
}

inline void makeBasic(TNode x){
  return x.setAttribute(IsBasic(), true);
}

inline void makeNonbasic(TNode x){
  return x.setAttribute(IsBasic(), false);
}

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__BASIC_H */
