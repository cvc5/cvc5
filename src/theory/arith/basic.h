/*********************                                                        */
/*! \file basic.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
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

class IsBasicManager {
private:
  std::vector<bool> d_basic;

public:
  IsBasicManager() : d_basic() {}

  void init(ArithVar var, bool value){
    Assert(var == d_basic.size());
    d_basic.push_back(value);
  }

  bool isBasic(ArithVar x) const{
    return d_basic[x];
  }

  void makeBasic(ArithVar x){
    Assert(!isBasic(x));
    d_basic[x] = true;
  }

  void makeNonbasic(ArithVar x){
    Assert(isBasic(x));
    d_basic[x] = false;
  }
};

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__BASIC_H */
