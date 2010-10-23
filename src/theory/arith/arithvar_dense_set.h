/*********************                                                        */
/*! \file arithvar_dense_set.h
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

#include <vector>
#include "theory/arith/arith_utilities.h"


#ifndef __CVC4__THEORY__ARITH__ARTIHVAR_DENSE_SET_H
#define __CVC4__THEORY__ARITH__ARTIHVAR_DENSE_SET_H

namespace CVC4 {
namespace theory {
namespace arith {

class ArithVarDenseSet {
private:
  std::vector<bool> d_set;

public:
  ArithVarDenseSet() : d_set() {}

  size_t size() const {
    return d_set.size();
  }

  void increaseSize(ArithVar max){
    Assert(max >= size());
    d_set.resize(max+1, false);
  }

  bool isMember(ArithVar x) const{
    return d_set[x];
  }

  void init(ArithVar x, bool val) {
    Assert(x >= size());
    increaseSize(x);
    d_set[x] = val;
  }

  void add(ArithVar x){
    Assert(!isMember(x));
    d_set[x] = true;
  }

  void remove(ArithVar x){
    Assert(isMember(x));
    d_set[x] = false;
  }
};

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__ARTIHVAR_DENSE_SET_H */
