/*********************                                                        */
/*! \file arithvar_set.h
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


#ifndef __CVC4__THEORY__ARITH__ARTIHVAR_SET_H
#define __CVC4__THEORY__ARITH__ARTIHVAR_SET_H

namespace CVC4 {
namespace theory {
namespace arith {

/**
 * This is an abstraction of a set of ArithVars.
 * This class is designed to provide constant time insertion, deletion, and element_of
 * and fast iteration.
 * The cost of doing this is that it takes O(M) where M is the total number
 * of ArithVars in memory.
 */

class ArithVarSet {
private:
  typedef std::vector<ArithVar> VarList;
  //List of the ArithVars in the set.
  VarList d_list;

  //Each ArithVar in the set is mapped to its position in d_list.
  //Each ArithVar not in the set is mapped to ARITHVAR_SENTINEL
  std::vector<unsigned> d_posVector;

public:
  typedef VarList::const_iterator iterator;

 ArithVarSet() :  d_list(), d_posVector() {}

  size_t size() const {
    return d_list.size();
  }

  size_t allocated() const {
    return d_posVector.size();
  }

  void increaseSize(ArithVar max){
    Assert(max >= allocated());
    d_posVector.resize(max+1, ARITHVAR_SENTINEL);
  }

  void increaseSize(){
    increaseSize(allocated());
  }

  bool isMember(ArithVar x) const{
    Assert(x <  allocated());
    return d_posVector[x] != ARITHVAR_SENTINEL;
  }

  /** Invalidates iterators */
  void init(ArithVar x, bool val) {
    Assert(x >= size());
    increaseSize(x);
    if(val){
      add(x);
    }
  }

  /** Invalidates iterators */
  void add(ArithVar x){
    Assert(!isMember(x));
    d_posVector[x] = size();
    d_list.push_back(x);
  }

  iterator begin() const{ return d_list.begin(); }
  iterator end() const{ return d_list.end(); }


  /** Invalidates iterators */
  void remove(ArithVar x){
    Assert(isMember(x));
    swapToBack(x);
    d_posVector[x] = ARITHVAR_SENTINEL;
    d_list.pop_back();
  }

 private:

  /** This should be true of all x < allocated() after every operation. */
  bool wellFormed(ArithVar x){
    if(d_posVector[x] == ARITHVAR_SENTINEL){
      return true;
    }else{
      return d_list[d_posVector[x]] == x;
    }
  }

  /** Swaps a member x to the back of d_list. */
  void swapToBack(ArithVar x){
    Assert(isMember(x));

    unsigned currentPos = d_posVector[x];
    ArithVar atBack = d_list.back();

    d_list[currentPos] = atBack;
    d_posVector[atBack] = currentPos;

    d_list[size() - 1] = x;
    d_posVector[x] = size() - 1;
  }
};

}; /* namespace arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__ARTIHVAR_SET_H */
