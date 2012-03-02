/*********************                                                        */
/*! \file arithvar_set.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARTIHVAR_SET_H
#define __CVC4__THEORY__ARITH__ARTIHVAR_SET_H

#include <vector>
#include "theory/arith/arithvar.h"
#include "context/context.h"
#include "context/cdlist.h"


namespace CVC4 {
namespace theory {
namespace arith {

/**
 * This is an abstraction of a set of ArithVars.
 * This class is designed to provide constant time insertion, deletion, and element_of
 * and fast iteration.
 *
 * ArithVarSets come in 2 varieties: ArithVarSet, and PermissiveBackArithVarSet.
 * The default ArithVarSet assumes that there is no knowledge assumed about ArithVars
 * that are greater than allocated(). Asking isMember() of such an ArithVar
 * is an assertion failure. The cost of doing this is that it takes O(M)
 * where M is the total number of ArithVars in memory.
 *
 * PermissiveBackArithVarSet means that all ArithVars are implicitly not in the set,
 * and any ArithVar past the end of d_posVector is not in the set.
 * A permissiveBack allows for less memory to be consumed on average.
 *
 */
template <bool permissiveBack>
class ArithVarSetImpl {
public:
  typedef std::vector<ArithVar> VarList;
private:
  //List of the ArithVars in the set.
  VarList d_list;

  //Each ArithVar in the set is mapped to its position in d_list.
  //Each ArithVar not in the set is mapped to ARITHVAR_SENTINEL
  std::vector<unsigned> d_posVector;

public:
  typedef VarList::const_iterator const_iterator;

  ArithVarSetImpl() :  d_list(), d_posVector() {}

  size_t size() const {
    return d_list.size();
  }
  bool empty() const {
    return d_list.empty();
  }

  size_t allocated() const {
    return d_posVector.size();
  }

  void purge() {
    for(VarList::const_iterator i=d_list.begin(), endIter=d_list.end();i!= endIter; ++i){
      d_posVector[*i] = ARITHVAR_SENTINEL;
    }
    d_list.clear();
    Assert(empty());
  }

  void increaseSize(ArithVar max){
    Assert(max >= allocated());
    d_posVector.resize(max+1, ARITHVAR_SENTINEL);
  }

  void increaseSize(){
    increaseSize(allocated());
  }

  bool isMember(ArithVar x) const{
    if(permissiveBack && x >=  allocated()){
      return false;
    }else{
      Assert(x <  allocated());
      return d_posVector[x] != ARITHVAR_SENTINEL;
    }
  }

  /** Invalidates iterators */
  void init(ArithVar x, bool val) {
    Assert(x >= allocated());
    increaseSize(x);
    if(val){
      add(x);
    }
  }

  /** Invalidates iterators */
  void add(ArithVar x){
    Assert(!isMember(x));
    if(permissiveBack && x >=  allocated()){
      increaseSize(x);
    }
    d_posVector[x] = size();
    d_list.push_back(x);
  }

  const_iterator begin() const{ return d_list.begin(); }
  const_iterator end() const{ return d_list.end(); }

  /**
   * Invalidates iterators.
   * Adds x to the set if it is not already in the set.
   */
  void softAdd(ArithVar x){
    if(!isMember(x)){
      add(x);
    }
  }

  const VarList& getList() const{
    return d_list;
  }

  /** Invalidates iterators */
  void remove(ArithVar x){
    Assert(isMember(x));
    swapToBack(x);
    Assert(d_list.back() == x);
    pop_back();
  }

  ArithVar pop_back() {
    Assert(!empty());
    ArithVar atBack = d_list.back();
    d_posVector[atBack] = ARITHVAR_SENTINEL;
    d_list.pop_back();
    return atBack;
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

typedef ArithVarSetImpl<false> ArithVarSet;
typedef ArithVarSetImpl<true> PermissiveBackArithVarSet;


/**
 * ArithVarMultiset
 */
class ArithVarMultiset {
public:
  typedef std::vector<ArithVar> VarList;
private:
  //List of the ArithVars in the multi set.
  VarList d_list;

  //Each ArithVar in the set is mapped to its position in d_list.
  //Each ArithVar not in the set is mapped to ARITHVAR_SENTINEL
  std::vector<unsigned> d_posVector;

  //Count of the number of elements in the array
  std::vector<unsigned> d_counts;

public:
  typedef VarList::const_iterator const_iterator;

  ArithVarMultiset() :  d_list(), d_posVector() {}

  size_t size() const {
    return d_list.size();
  }

  bool empty() const {
    return d_list.empty();
  }

  size_t allocated() const {
    Assert(d_posVector.size() == d_counts.size());
    return d_posVector.size();
  }

  void purge() {
    for(VarList::const_iterator i=d_list.begin(), endIter=d_list.end(); i!= endIter; ++i){
      d_posVector[*i] = ARITHVAR_SENTINEL;
      d_counts[*i] = 0;
    }
    d_list.clear();
    Assert(empty());
  }

  void increaseSize(ArithVar max){
    Assert(max >= allocated());
    d_posVector.resize(max+1, ARITHVAR_SENTINEL);
    d_counts.resize(max+1, 0);
  }

  void increaseSize(){
    increaseSize(allocated());
  }

  bool isMember(ArithVar x) const{
    if( x >=  allocated()){
      return false;
    }else{
      Assert(x <  allocated());
      return d_posVector[x] != ARITHVAR_SENTINEL;
    }
  }

  /**
   * Invalidates iterators.
   */
  void addMultiset(ArithVar x){
    if( x >=  allocated()){
      increaseSize(x);
    }
    if(d_counts[x] == 0){
      d_posVector[x] = size();
      d_list.push_back(x);
    }
    d_counts[x]++;
  }

  unsigned count(ArithVar x){
    if( x >=  allocated()){
      return 0;
    }else{
      return d_counts[x];
    }
  }

  const_iterator begin() const{ return d_list.begin(); }
  const_iterator end() const{ return d_list.end(); }

  const VarList& getList() const{
    return d_list;
  }

  /** Invalidates iterators */
  void remove(ArithVar x){
    Assert(isMember(x));
    swapToBack(x);
    Assert(d_list.back() == x);
    pop_back();
  }

  ArithVar pop_back() {
    Assert(!empty());
    ArithVar atBack = d_list.back();
    d_posVector[atBack] = ARITHVAR_SENTINEL;
    d_counts[atBack] = 0;
    d_list.pop_back();
    return atBack;
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

class CDArithVarSet {
private:

  class RemoveIntWrapper{
  private:
    ArithVar d_var;
    ArithVarCallBack& d_onDestruction;

  public:
    RemoveIntWrapper(ArithVar v, ArithVarCallBack& onDestruction):
      d_var(v), d_onDestruction(onDestruction)
    {}

    ~RemoveIntWrapper(){
      d_onDestruction.callback(d_var);
    }
  };

  std::vector<bool> d_set;
  context::CDList<RemoveIntWrapper> d_list;

  class OnDestruction : public ArithVarCallBack {
  private:
    std::vector<bool>& d_set;
  public:
    OnDestruction(std::vector<bool>& set):
      d_set(set)
    {}

    void callback(ArithVar x){
      Assert(x < d_set.size());
      d_set[x] = false;
    }
  };

  OnDestruction d_callback;

public:
  CDArithVarSet(context::Context* c) :
    d_list(c), d_callback(d_set)
  { }

  /** This cannot be const as garbage collection is done lazily. */
  bool contains(ArithVar x) const{
    if(x < d_set.size()){
      return d_set[x];
    }else{
      return false;
    }
  }

  void insert(ArithVar x){
    Assert(!contains(x));
    if(x >= d_set.size()){
      d_set.resize(x+1, false);
    }
    d_list.push_back(RemoveIntWrapper(x, d_callback));
    d_set[x] = true;
  }
};


}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__ARTIHVAR_SET_H */
