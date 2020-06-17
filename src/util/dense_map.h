/*********************                                                        */
/*! \file dense_map.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is an abstraction of a Map from unsigned integers to elements of type T.
 **
 ** This is an abstraction of a Map from an unsigned integer to elements of type T.
 ** This class is designed to provide constant time insertion, deletion, element_of,
 ** and fast iteration. This is done by storing backing vectors of size greater than
 ** the maximum key.  This datastructure is appropriate for heavy use datastructures
 ** where the Keys are a dense set of integers.
 **
 ** T must support T(), and operator=().
 **
 ** The derived utility classes DenseSet and DenseMultiset are also defined.
 **/

#include "cvc4_private.h"

#pragma once

#include <limits>
#include <vector>

#include "base/check.h"
#include "util/index.h"


namespace CVC4 {

template <class T>
class DenseMap {
public:
  typedef Index Key;
  typedef std::vector<Key> KeyList;
  typedef KeyList::const_iterator const_iterator;

private:
  //List of the keys in the dense map.
  KeyList d_list;

  typedef Index Position;
  typedef std::vector<Position> PositionMap;
  static const Position POSITION_SENTINEL =
      std::numeric_limits<Position>::max();

  //Each Key in the set is mapped to its position in d_list.
  //Each Key not in the set is mapped to KEY_SENTINEL
  PositionMap d_posVector;

  typedef std::vector<T> ImageMap;
  //d_image : Key |-> T
  ImageMap d_image;

public:

  DenseMap() :  d_list(), d_posVector(), d_image() {}

  /** Returns the number of elements in the set. */
  size_t size() const {
    return d_list.size();
  }

  /** Returns true if the map is empty(). */
  bool empty() const {
    return d_list.empty();
  }

  /**
   * Similar to a std::vector::clear().
   *
   * Invalidates iterators.
   */
  void clear() {
    d_list.clear();
    d_posVector.clear();
    d_image.clear();
    Assert(empty());
  }

  /**
   * Similar to a clear(), but the datastructures are not reset in size.
   * Invalidates iterators.
   */
  void purge() {
    while(!empty()){
      pop_back();
    }
    Assert(empty());
  }

  /** Returns true if k is a key of this datastructure. */
  bool isKey(Key x) const{
    if( x >= allocated()){
      return false;
    }else{
      Assert(x < allocated());
      return d_posVector[x] != +POSITION_SENTINEL;
    }
  }

  /**
   * Maps the key to value in the map.
   * Invalidates iterators.
   */
  void set(Key key, const T& value){
    if( key >= allocated()){
      increaseSize(key);
    }

    if(!isKey(key)){
      d_posVector[key] = size();
      d_list.push_back(key);
    }
    d_image[key] = value;
  }

  /** Returns a mutable reference to the element mapped by key. */
  T& get(Key key){
    Assert(isKey(key));
    return d_image[key];
  }

  /** Returns a const reference to the element mapped by key.*/
  const T& operator[](Key key) const {
    Assert(isKey(key));
    return d_image[key];
  }

  /** Returns an iterator over the keys of the map. */
  const_iterator begin() const{ return d_list.begin(); }
  const_iterator end() const{ return d_list.end(); }

  const KeyList& getKeys() const{
    return d_list;
  }

  /**
   * Removes the mapping associated with key.
   * This changes the order of the keys.
   *
   * Invalidates iterators.
   */
  void remove(Key x){
    Assert(isKey(x));
    swapToBack(x);
    Assert(d_list.back() == x);
    pop_back();
  }

  /** Returns the key at the back of a non-empty list.*/
  Key back() const {
    return d_list.back();
  }

  /** Removes the element associated with the last Key from the map. */
  void pop_back() {
    Assert(!empty());
    Key atBack = back();
    d_posVector[atBack] = +POSITION_SENTINEL;
    d_image[atBack] = T();
    d_list.pop_back();
  }


  /** Adds at least a constant fraction of the elements in the current map to another map. */
  void splitInto(DenseMap<T>& target){
    uint32_t targetSize = size()/2;
    while(size() > targetSize){
      Key key = back();
      target.set(key, get(key));
      pop_back();
    }
  }

  /** Adds the current target map to the current map.*/
  void addAll(const DenseMap<T>& target){
    for(const_iterator i = target.begin(), e = target.end(); i != e; ++i){
      Key k = *i;
      set(k, target[k]);
    }
  }



 private:

  size_t allocated() const {
    Assert(d_posVector.size() == d_image.size());
    return d_posVector.size();
  }

  void increaseSize(Key max){
    Assert(max >= allocated());
    d_posVector.resize(max+1, +POSITION_SENTINEL);
    d_image.resize(max+1);
  }

  /** Swaps a member x to the back of d_list. */
  void swapToBack(Key x){
    Assert(isKey(x));

    Position currentPos = d_posVector[x];
    Key atBack = back();

    d_list[currentPos] = atBack;
    d_posVector[atBack] = currentPos;

    Position last = size() - 1;

    d_list[last] = x;
    d_posVector[x] = last;
  }
}; /* class DenseMap<T> */

/**
 * This provides an abstraction for a set of unsigned integers with similar capabilities
 * as DenseMap. This is implemented as a light wrapper for DenseMap<bool> with an
 * interface designed for use as a set instead of a map.
 */
class DenseSet {
private:
  typedef DenseMap<bool> BackingMap;
  BackingMap d_map;
public:
  typedef BackingMap::const_iterator const_iterator;
  typedef BackingMap::Key Element;

  size_t size() const { return d_map.size(); }
  bool empty() const { return d_map.empty(); }

  /** See DenseMap's documentation. */
  void purge() { d_map.purge(); }
  void clear() { d_map.clear(); }

  bool isMember(Element x) const{ return d_map.isKey(x); }

  /**
   * Adds an element that is not a member of the set to the set.
   */
  void add(Element x){
    Assert(!isMember(x));
    d_map.set(x, true);
  }

  /** Adds an element to the set even if it is already an element of the set. */
  void softAdd(Element x){ d_map.set(x, true); }

  /** Removes an element from the set. */
  void remove(Element x){ d_map.remove(x); }

  const_iterator begin() const{ return d_map.begin(); }
  const_iterator end() const{ return d_map.end(); }

  Element back() { return d_map.back(); }
  void pop_back() { d_map.pop_back(); }
}; /* class DenseSet */

/**
 * This provides an abstraction for a multiset of unsigned integers with similar
 * capabilities as DenseMap.
 * This is implemented as a light wrapper for DenseMap<bool> with an
 * interface designed for use as a set instead of a map.
 */
class DenseMultiset {
public:
  typedef uint32_t CountType;

private:
  typedef DenseMap<CountType> BackingMap;
  BackingMap d_map;

public:
  typedef BackingMap::const_iterator const_iterator;
  typedef BackingMap::Key Element;

  DenseMultiset() :  d_map() {}

  size_t size() const { return d_map.size(); }
  bool empty() const { return d_map.empty(); }

  void purge() { d_map.purge(); }
  void clear() { d_map.clear(); }

  bool isMember(Element x) const{ return d_map.isKey(x); }

  void add(Element x, CountType c = 1u){
    Assert(c > 0);
    if(d_map.isKey(x)){
      d_map.set(x, d_map.get(x)+c);
    }else{
      d_map.set(x,c);
    }
  }

  void setCount(Element x, CountType c){
    d_map.set(x, c);
  }

  void removeAll(Element x){ return d_map.remove(x); }

  void removeOne(Element x){
    CountType c = count(x);
    switch(c){
    case 0: break; // do nothing
    case 1: removeAll(x); break; // remove
    default: d_map.set(x, c-1); break; // decrease
    }
  }

  void removeOneOfEverything(){
    BackingMap::KeyList keys(d_map.begin(), d_map.end());
    for(BackingMap::const_iterator i=keys.begin(), i_end = keys.end(); i != i_end; ++i){
      removeOne(*i);
    }
  }

  CountType count(Element x) const {
    if(d_map.isKey(x)){
      return d_map[x];
    }else {
      return 0;
    }
  }

  const_iterator begin() const{ return d_map.begin(); }
  const_iterator end() const{ return d_map.end(); }
  Element back() { return d_map.back(); }
  void pop_back() { d_map.pop_back(); }
}; /* class DenseMultiset */

}/* CVC4 namespace */
