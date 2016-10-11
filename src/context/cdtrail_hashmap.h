/*********************                                                        */
/*! \file cdtrail_hashmap.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent hashmap built using trail of elements
 **
 ** Context-dependent hashmap that explicitly keeps track of its edit history.
 ** This is similar in functionality to CDHashMap with fewer capabilites and
 ** slight changes in the interface. It has the advantage of being lighter in
 ** memory usage.
 **
 ** See also:
 **  CDInsertHashMap : An "insert-once" CD hash map.
 **  CDHashMap : A fully featured CD hash map. (The closest to <ext/hash_map>)
 **
 ** Notes:
 ** - To iterate efficiently over the elements use the key_iterators.
 ** - operator[] is only supported as a const derefence (must succeed).
 ** - Insertions to the map are done with respect to a context.
 ** - Insertions can be done in two manors either with insert() or
 **   insert_no_overwrite().
 ** - insert(k,d) inserts the key data pair into the hashtable and returns a
 **   false if it overwrote the previous value.
 ** - insert_no_overwrite(k,d) inserts key data pair into the hashtable only
 **   if the value is not already there. It returns true, if an element was
 **   added. This conditionally extends the trail length if it returns true.
 ** - inserts are compacting.  If there is another insert to the same key
 **   at the same context, the memory is reused.
 ** - Iterating over const_iterators has amortized time proportional to
 **   O(trail length). (If this needs to be improved, please bug Tim.)
 ** - contains() and operator[] are slightly faster than using stl style
 **   iterator comparisons: find(), end(), etc.
 **/


#include "cvc4_private.h"

#pragma once

#include <boost/static_assert.hpp>
#include <ext/hash_map>
#include <deque>
#include <utility>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "context/context.h"
#include "context/cdtrail_hashmap_forward.h"
#include "expr/node.h"

namespace CVC4 {
namespace context {


template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class TrailHashMap {
public:
  /** A pair of Key and Data that mirrors hash_map::value_type. */
  typedef std::pair<Key, Data> value_type;

private:

  /** The trail information from an insert. */
  struct KDT {
    /** The Key Data pair. */
    value_type d_kd;

    /**
     * The previous trail entry with the same key.
     * On a pop, this is the element to revert to.
     * This value is a self loop if there is no previous entry.
     */
    size_t d_prevKey;

    /**  The whether the trail element is current. */
    bool d_current;

    KDT(const Key& key, const Data& data, size_t prev, bool cur = true):
      d_kd(std::make_pair(key, data)), d_prevKey(prev), d_current(cur){ }
    KDT(){}
  };

  typedef std::deque<KDT> KDTVec;
  typedef typename KDTVec::const_iterator KDTVec_const_iterator;
  /** The trail of elements. */
  KDTVec d_kdts;


  typedef __gnu_cxx::hash_map<Key, size_t, HashFcn> PositionMap;
  typedef typename PositionMap::iterator PM_iterator;
  typedef typename PositionMap::const_iterator PM_const_iterator;

  /** A map of keys to their positions in the trail. */
  PositionMap d_posMap;


  /** The number of unique keys in the map. */
  size_t d_uniqueKeys;

  /** Internal utility class. NonConstant find on the position map.*/
  inline PM_iterator ncfind(const Key& k) {
    return d_posMap.find(k);
  }

  /** Internal utility class. Position Map Find.*/
  inline PM_const_iterator pmfind(const Key& k) const{
    return d_posMap.find(k);
  }
  /** Internal utility class. Position Map End.*/
  inline PM_const_iterator pmend() const{
    return d_posMap.end();
  }

  /** This is true if the previous entry in the trail points at itself.*/
  inline bool selfLoop(size_t pos, const KDT& kdt) const {
    return pos == kdt.d_prevKey;
  }

public:
  /**
   * Constant iterator for TrailHashMap.
   * Only supports forward iteration.
   * This always points at the end or a current element in the trail.
   * This is done by iterating over the trail.
   */
  class const_iterator {
  private:
    /** A vector iterator. */
    KDTVec_const_iterator d_it;

    /** A pointer to the end of the vector.*/
    KDTVec_const_iterator d_end;

    /** Move the iterator to the end or the next current element.*/
    void findCurrent(){
      while(d_it != d_end && !(*d_it).d_current){
        ++d_it;
      }
    }

  public:

    /** Constructs an iterator for a TrailHashMap. */
    const_iterator(KDTVec_const_iterator it, KDTVec_const_iterator end) :
      d_it(it),
      d_end(end){
      findCurrent();
    }

    /** Copy constructor for an iterator for a TrailHashMap. */
    const_iterator(const const_iterator& other) :
      d_it(other.d_it), d_end(other.d_end){
      // Do not need to findCurrent()
    }

    /** Returns true if the iterators are the same. */
    inline bool operator==(const const_iterator& other) const {
      return d_it == other.d_it;
    }

    /** Returns true if the iterators are the same. */
    inline bool operator!=(const const_iterator& other) const {
      return d_it != other.d_it;
    }

    /** Returns a pair<Key,Data>. */
    inline const value_type& operator*() const {
      return (*d_it).d_kd;
    }

    /** Prefix increment */
    const_iterator& operator++() {
      ++d_it;
      findCurrent();
      return *this;
    }
  };

  /** Returns a beginning iterator.*/
  inline const_iterator begin() const{
    return const_iterator(d_kdts.begin(), d_kdts.end());
  }

  /** Returns an end iterator.*/
  inline const_iterator end() const{
    return const_iterator(d_kdts.end(), d_kdts.end());
  }

  /** Returns true if the trail is empty.*/
  inline bool empty() const { return d_kdts.empty(); }

  /** Returns the size of the trail.*/
  inline size_t trailSize() const { return d_kdts.size(); }

  /** Returns the number of unique keys in the map.*/
  inline size_t uniqueKeys() const { return d_uniqueKeys; }

  /** Returns true if the key is in the map.*/
  inline bool contains(const Key& k) const {
    return pmfind(k) != pmend();
  }

  /**
   * Returns a NON const reference to an element in the Map.
   * k must be a key in the Map.
   * DO NOT USE THIS UNLESS YOU ARE CONFIDENT THE CHANGES MAKE SENSE.
   */
  Data& lookup(const Key& k){
    Assert(contains(k));
    PM_iterator ci = ncfind(k);
    KDT& kdt = d_kdts[(*ci).second];
    return kdt.d_kd.second;
  }

  /**
   * Returns a const reference to an element mapped by a Key k.
   * k must be a key in the Map.
   */
  const Data& operator[](const Key& k) const {
    PM_const_iterator pci = pmfind(k);
    Assert(pci != pmend());
    return d_kdts[(*pci).second].d_kd.second;
  }

  /**
   * If the key k is in the map, this returns a const_iterator pointing at this
   * element.  Otherwise, this returns end().
   */
  const_iterator find(const Key& k) const {
    PM_const_iterator pci = pmfind(k);
    if(pci == pmend()){
      return end();
    }else{
      size_t pos = (*pci).second;
      return const_iterator(d_kdts.begin() + pos, d_kdts.end());
    }
  }

  /**
   * Similar to contains, but includes a notion of trail position.
   * Returns <true, true> if contains(k) and the current position of k
   *  in the map is greater than or equal to pos.
   * Returns <true, false> if it contains(k) but not the previous condition.
   * Returns <false, false> if it does not contains(k).
   */
  std::pair<bool, bool> hasAfter(const Key& k, size_t pos) {
    PM_iterator it = ncfind(k);
    if(it != d_posMap.end()){
      return std::make_pair(true, (*it).second >= pos );
    }
    return std::make_pair(false, false);
  }

  /**
   * Inserts an element unconditionally.
   * Always increases the trail size.
   * Returns true if the key count increased.
   */
  bool push_back(const Key& k, const Data& d){
    std::pair<bool, bool> res = compacting_push_back(k, d, trailSize());
    return res.first;
  }

  /**
   * This inserts an element into the trail.
   * This insert can reuse the same trail element if the postion of the element
   * is >= threshold.
   *
   * Return values:
   * If pair<bool, bool> res = compacting_push_back(..),
   * then res.first is true if this is a new unique key, and
   * res.second is true if the trail length increased.
   * 
   */
  std::pair<bool, bool> compacting_push_back(const Key& k, const Data& d, size_t threshold){
    size_t backPos = d_kdts.size();
    std::pair<PM_iterator, bool> res = d_posMap.insert(std::make_pair(k, backPos));
    if(!res.second){
      size_t& prevPosInPM = (*res.first).second;

      Assert(d_kdts[prevPosInPM].d_current);

      if(prevPosInPM < threshold){
        d_kdts.push_back(KDT(k,d, prevPosInPM));
        d_kdts[prevPosInPM].d_current = false;
        prevPosInPM = backPos;

        return std::make_pair(false, true);
      }else{
        d_kdts[prevPosInPM].d_kd.second = d;
        return std::make_pair(false, false);
      }
    }else{
      d_kdts.push_back(KDT(k,d, backPos));
      ++d_uniqueKeys;
      return std::make_pair(true, true);
    }
  }

  /**
   * Inserts an element if the key is not already in the map.
   * Returns true if the element was inserted.
   */
  bool insert_no_overwrite(const Key& k, const Data& d){
    size_t backPos = d_kdts.size();
    std::pair<PM_iterator, bool> res = d_posMap.insert(std::make_pair(k, backPos));
    if(res.second){
      d_kdts.push_back(KDT(k,d, backPos));
      ++d_uniqueKeys;
    }
    Debug("TrailHashMap") <<"TrailHashMap insert" << k << " d " << d << " " << backPos << std::endl;
    return res.second;
  }

  /** Pops the element at the back of the trail. */
  void pop_back(){
    Assert(!empty());
    const KDT& back = d_kdts.back();
    const Key& k = back.d_kd.first;
    if(selfLoop(trailSize()-1, back)){
      d_posMap.erase(k);
      --d_uniqueKeys;
      Debug("TrailHashMap") <<"TrailHashMap pop_back erase " << trailSize() <<" " << std::endl;

    }else{
      Debug("TrailHashMap") <<"TrailHashMap reset " << trailSize() <<" " << " " << back.d_prevKey << std::endl;
      d_posMap[k] = back.d_prevKey;
      d_kdts[back.d_prevKey].d_current = true;
    }
    d_kdts.pop_back();
  }

  /** Pops the element at the back of the trail until the trailSize is <= s. */
  void pop_to_size(size_t s){
    while(trailSize() > s){
      pop_back();
    }
  }
};/* class TrailHashMap<> */

template <class Key, class Data, class HashFcn >
class CDTrailHashMap : public ContextObj {
private:
  /** A short name for the templatized TrailMap that backs the CDTrailMap. */
  typedef TrailHashMap<Key, Data, HashFcn> THM;

  /** The trail map that backs the CDTrailMap. */
  THM* d_trailMap;
public:
  /** Iterator for the CDTrailHashMap. */
  typedef typename THM::const_iterator const_iterator;

  /** Return value of operator* on a const_iterator (pair<Key,Data>).*/
  typedef typename THM::value_type value_type;

private:
  /**
   * The length of the trail in the current context.
   * This is used to support reverting.
   */
  size_t d_trailSize;

  /**
   * The length of the trail immediately after the previous makeCurrent().
   * This is used to support compacting inserts.
   */
  size_t d_prevTrailSize;

  /**
   * Private copy constructor used only by save().  d_trailMap is not copied:
   * only the base class information, d_trailSize, and d_prevTrailSize
   * are needed in restore.
   */
  CDTrailHashMap(const CDTrailHashMap<Key, Data, HashFcn>& l) :
    ContextObj(l),
    d_trailMap(NULL),
    d_trailSize(l.d_trailSize),
    d_prevTrailSize(l.d_prevTrailSize){
    Debug("CDTrailHashMap") << "copy ctor: " << this
                    << " from " << &l
                    << " size " << d_trailSize << std::endl;
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current sizes to a copy using the copy constructor,
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDTrailHashMap<Key, Data, HashFcn>(*this);
    Debug("CDTrailHashMap") << "save " << this
                            << " at level " << this->getContext()->getLevel()
                            << " size at " << this->d_trailSize
                            << " d_list is " << this->d_trailMap
                            << " data:" << data << std::endl;
    return data;
  }
protected:
  /**
   * Implementation of mandatory ContextObj method restore: simply
   * restores the previous size.  Note that the list pointer and the
   * allocated size are not changed.
   */
  void restore(ContextObj* data) {
    Debug("CDTrailHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " data == " << data
                            << " d_trailMap == " << this->d_trailMap << std::endl;
    size_t oldSize = ((CDTrailHashMap<Key, Data, HashFcn>*)data)->d_trailSize;
    d_trailMap->pop_to_size(oldSize);
    d_trailSize = oldSize;
    Assert(d_trailMap->trailSize() == d_trailSize);

    d_prevTrailSize = ((CDTrailHashMap<Key, Data, HashFcn>*)data)->d_prevTrailSize;
    Debug("CDTrailHashMap") << "restore " << this
                            << " level " << this->getContext()->getLevel()
                            << " size back to " << this->d_trailSize << std::endl;
  }

  /**
   * We need to save the d_trailSize immediately after a successful makeCurrent.
   * So this version needs to be used everywhere instead of maekCurrent()
   * internally.
   */
  void internalMakeCurrent () {
    if(!isCurrent()){
      makeCurrent();
      d_prevTrailSize = d_trailSize;
    }
  }

public:

  /**
   * Main constructor: d_trailMap starts as an empty map, with the sizes are 0
   */
  CDTrailHashMap(Context* context) :
    ContextObj(context),
    d_trailMap(new THM()),
    d_trailSize(0),
    d_prevTrailSize(0){
    Assert(d_trailMap->trailSize() == d_trailSize);
  }

  /**
   * Destructor: delete the map
   */
  ~CDTrailHashMap() {
    this->destroy();
    delete d_trailMap;
  }

  /** Returns true if the map is empty in the current context. */
  bool empty() const{
    return d_trailSize == 0;
  }

  /** Returns true the size of the map in the current context. */
  size_t size() const {
    return d_trailMap->uniqueKeys();
  }

  /**
   * Inserts an element into the map.
   * This always succeeds.
   * Returns true if the key is new.
   */
  bool insert(const Key& k, const Data& d){
    internalMakeCurrent();
    std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, d, d_prevTrailSize);
    if(res.second){
      ++d_trailSize;
    }
    Assert(d_trailMap->trailSize() == d_trailSize);
    return res.first;
  }

  /**
   * Inserts an element into the map if the key is not already there.
   * This has no side effects if the insert does not happen.
   * Returns true if the element was inserted.
   */
  bool insert_no_overwrite(const Key& k, const Data& d){
    bool res = d_trailMap->insert_no_overwrite(k, d);
    if(res){
      internalMakeCurrent();
      ++d_trailSize;
    }
    Assert(d_trailMap->trailSize() == d_trailSize);
    return res;
  }

  /** Returns true if k is a mapped key in the context. */
  bool contains(const Key& k) const {
    return d_trailMap->contains(k);
  }

  /**
   * Returns a reference the data mapped by k.
   * k must be in the map in this context.
   */
  const Data& operator[](const Key& k) const {
    return (*d_trailMap)[k];
  }
 /*
// While the following code "works", I wonder if it is not better to disable it?
// Non-const operator[] has strange semantics for a context-dependent
// data structure.
  Data& operator[](const Key& k) {
    internalMakeCurrent();
    std::pair<bool, bool> res = d_trailMap->hasAfter(k, d_prevTrailSize);
    if(!res.first){
      std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, Data(), d_prevTrailSize);
      if(res.second){
        ++d_trailSize;
      }
    }else if(!res.second){
      std::pair<bool, bool> res = d_trailMap->compacting_push_back(k, (*d_trailMap)[k], d_prevTrailSize);
      if(res.second){
        ++d_trailSize;
      }
    }
    return d_trailMap->lookup(k);
  }
 */

  /**
   * Returns a const_iterator to the value_type if k is a mapped key in
   * the context.
   */
  const_iterator find(const Key& k) const {
    return d_trailMap->find(k);
  }

  /** Returns an iterator to the beginning of the map.  */
  const_iterator begin() const{
    return d_trailMap->begin();
  }
  /** Returns an iterator to the end of the map.  */
  const_iterator end() const{
    return d_trailMap->end();
  }

};/* class CDTrailHashMap<> */

template <class Data, class HashFcn>
class CDTrailHashMap <TNode, Data, HashFcn > : public ContextObj {
  /* CDTrailHashMap is challenging to get working with TNode.
   * Consider using CDHashMap<TNode,...> instead.
   *
   * Explanation:
   * CDTrailHashMap uses keys during deallocation.
   * If the key is a TNode and the backing (the hard node reference)
   * for the key in another data structure removes the key at the same context
   * the ref count could drop to 0.  The key would then not be eligible to be
   * hashed. Getting the order right with a guarantee is too hard.
   */

  BOOST_STATIC_ASSERT(sizeof(Data) == 0);
};

}/* CVC4::context namespace */
}/* CVC4 namespace */
