/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Context-dependent insert only hashmap built using trail of edits
 *
 * Context-dependent hashmap that only allows for one insertion per element.
 * This can be viewed as a highly restricted version of CDHashMap.
 * It is significantly lighter in memory usage than CDHashMap.
 *
 * See also:
 *  CDTrailHashMap : A lightweight CD hash map with poor iteration
 *    characteristics and some quirks in usage.
 *  CDHashMap : A fully featured CD hash map. (The closest to <ext/hash_map>)
 *
 * Notes:
 * - To iterate efficiently over the elements use the key_iterators.
 * - operator[] is only supported as a const derefence (must succeed).
 * - insert(k) must always work.
 * - Use insert_safe if you want to check if the element has been inserted
 *   and only insert if it has not yet been.
 * - Does not accept TNodes as keys.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__CONTEXT__CDINSERT_HASHMAP_H
#define CVC5__CONTEXT__CDINSERT_HASHMAP_H

#include <deque>
#include <functional>
#include <unordered_map>
#include <utility>

#include "base/check.h"
#include "base/output.h"
#include "context/cdinsert_hashmap_forward.h"
#include "context/context.h"

namespace cvc5 {

namespace internal {
template <bool ref_count>
class NodeTemplate;
}

namespace context {

template <class Key, class Data, class HashFcn = std::hash<Key> >
class InsertHashMap {
private:
  using KeyVec = std::deque<Key>;
  /** A list of the keys in the map maintained as a stack. */
  KeyVec d_keys;

  using HashMap = std::unordered_map<const Key, const Data, HashFcn>;
  /** The hash_map used for element lookup. */
  HashMap d_hashMap;

public:
  /**
   * An iterator over a list of keys.
   * Use this to efficiently iterate over the elements.
   * (See std::deque<>::iterator).
   */
  typedef typename KeyVec::const_iterator key_iterator;

  /**An iterator over the elements in the hash_map. */
  typedef typename HashMap::const_iterator const_iterator;

  // The type of the <Key, Data> values in the hashmap.
  using value_type = typename HashMap::value_type;

  /**
   * Returns an iterator to the begining of the HashMap.
   * Acts like a hash_map::const_iterator.
   */
  const_iterator begin() const{
    return d_hashMap.begin();
  }
  /**
   * Returns an iterator to the end of the HashMap.
   * Acts like a hash_map::const_iterator.
   */
  const_iterator end() const{
    return d_hashMap.end();
  }

  /**
   * Returns an iterator to the Key k of the map.
   * See hash_map::find()
   */
  const_iterator find(const Key& k) const{
    return d_hashMap.find(k);
  }

  /** Returns an iterator to the start of the set of keys. */
  key_iterator key_begin() const{
    return d_keys.begin();
  }
  /** Returns an iterator to the end of the set of keys. */
  key_iterator key_end() const{
    return d_keys.end();
  }

  /** Returns true if the map is empty. */
  bool empty() const { return d_keys.empty(); }
  /** Returns the number of elements in the map. */
  size_t size() const { return d_keys.size(); }

  /** Returns true if k is a mapped key. */
  bool contains(const Key& k) const {
    return find(k) != end();
  }

  /**
   * Returns a reference the data mapped by k.
   * This must succeed.
   */
  const Data& operator[](const Key& k) const {
    const_iterator ci = find(k);
    Assert(ci != end());
    return (*ci).second;
  }

  /**
   * Inserts an element into the map, and pushes its key to the front
   * of the stack. The key inserted must be not be currently mapped.
   */
  void push_front(const Key& k, const Data& d){
    Assert(!contains(k));
    d_hashMap.insert(std::make_pair(k, d));
    d_keys.push_front(k);
  }

  /**
   * Inserts an element into the map, and pushes its key onto the
   * back on the stack.  The key inserted must be not be currently mapped.
   */
  void push_back(const Key& k, const Data& d){
    Assert(!contains(k));
    d_hashMap.insert(std::make_pair(k, d));
    d_keys.push_back(k);
  }

  /**
   * Pops the key at the front of the list off and removes its key from the map.
   */
  void pop_front(){
    Assert(!empty());
    const Key& front = d_keys.front();
    d_hashMap.erase(front);

    Trace("TrailHashMap") <<"TrailHashMap pop_front " << size() << std::endl;
    d_keys.pop_front();
  }

  /**
   * Pops the key at the back of the stack off and removes its key from the map.
   */
  void pop_back(){
    Assert(!empty());
    const Key& back = d_keys.back();
    d_hashMap.erase(back);

    Trace("TrailHashMap") <<"TrailHashMap pop_back " << size() << std::endl;
    d_keys.pop_back();
  }

  /**
   * Pops the back of the stack until the size is below s.
   */
  void pop_to_size(size_t s){
    while(size() > s){
      pop_back();
    }
  }
};/* class TrailHashMap<> */

template <class Key, class Data, class HashFcn>
class CDInsertHashMap : public ContextObj {
private:
  typedef InsertHashMap<Key, Data, HashFcn> IHM;

  /** An InsertHashMap that backs all of the data. */
  IHM* d_insertMap;

  /** For restores, we need to keep track of the previous size. */
  size_t d_size;

  /**
   * Private copy constructor used only by save().  d_insertMap is
   * not copied: only the base class information and
   * d_size are needed in restore.
   */
  CDInsertHashMap(const CDInsertHashMap& l)
      : ContextObj(l), d_insertMap(nullptr), d_size(l.d_size)
  {
    Trace("CDInsertHashMap") << "copy ctor: " << this
                    << " from " << &l
                    << " size " << d_size << std::endl;
  }
  CDInsertHashMap& operator=(const CDInsertHashMap&) = delete;

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current size information to a copy using the copy constructor (the
   * pointer and the allocated size are *not* copied as they are not
   * restored on a pop).  The saved information is allocated using the
   * ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    ContextObj* data = new(pCMM) CDInsertHashMap<Key, Data, HashFcn>(*this);
    return data;
  }
protected:
 /**
  * Implementation of mandatory ContextObj method restore:
  * restore to the previous size taking into account the number
  * of new pushFront calls have happened since saving.
  * The d_insertMap is untouched.
  */
 void restore(ContextObj* data) override
 {
   size_t oldSize = ((CDInsertHashMap<Key, Data, HashFcn>*)data)->d_size;

   // The size to restore to.
   size_t restoreSize = oldSize;
   d_insertMap->pop_to_size(restoreSize);
   d_size = restoreSize;
   Assert(d_insertMap->size() == d_size);
  }
public:

 /**
   * Main constructor: d_insertMap starts as an empty map, with the size is 0
   */
 CDInsertHashMap(Context* context)
     : ContextObj(context), d_insertMap(new IHM()), d_size(0)
 {
   Assert(d_insertMap->size() == d_size);
 }

  /**
   * Destructor: delete the d_insertMap
   */
  ~CDInsertHashMap() {
    this->destroy();
    delete d_insertMap;
  }

  /** An iterator over the elements in the hash_map. */
  typedef typename IHM::const_iterator const_iterator;

  /**
   * An iterator over a list of keys.
   * Use this to efficiently iterate over the elements.
   * (See std::deque<>::iterator).
   */
  typedef typename IHM::key_iterator key_iterator;

  // The type of the <key, data> values in the hashmap.
  using value_type = typename IHM::value_type;

  /** Returns true if the map is empty in the current context. */
  bool empty() const{
    return d_size == 0;
  }

  /** Returns true the size of the map in the current context. */
  size_t size() const {
    return d_size;
  }

  /**
   * Inserts an element into the map.
   * The key inserted must be not be currently mapped.
   * This is implemented using d_insertMap.push_back().
   */
  void insert(const Key& k, const Data& d){
    makeCurrent();
    ++d_size;
    d_insertMap->push_back(k, d);
    Assert(d_insertMap->size() == d_size);
  }

  /**
   * Checks if the key k is mapped already.
   * If it is, this returns false.
   * Otherwise it is inserted and this returns true.
   */
  bool insert_safe(const Key& k, const Data& d){
    if(contains(k)){
      return false;
    }else{
      insert(k,d);
      return true;
    }
  }

  /** Returns true if k is a mapped key in the context. */
  bool contains(const Key& k) const {
    return d_insertMap->contains(k);
  }

  /**
   * Returns a reference the data mapped by k.
   * k must be in the map in this context.
   */
  const Data& operator[](const Key& k) const {
    return (*d_insertMap)[k];
  }

   /**
    * Returns a const_iterator to the value_type if k is a mapped key in
    * the context.
    */
  const_iterator find(const Key& k) const {
    return d_insertMap->find(k);
  }

  /**
   * Returns an iterator to the begining of the map.
   * Acts like a hash_map::const_iterator.
   */
  const_iterator begin() const{
    return d_insertMap->begin();
  }

  /**
   * Returns an iterator to the end of the map.
   * Acts like a hash_map::const_iterator.
   */
  const_iterator end() const{
    return d_insertMap->end();
  }

  /** Returns an iterator to the start of the set of keys. */
  key_iterator key_begin() const{
    return d_insertMap->key_begin();
  }
  /** Returns an iterator to the end of the set of keys. */
  key_iterator key_end() const{
    return d_insertMap->key_end();
  }
};/* class CDInsertHashMap<> */

template <class Data, class HashFcn>
class CDInsertHashMap<internal::NodeTemplate<false>, Data, HashFcn>
    : public ContextObj
{
  /* CDInsertHashMap is challenging to get working with TNode.
   * Consider using CDHashMap<TNode,...> instead.
   *
   * Explanation:
   * CDInsertHashMap uses keys for deallocation.
   * If the key is a TNode and the backing (the hard node reference)
   * for the key in another data structure removes the key at the same context
   * the ref count could drop to 0.  The key would then not be eligible to be
   * hashed. Getting the order right with a guarantee is too hard.
   */

  static_assert(sizeof(Data) == 0,
                "Cannot create a CDInsertHashMap with TNode keys");
};

}  // namespace context
}  // namespace cvc5

#endif
