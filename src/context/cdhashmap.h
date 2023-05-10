/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Mikolas Janota, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Context-dependent map class.
 *
 * Generic templated class for a map which must be saved and restored as
 * contexts are pushed and popped.  Requires that operator= be defined for the
 * data class, and operator== for the key class.  For key types that don't have
 * a std::hash<>, you should provide an explicit HashFcn.
 *
 * See also:
 *  CDInsertHashMap : An "insert-once" CD hash map.
 *  CDTrailHashMap : A lightweight CD hash map with poor iteration
 *    characteristics and some quirks in usage.
 *
 * Internal documentation:
 *
 * CDHashMap<> is something of a work in progress at present (26 May
 * 2010), due to some recent discoveries of problems with its
 * internal state.  Here are some notes on the internal use of
 * CDOhash_maps that may be useful in figuring out this mess:
 *
 *     So you have a CDHashMap<>.
 *
 *     You insert some (key,value) pairs.  Each allocates a CDOhash_map<>
 *     and goes on a doubly-linked list headed by map.d_first and
 *     threaded via CDOhash_map.{d_prev,d_next}.  CDOhash_maps are constructed
 *     with a NULL d_map pointer, but then immediately call
 *     makeCurrent() and set the d_map pointer back to the map.  At
 *     context level 0, this doesn't lead to anything special.  In
 *     higher context levels, this stores away a CDOhash_map with a NULL
 *     map pointer at level 0, and a non-NULL map pointer in the
 *     current context level.  (Remember that for later.)
 *
 *     When a key is associated to a new value in a CDHashMap, its
 *     associated CDOhash_map calls makeCurrent(), then sets the new
 *     value.  The save object is also a CDOhash_map (allocated in context
 *     memory).
 *
 *     Now, CDOhash_maps disappear in a variety of ways.
 *
 *     First, you might pop beyond a "modification of the value"
 *     scope level, requiring a re-association of the key to an old
 *     value.  This is easy.  CDOhash_map::restore() does the work, and
 *     the context memory of the save object is reclaimed as usual.
 *
 *     Second, you might pop beyond a "insert the key" scope level,
 *     requiring that the key be completely removed from the map and
 *     its CDOhash_map object memory freed.  Here, the CDOhash_map is restored
 *     to a "NULL-map" state (see above), signaling it to remove
 *     itself from the map completely and put itself on a "trash
 *     list" for its scope.
 *
 *     Third, you might delete the cdhashmap(calling CDHashMap::~CDHashMap()).
 *     This first calls destroy(), as per ContextObj contract, but
 *     cdhashmapdoesn't save/restore itself, so that does nothing at the
 *     CDHashMap-level. Then, for each element in the map, it marks it as being
 *     "part of a complete map destruction", which essentially short-circuits
 *     CDOhash_map::restore() (see CDOhash_map::restore()), then deallocates
 *     it.
 *
 *     Fourth, you might clear() the CDHashMap.  This does exactly the
 *     same as CDHashMap::~CDHashMap(), except that it doesn't call destroy()
 *     on itself.
 *
 *     ContextObj::deleteSelf() calls the CDOhash_map destructor, then
 *     frees the memory associated to the CDOhash_map.
 *     CDOhash_map::~CDOhash_map() calls destroy(), which restores as much as
 *     possible.
 */

#include "cvc5parser_public.h"

#ifndef CVC5__CONTEXT__CDHASHMAP_H
#define CVC5__CONTEXT__CDHASHMAP_H

#include <functional>
#include <iterator>
#include <unordered_map>

#include "base/check.h"
#include "context/cdhashmap_forward.h"
#include "context/context.h"

namespace cvc5::context {

// Auxiliary class: almost the same as CDO (see cdo.h)

template <class Key, class Data, class HashFcn = std::hash<Key> >
class CDOhash_map : public ContextObj
{
  friend class CDHashMap<Key, Data, HashFcn>;

 public:
  // The type of the <Key, Data> pair mapped by this class.
  //
  // Implementation:
  // The data and key visible to users of CDHashMap are only visible through
  // const references. Thus the type of dereferencing a
  // CDHashMap<Key, Data>::iterator.second is intended to always be a
  // `const Data&`. (Otherwise, to get a Data& safely, access operations
  // would need to makeCurrent() to get the Data&, which is an unacceptable
  // performance hit.) To allow for the desired updating in other scenarios, we
  // store a std::pair<const Key, const Data> and break the const encapsulation
  // when necessary.
  using value_type = std::pair<const Key, const Data>;

 private:
  value_type d_value;

  // See documentation of value_type for why this is needed.
  Key& mutable_key() { return const_cast<Key&>(d_value.first); }
  // See documentation of value_type for why this is needed.
  Data& mutable_data() { return const_cast<Data&>(d_value.second); }

  CDHashMap<Key, Data, HashFcn>* d_map;

  // Doubly-linked list for keeping track of elements in order of insertion
  CDOhash_map* d_prev;
  CDOhash_map* d_next;

  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    return new (pCMM) CDOhash_map(*this);
  }

  void restore(ContextObj* data) override
  {
    CDOhash_map* p = static_cast<CDOhash_map*>(data);
    if (d_map != NULL)
    {
      if (p->d_map == NULL)
      {
        Assert(d_map->d_map.find(getKey()) != d_map->d_map.end()
               && (*d_map->d_map.find(getKey())).second == this);
        // no longer in map (popped beyond first level in which it was)
        d_map->d_map.erase(getKey());
        // If we call deleteSelf() here, it re-enters restore().  So,
        // put it on a "trash heap" instead, for later deletion.
        //
        // FIXME multithreading
        if (d_map->d_first == this)
        {
          if (d_next == this)
          {
            Assert(d_prev == this);
            d_map->d_first = NULL;
          }
          else
          {
            d_map->d_first = d_next;
          }
        }
        d_next->d_prev = d_prev;
        d_prev->d_next = d_next;

        // this->deleteSelf();
        enqueueToGarbageCollect();
      }
      else
      {
        mutable_data() = p->get();
      }
    }
    // Explicitly call destructors for the key and the data as they will not
    // otherwise get called.
    p->mutable_key().~Key();
    p->mutable_data().~Data();
  }

  /** ensure copy ctor is only called by us */
  CDOhash_map(const CDOhash_map& other)
      : ContextObj(other),
        // don't need to save the key---and if we do we can get
        // refcounts for Node keys messed up and leak memory
        d_value(Key(), other.d_value.second),
        d_map(other.d_map),
        d_prev(NULL),
        d_next(NULL)
  {
  }
  CDOhash_map& operator=(const CDOhash_map&) = delete;

 public:
  CDOhash_map(Context* context,
              CDHashMap<Key, Data, HashFcn>* map,
              const Key& key,
              const Data& data)
      : ContextObj(context), d_value(key, data), d_map(NULL)
  {
    // Normal map insertion: first makeCurrent(), then set the data
    // and then, later, the map.  Order is important; we can't
    // initialize d_map in the constructor init list above, because
    // we want the restore of d_map to NULL to signal us to remove
    // the element from the map.

    set(data);
    d_map = map;

    CDOhash_map*& first = d_map->d_first;
    if (first == NULL)
    {
      first = d_next = d_prev = this;
    }
    else
    {
      d_prev = first->d_prev;
      d_next = first;
      d_prev->d_next = this;
      first->d_prev = this;
    }
  }

  ~CDOhash_map() { destroy(); }

  void set(const Data& data)
  {
    makeCurrent();
    mutable_data() = data;
  }

  const Key& getKey() const { return d_value.first; }

  const Data& get() const { return d_value.second; }

  const value_type& getValue() const { return d_value; }

  operator Data() { return get(); }

  const Data& operator=(const Data& data)
  {
    set(data);
    return data;
  }

  CDOhash_map* next() const
  {
    if (d_next == d_map->d_first)
    {
      return NULL;
    }
    else
    {
      return d_next;
    }
  }
}; /* class CDOhash_map<> */

/**
 * Generic templated class for a map which must be saved and restored
 * as contexts are pushed and popped.  Requires that operator= be
 * defined for the data class, and operator== for the key class.
 */
template <class Key, class Data, class HashFcn>
class CDHashMap : public ContextObj
{
  typedef CDOhash_map<Key, Data, HashFcn> Element;
  typedef std::unordered_map<Key, Element*, HashFcn> table_type;

  friend class CDOhash_map<Key, Data, HashFcn>;

  table_type d_map;

  Element* d_first;
  Context* d_context;

  // Nothing to save; the elements take care of themselves
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    Unreachable();
    SuppressWrongNoReturnWarning;
  }

  // Similarly, nothing to restore
  void restore(ContextObj* data) override { Unreachable(); }

  // no copy or assignment
  CDHashMap(const CDHashMap&) = delete;
  CDHashMap& operator=(const CDHashMap&) = delete;

 public:
  CDHashMap(Context* context)
      : ContextObj(context), d_map(), d_first(NULL), d_context(context)
  {
  }

  ~CDHashMap()
  {
    destroy();
    clear();
  }

  void clear()
  {
    for (auto& key_element_pair : d_map)
    {
      // mark it as being a destruction (short-circuit restore())
      Element* element = key_element_pair.second;
      element->d_map = nullptr;
      element->deleteSelf();
    }
    d_map.clear();
    d_first = nullptr;
  }

  // The usual operators of map

  size_t size() const { return d_map.size(); }

  bool empty() const { return d_map.empty(); }

  size_t count(const Key& k) const { return d_map.count(k); }

  // If a key is not present, a new object is created and inserted
  Element& operator[](const Key& k)
  {
    const auto res = d_map.insert({k, nullptr});
    if (res.second)
    {  // create new object
      res.first->second = new (true) Element(d_context, this, k, Data());
    }
    return *(res.first->second);
  }

  bool insert(const Key& k, const Data& d)
  {
    const auto res = d_map.insert({k, nullptr});
    if (res.second)
    {  // create new object
      res.first->second = new (true) Element(d_context, this, k, d);
    }
    else
    {
      res.first->second->set(d);
    }
    return res.second;
  }

  // FIXME: no erase(), too much hassle to implement efficiently...

  using value_type = typename CDOhash_map<Key, Data, HashFcn>::value_type;

  class iterator
  {
    const Element* d_it;

   public:
    using iterator_category = std::forward_iterator_tag;
    using value_type = typename CDOhash_map<Key, Data, HashFcn>::value_type;
    using difference_type = ptrdiff_t;
    using pointer = typename CDOhash_map<Key, Data, HashFcn>::value_type*;
    using reference = typename CDOhash_map<Key, Data, HashFcn>::value_type&;

    iterator(const Element* p) : d_it(p) {}
    iterator(const iterator& i) : d_it(i.d_it) {}

    // Default constructor
    iterator() : d_it(nullptr) {}

    // (Dis)equality
    bool operator==(const iterator& i) const { return d_it == i.d_it; }
    bool operator!=(const iterator& i) const { return d_it != i.d_it; }

    // Dereference operators.
    const value_type& operator*() const { return d_it->getValue(); }
    const value_type* operator->() const { return &d_it->getValue(); }

    // Prefix increment
    iterator& operator++()
    {
      d_it = d_it->next();
      return *this;
    }

    // Postfix increment is not yet supported.
  }; /* class CDHashMap<>::iterator */

  typedef iterator const_iterator;

  iterator begin() const { return iterator(d_first); }

  iterator end() const { return iterator(NULL); }

  iterator find(const Key& k) const
  {
    typename table_type::const_iterator i = d_map.find(k);

    if (i == d_map.end())
    {
      return end();
    }
    else
    {
      return iterator((*i).second);
    }
  }

}; /* class CDHashMap<> */

}  // namespace cvc5::context

#endif /* CVC5__CONTEXT__CDHASHMAP_H */
