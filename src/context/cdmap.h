/*********************                                                        */
/** cdmap.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Context-dependent map class.  Generic templated class for a map
 ** which must be saved and restored as contexts are pushed and
 ** popped.  Requires that operator= be defined for the data class,
 ** and operator== for the key class.  For key types that don't have a
 ** __gnu_cxx::hash<>, you should provide an explicit HashFcn.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDMAP_H
#define __CVC4__CONTEXT__CDMAP_H

#include "context/context.h"
#include "util/Assert.h"

#include <iterator>
#include <ext/hash_map>

namespace CVC4 {
namespace context {

// Auxiliary class: almost the same as CDO (see cdo.h), but on
// setNull() call it erases itself from the map.

template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> > class CDMap;

template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class CDOmap : public ContextObj {
  Key d_key;
  Data d_data;
  bool d_inMap; // whether the data must be in the map
  CDMap<Key, Data, HashFcn>* d_cdmap;

  // Doubly-linked list for keeping track of elements in order of insertion
  CDOmap<Key, Data, HashFcn>* d_prev;
  CDOmap<Key, Data, HashFcn>* d_next;

  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDOmap<Key, Data, HashFcn>(*this);
  }

  virtual void restore(ContextObj* data) {
    CDOmap<Key, Data, HashFcn>* p((CDOmap<Key, Data, HashFcn>*) data);
    if(p->d_inMap) {
      d_data = p->d_data;
      d_inMap = true;
    } else {
      // Erase itself from the map and put itself into trash.  We cannot
      // "delete this" here, because it will break context operations in
      // a non-trivial way.
      if(d_cdmap->d_map.count(d_key) > 0) {
        d_cdmap->d_map.erase(d_key);
        d_cdmap->d_trash.push_back(this);
      }

      d_prev->d_next = d_next;
      d_next->d_prev = d_prev;

      if(d_cdmap->d_first == this) {
        d_cdmap->d_first = d_next;

        if(d_next == this) {
          d_cdmap->d_first = NULL;
        }
      }
    }
  }

public:

  CDOmap(Context* context,
         CDMap<Key, Data, HashFcn>* cdmap,
	 const Key& key,
         const Data& data) :
    ContextObj(context),
    d_key(key),
    d_inMap(false),
    d_cdmap(cdmap) {

    set(data);

    CDOmap<Key, Data, HashFcn>*& first = d_cdmap->d_first;
    if(first == NULL) {
      first = d_next = d_prev = this;
    } else {
      d_prev = first->d_prev;
      d_next = first;
      d_prev->d_next = first->d_prev = this;
    }
  }

  ~CDOmap() throw(AssertionException) { destroy(); }

  void set(const Data& data) {
    makeCurrent();
    d_data = data;
    d_inMap = true;
  }

  const Key& getKey() const {
    return d_key;
  }

  const Data& get() const {
    return d_data;
  }

  operator Data() {
    return get();
  }

  CDOmap<Key, Data, HashFcn>& operator=(const Data& data) {
    set(data);
    return *this;
  }

  CDOmap<Key, Data, HashFcn>* next() const {
    if(d_next == d_cdmap->d_first) {
      return NULL;
    } else {
      return d_next;
    }
  }
};/* class CDOmap */

// Dummy subclass of ContextObj to serve as our data class
class CDMapData : public ContextObj {
  // befriend CDMap<> so that it can allocate us
  template <class Key, class Data, class HashFcn>
  friend class CDMap;

  ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDMapData(*this);
  }

  void restore(ContextObj* data) {}

public:

  CDMapData(Context* context) : ContextObj(context) {}
  CDMapData(const ContextObj& co) : ContextObj(co) {}
};

/**
 * Generic templated class for a map which must be saved and restored
 * as contexts are pushed and popped.  Requires that operator= be
 * defined for the data class, and operator== for the key class.
 */
template <class Key, class Data, class HashFcn>
class CDMap : public ContextObj {

  friend class CDOmap<Key, Data, HashFcn>;

  typedef __gnu_cxx::hash_map<Key, CDOmap<Key, Data, HashFcn>*, HashFcn> table_type;
  table_type d_map;

  // The vector of CDOmap objects to be destroyed
  std::vector<CDOmap<Key, Data, HashFcn>*> d_trash;
  CDOmap<Key, Data, HashFcn>* d_first;
  Context* d_context;

  // Nothing to save; the elements take care of themselves
  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDMapData(*this);
  }

  // Similarly, nothing to restore
  virtual void restore(ContextObj* data) {}

  // Destroy stale CDOmap objects from trash
  void emptyTrash() {
    for(typename std::vector<CDOmap<Key, Data, HashFcn>*>::iterator
          i = d_trash.begin(), iend = d_trash.end(); i != iend; ++i) {
      /*
        delete *i;
        free(*i);
      */
    }
    d_trash.clear();
  }

public:

  CDMap(Context* context) :
    ContextObj(context),
    d_first(NULL),
    d_context(context) {
  }

  ~CDMap() throw(AssertionException) {
    // Delete all the elements and clear the map
    /*for(typename table_type::iterator
          i = d_map.begin(), iend = d_map.end(); i != iend; ++i) {

        delete (*i).second;
        free((*i).second);

    }*/
    d_map.clear();
    emptyTrash();
  }

  // The usual operators of map

  size_t size() const {
    return d_map.size();
  }

  size_t count(const Key& k) const {
    return d_map.count(k);
  }

  typedef CDOmap<Key, Data, HashFcn>& ElementReference;

  // If a key is not present, a new object is created and inserted
  CDOmap<Key, Data, HashFcn>& operator[](const Key& k) {
    emptyTrash();

    typename table_type::iterator i = d_map.find(k);

    CDOmap<Key, Data, HashFcn>* obj;
    if(i == d_map.end()) {// create new object
      obj = new(true) CDOmap<Key, Data, HashFcn>(d_context, this, k, Data());
      d_map[k] = obj;
    } else {
      obj = (*i).second;
    }
    return *obj;
  }

  void insert(const Key& k, const Data& d) {
    emptyTrash();

    typename table_type::iterator i = d_map.find(k);

    if(i == d_map.end()) {// create new object
      CDOmap<Key, Data, HashFcn>*
	obj = new(true) CDOmap<Key, Data, HashFcn>(d_context, this, k, d);
      d_map[k] = obj;
    } else {
      (*i).second->set(d);
    }
  }

  // FIXME: no erase(), too much hassle to implement efficiently...

  class iterator {
    const CDOmap<Key, Data, HashFcn>* d_it;

  public:

    iterator(const CDOmap<Key, Data, HashFcn>* p) : d_it(p) {}
    iterator(const iterator& i) : d_it(i.d_it) {}

    // Default constructor
    iterator() {}

    // (Dis)equality
    bool operator==(const iterator& i) const {
      return d_it == i.d_it;
    }
    bool operator!=(const iterator& i) const {
      return d_it != i.d_it;
    }

    // Dereference operators.
    std::pair<const Key, Data> operator*() const {
      return std::pair<const Key, Data>(d_it->getKey(), d_it->get());
    }

    // Prefix increment
    iterator& operator++() {
      d_it = d_it->next();
      return *this;
    }

    // Postfix increment: requires a Proxy object to hold the
    // intermediate value for dereferencing
    class Proxy {
      const std::pair<const Key, Data>* d_pair;

    public:

      Proxy(const std::pair<const Key, Data>& p) : d_pair(&p) {}

      const std::pair<const Key, Data>& operator*() const {
        return *d_pair;
      }
    };/* class CDMap<>::iterator::Proxy */

    // Actual postfix increment: returns Proxy with the old value.
    // Now, an expression like *i++ will return the current *i, and
    // then advance the orderedIterator.  However, don't try to use
    // Proxy for anything else.
    const Proxy operator++(int) {
      Proxy e(*(*this));
      ++(*this);
      return e;
    }
  };/* class CDMap<>::iterator */

  typedef iterator const_iterator;

  iterator begin() const {
    return iterator(d_first);
  }

  iterator end() const {
    return iterator(NULL);
  }

  iterator find(const Key& k) const {
    typename table_type::const_iterator i = d_map.find(k);
    if(i == d_map.end()) {
      return end();
    } else {
      return iterator((*i).second);
    }
  }

};/* class CDMap<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDMAP_H */
