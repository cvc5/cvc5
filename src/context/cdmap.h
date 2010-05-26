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

#include <vector>
#include <iterator>
#include <ext/hash_map>

namespace CVC4 {
namespace context {

// Auxiliary class: almost the same as CDO (see cdo.h)

template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> > class CDMap;

template <class T, class U>
inline std::ostream& operator<<(std::ostream& out, const std::pair<T, U>& p) {
  return out << "[" << p.first << "," << p.second << "]";
}

template <class Key, class Data, class HashFcn = __gnu_cxx::hash<Key> >
class CDOmap : public ContextObj {
  friend class CDMap<Key, Data, HashFcn>;

  Key d_key;
  Data d_data;
  CDMap<Key, Data, HashFcn>* d_map;

  // Doubly-linked list for keeping track of elements in order of insertion
  CDOmap* d_prev;
  CDOmap* d_next;

  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDOmap(*this);
  }

  virtual void restore(ContextObj* data) {
    CDOmap* p = static_cast<CDOmap*>(data);
    if(p->d_map == NULL) {
      Assert(d_map->d_map.find(d_key) != d_map->d_map.end() &&
             (*d_map->d_map.find(d_key)).second == this);
      // no longer in map (popped beyond first level in which it was)
      d_map->d_map.erase(d_key);
      // If we call deleteSelf() here, it re-enters restore().  So,
      // put it on a "trash heap" instead, for later deletion.
      //
      // FIXME multithreading
      if(d_map->d_first == this) {
        Debug("gc") << "remove first-elem " << this << " from map " << d_map << " with next-elem " << d_next << std::endl;
        if(d_next == this) {
          Assert(d_prev == this);
          d_map->d_first = NULL;
        } else {
          d_map->d_first = d_next;
        }
      } else {
        Debug("gc") << "remove nonfirst-elem " << this << " from map " << d_map << std::endl;
      }
      d_next->d_prev = d_prev;
      d_prev->d_next = d_next;
      Debug("gc") << "CDMap<> trash push_back " << this << std::endl;
      d_map->d_trash.push_back(this);
    } else {
      d_data = p->d_data;
    }
  }

public:

  CDOmap(Context* context,
         CDMap<Key, Data, HashFcn>* map,
	 const Key& key,
         const Data& data) :
    ContextObj(context),
    d_key(key),
    d_map(NULL) {

    // makeCurrent(), then set the data and then the map.  Order is
    // important; we can't initialize d_map in the constructor init
    // list above, because we want the restore of d_map to NULL to
    // signal us to remove the element from the map.
    set(data);
    d_map = map;

    CDOmap*& first = d_map->d_first;
    if(first == NULL) {
      first = d_next = d_prev = this;
      Debug("gc") << "add first-elem " << this << " to map " << d_map << std::endl;
    } else {
      Debug("gc") << "add nonfirst-elem " << this << " to map " << d_map << " with first-elem " << first << "[" << first->d_prev << " " << first->d_next << std::endl;
      d_prev = first->d_prev;
      d_next = first;
      d_prev->d_next = this;
      first->d_prev = this;
    }
  }

  ~CDOmap() throw(AssertionException) {
    destroy();
  }

  void set(const Data& data) {
    makeCurrent();
    d_data = data;
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

  CDOmap& operator=(const Data& data) {
    set(data);
    return *this;
  }

  CDOmap* next() const {
    if(d_next == d_map->d_first) {
      return NULL;
    } else {
      return d_next;
    }
  }
};/* class CDOmap<> */


/**
 * Generic templated class for a map which must be saved and restored
 * as contexts are pushed and popped.  Requires that operator= be
 * defined for the data class, and operator== for the key class.
 */
template <class Key, class Data, class HashFcn>
class CDMap : public ContextObj {

  typedef CDOmap<Key, Data, HashFcn> Element;
  typedef __gnu_cxx::hash_map<Key, Element*, HashFcn> table_type;

  friend class CDOmap<Key, Data, HashFcn>;

  table_type d_map;

  Element* d_first;
  Context* d_context;

  std::vector<Element*> d_trash;

  // Nothing to save; the elements take care of themselves
  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    Unreachable();
  }

  // Similarly, nothing to restore
  virtual void restore(ContextObj* data) {
    Unreachable();
  }

  void emptyTrash() {
    //FIXME multithreading
    for(typename std::vector<Element*>::iterator i = d_trash.begin();
        i != d_trash.end();
        ++i) {
      Debug("gc") << "emptyTrash(): " << *i << std::endl;
      (*i)->deleteSelf();
    }
    d_trash.clear();
  }

public:

  CDMap(Context* context) :
    ContextObj(context),
    d_map(),
    d_first(NULL),
    d_context(context),
    d_trash() {
  }

  ~CDMap() throw(AssertionException) {
    Debug("gc") << "cdmap " << this
                << " disappearing, destroying..." << std::endl;
    destroy();
    Debug("gc") << "cdmap " << this
                << " disappearing, done destroying" << std::endl;
    for(typename table_type::iterator i = d_map.begin();
        i != d_map.end();
        ++i) {
      (*i).second->deleteSelf();
    }
    Debug("gc") << "cdmap " << this << " gone, emptying trash" << std::endl;
    emptyTrash();
    Debug("gc") << "done emptying trash for " << this << std::endl;
  }

  void clear() throw(AssertionException) {
    Debug("gc") << "cdmap " << this
                << " disappearing, destroying..." << std::endl;
    for(typename table_type::iterator i = d_map.begin();
        i != d_map.end();
        ++i) {
      (*i).second->deleteSelf();
    }
    d_map.clear();
    emptyTrash();
    Debug("gc") << "done emptying trash for " << this << std::endl;
  }


  // The usual operators of map

  size_t size() const {
    return d_map.size();
  }

  size_t count(const Key& k) const {
    return d_map.count(k);
  }

  // If a key is not present, a new object is created and inserted
  Element& operator[](const Key& k) {
    emptyTrash();

    typename table_type::iterator i = d_map.find(k);

    Element* obj;
    if(i == d_map.end()) {// create new object
      obj = new(true) Element(d_context, this, k, Data());
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
      Element* obj = new(true) Element(d_context, this, k, d);
      d_map[k] = obj;
    } else {
      (*i).second->set(d);
    }
  }

  // FIXME: no erase(), too much hassle to implement efficiently...

  /**
   * "Obliterating" is kind of like erasing, except it's not
   * backtrackable; the key is permanently removed from the map.
   * (Naturally, it can be re-added as a new element.)
   */
  void obliterate(const Key& k) {
    typename table_type::iterator i = d_map.find(k);
    if(i != d_map.end()) {
      Debug("gc") << "key " << k << " obliterated" << std::endl;
      // We can't call ->deleteSelf() here, because it calls the
      // ContextObj destructor, which calls CDOmap::destroy(), which
      // restore()'s, which puts the CDOmap on the trash, which causes
      // a double-delete.
      (*i).second->~Element();
      // Writing ...->~CDOmap() in the above is legal (?) but breaks
      // g++ 4.1, though later versions have no problem.

      typename table_type::iterator j = d_map.find(k);
      // This if() succeeds for objects inserted when in the
      // zero-scope: they were never save()'d there, so restore()
      // never gets a NULL map and so they leak.
      if(j != d_map.end()) {
        Element* elt = (*j).second;
        if(d_first == elt) {
          if(elt->d_next == elt) {
            Assert(elt->d_prev == elt);
            d_first = NULL;
          } else {
            d_first = elt->d_next;
          }
        } else {
          elt->d_prev->d_next = elt->d_next;
          elt->d_next->d_prev = elt->d_prev;
        }
        d_map.erase(j);//FIXME multithreading
        Debug("gc") << "key " << k << " obliterated zero-scope: " << elt << std::endl;
        // was already destructed, so don't call ->deleteSelf()
        ::operator delete(elt);
      }
    }
  }

  class iterator {
    const Element* d_it;

  public:

    iterator(const Element* p) : d_it(p) {}
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
    // then advance the iterator.  However, don't try to use
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

  iterator find(const Key& k) {
    emptyTrash();
    return const_cast<const CDMap*>(this)->find(k);
  }

};/* class CDMap<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDMAP_H */
