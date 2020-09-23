/*********************                                                        */
/*! \file cdhashset.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent set class.
 **
 ** Context-dependent set class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__CONTEXT__CDHASHSET_H
#define CVC4__CONTEXT__CDHASHSET_H

#include "base/check.h"
#include "context/cdinsert_hashmap.h"
#include "context/context.h"

namespace CVC4 {
namespace context {

template <class V, class HashFcn>
class CDHashSet : protected CDInsertHashMap<V, bool, HashFcn> {
  typedef CDInsertHashMap<V, bool, HashFcn> super;

  // no copy or assignment
  CDHashSet(const CDHashSet&) = delete;
  CDHashSet& operator=(const CDHashSet&) = delete;

public:

  // ensure these are publicly accessible
  static void* operator new(size_t size, bool b) {
    return ContextObj::operator new(size, b);
  }

  static void operator delete(void* pMem, bool b) {
    return ContextObj::operator delete(pMem, b);
  }

  void deleteSelf() {
    this->ContextObj::deleteSelf();
  }

  static void operator delete(void* pMem) {
    AlwaysAssert(false) << "It is not allowed to delete a ContextObj this way!";
  }

  CDHashSet(Context* context) :
    super(context) {
  }

  size_t size() const {
    return super::size();
  }

  bool empty() const {
    return super::empty();
  }

  bool insert(const V& v) {
    return super::insert_safe(v, true);
  }

  bool contains(const V& v) const {
    return super::contains(v);
  }

  class const_iterator {
    typename super::const_iterator d_it;

  public:

    const_iterator(const typename super::const_iterator& it) : d_it(it) {}
    const_iterator(const const_iterator& it) : d_it(it.d_it) {}

    // Default constructor
    const_iterator() {}

    // (Dis)equality
    bool operator==(const const_iterator& i) const {
      return d_it == i.d_it;
    }
    bool operator!=(const const_iterator& i) const {
      return d_it != i.d_it;
    }

    // Dereference operators.
    V operator*() const {
      return (*d_it).first;
    }

    // Prefix increment
    const_iterator& operator++() {
      ++d_it;
      return *this;
    }

    // Postfix increment: requires a Proxy object to hold the
    // intermediate value for dereferencing
    class Proxy {
      const V& d_val;

    public:

      Proxy(const V& v) : d_val(v) {}

      V operator*() const {
        return d_val;
      }
    };/* class CDSet<>::iterator::Proxy */

    // Actual postfix increment: returns Proxy with the old value.
    // Now, an expression like *i++ will return the current *i, and
    // then advance the orderedIterator.  However, don't try to use
    // Proxy for anything else.
    const Proxy operator++(int) {
      Proxy e(*(*this));
      ++(*this);
      return e;
    }
  };/* class CDSet<>::iterator */

  const_iterator begin() const {
    return const_iterator(super::begin());
  }

  const_iterator end() const {
    return const_iterator(super::end());
  }

  const_iterator find(const V& v) const {
    return const_iterator(super::find(v));
  }

  typedef typename super::key_iterator key_iterator;
  key_iterator key_begin() const {
    return super::key_begin();
  }
  key_iterator key_end() const {
    return super::key_end();
  }

  void insertAtContextLevelZero(const V& v) {
    return super::insertAtContextLevelZero(v, true);
  }

};/* class CDHashSet */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CDHASHSET_H */
