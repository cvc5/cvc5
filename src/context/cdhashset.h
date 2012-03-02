/*********************                                                        */
/*! \file cdset.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent set class.
 **
 ** Context-dependent set class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDSET_H
#define __CVC4__CONTEXT__CDSET_H

#include "context/context.h"
#include "context/cdhashset_forward.h"
#include "context/cdhashmap.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {

template <class V, class HashFcn>
class CDHashSet : protected CDHashMap<V, V, HashFcn> {
  typedef CDHashMap<V, V, HashFcn> super;

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
    AlwaysAssert(false, "It is not allowed to delete a ContextObj this way!");
  }

  CDHashSet(Context* context) :
    super(context) {
  }

  size_t size() const {
    return super::size();
  }

  size_t count(const V& v) const {
    return super::count(v);
  }

  bool insert(const V& v) {
    return super::insert(v, v);
  }

  bool contains(const V& v) {
    return find(v) != end();
  }

  // FIXME: no erase(), too much hassle to implement efficiently...

  class iterator {
    typename super::iterator d_it;

  public:

    iterator(const typename super::iterator& it) : d_it(it) {}
    iterator(const iterator& it) : d_it(it.d_it) {}

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
    V operator*() const {
      return (*d_it).first;
    }

    // Prefix increment
    iterator& operator++() {
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

  typedef iterator const_iterator;

  const_iterator begin() const {
    return iterator(super::begin());
  }

  const_iterator end() const {
    return iterator(super::end());
  }

  const_iterator find(const V& v) const {
    return iterator(super::find(v));
  }

};/* class CDSet */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDSET_H */
