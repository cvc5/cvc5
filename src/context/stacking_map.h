/*********************                                                        */
/*! \file stacking_map.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Backtrackable map using an undo stack
 **
 ** Backtrackable map using an undo stack rather than storing items in
 ** a CDMap<>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__STACKING_MAP_H
#define __CVC4__CONTEXT__STACKING_MAP_H

#include <utility>
#include <vector>
#include <ext/hash_map>

#include "expr/node.h"
#include "context/cdo.h"

namespace CVC4 {
namespace context {

template <class T>
struct StackingMapArgType {
  typedef T argtype;
};/* struct StackingMapArgType<T> */

template <>
struct StackingMapArgType<Node> {
  typedef TNode argtype;
};/* struct StackingMapArgType<Node> */


template <class KeyType, class ValueType, class KeyHash>
struct StackingMapRestoreValue {
  typedef typename StackingMapArgType<KeyType>::argtype ArgType;
  static void restore(__gnu_cxx::hash_map<KeyType, ValueType, KeyHash>& map, const ArgType& k, const ValueType& v) {
    map[k] = v;
  }
};/* struct StackingMapRestoreValue<KeyType, ValueType, KeyHash> */

template <class KeyType, class KeyHash>
struct StackingMapRestoreValue<KeyType, Node, KeyHash> {
  typedef typename StackingMapArgType<KeyType>::argtype ArgType;
  static void restore(__gnu_cxx::hash_map<KeyType, Node, KeyHash>& map, const ArgType& k, TNode v) {
    if(v.isNull()) {
      map.erase(k);
    } else {
      map[k] = v;
    }
  }
};/* struct StackingMapRestoreValue<KeyType, Node, KeyHash> */

template <class KeyType, class KeyHash>
struct StackingMapRestoreValue<KeyType, TNode, KeyHash> {
  typedef typename StackingMapArgType<KeyType>::argtype ArgType;
  static void restore(__gnu_cxx::hash_map<KeyType, TNode, KeyHash>& map, const ArgType& k, TNode v) {
    if(v.isNull()) {
      map.erase(k);
    } else {
      map[k] = v;
    }
  }
};/* struct StackingMapRestoreValue<KeyType, TNode, KeyHash> */


template <class KeyType, class ValueType, class KeyHash>
class StackingMap : context::ContextNotifyObj {
  /** Our underlying map type. */
  typedef __gnu_cxx::hash_map<KeyType, ValueType, KeyHash> MapType;

  /**
   * The type for arguments being passed in.  It's the same as
   * KeyType, unless KeyType is Node, then it's TNode for efficiency.
   */
  typedef typename StackingMapArgType<KeyType>::argtype ArgType;

  /** Our map of keys to their values. */
  MapType d_map;

  /** Our undo stack for changes made to d_map. */
  std::vector<std::pair<ArgType, ValueType> > d_trace;

  /** Our current offset in the d_trace stack (context-dependent). */
  context::CDO<size_t> d_offset;

protected:

  /**
   * Called by the Context when a pop occurs.  Cancels everything to the
   * current context level.  Overrides ContextNotifyObj::contextNotifyPop().
   */
  void contextNotifyPop();

public:
  typedef typename MapType::const_iterator const_iterator;

  StackingMap(context::Context* ctxt) :
    context::ContextNotifyObj(ctxt),
    d_offset(ctxt, 0) {
  }

  ~StackingMap() throw() { }

  const_iterator find(ArgType n) const { return d_map.find(n); }
  const_iterator end() const { return d_map.end(); }

  /**
   * Return a key's value in the key-value map.  If n is not a key in
   * the map, this function returns a default-constructed value.
   */
  ValueType operator[](ArgType n) const {
    const_iterator it = find(n);
    if(it == end()) {
      return ValueType();
    } else {
      return (*it).second;
    }
  }
  //ValueType& operator[](ArgType n) { return d_map[n]; }// not permitted--bypasses set() logic

  /**
   * Set the value in the key-value map for Node n to newValue.
   */
  void set(ArgType n, const ValueType& newValue);

};/* class StackingMap<> */

template <class KeyType, class ValueType, class KeyHash>
void StackingMap<KeyType, ValueType, KeyHash>::set(ArgType n, const ValueType& newValue) {
  Trace("sm") << "SM setting " << n << " : " << newValue << " @ " << d_trace.size() << std::endl;
  ValueType& ref = d_map[n];
  d_trace.push_back(std::make_pair(n, ValueType(ref)));
  d_offset = d_trace.size();
  ref = newValue;
}

template <class KeyType, class ValueType, class KeyHash>
void StackingMap<KeyType, ValueType, KeyHash>::contextNotifyPop() {
  Trace("sm") << "SM cancelling : " << d_offset << " < " << d_trace.size() << " ?" << std::endl;
  while(d_offset < d_trace.size()) {
    std::pair<ArgType, ValueType> p = d_trace.back();
    StackingMapRestoreValue<KeyType, ValueType, KeyHash>::restore(d_map, p.first, p.second);
    d_trace.pop_back();
  }
  Trace("sm") << "SM cancelling finished." << std::endl;
}

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /*__CVC4__CONTEXT__STACKING_MAP_H */
