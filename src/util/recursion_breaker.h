/*********************                                                        */
/*! \file recursion_breaker.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A utility class to help with detecting recursion in a
 ** computation
 **
 ** A utility class to help with detecting recursion in a computation.
 ** A breadcrumb trail is left, and a function can query the breaker
 ** to see if recursion has occurred.  For example:
 **
 ** @code
 **   int foo(int x) {
 **     RecursionBreaker<int> breaker("foo", x);
 **     if(breaker.isRecursion()) {
 **       ++d_count;
 **       return 0;
 **     }
 **     int xfactor = x * x;
 **     if(x > 0) {
 **       xfactor = -xfactor;
 **     }
 **     int y = foo(11 * x + xfactor);
 **     int z = y < 0 ? y : x * y;
 **     cout << "x == " << x << ", y == " << y << " ==> " << z << endl;
 **     return z;
 **   }
 ** @endcode
 **
 ** Recursion occurs after a while in this example, and the recursion
 ** is broken by the RecursionBreaker.
 **
 ** RecursionBreaker is really just a thread-local set of "what has
 ** been seen."  The above example is trivial, easily fixed by
 ** allocating such a set at the base of the recursion, and passing a
 ** reference to it to each invocation.  But other cases of
 ** nontrivial, mutual recursion exist that aren't so easily broken,
 ** and that's what the RecursionBreaker is for.  See
 ** Datatype::getCardinality(), for example.  A Datatype's cardinality
 ** depends on the cardinalities of the types it references---but
 ** these, in turn can reference the original datatype in a cyclic
 ** fashion.  Where that happens, we need to break the recursion.
 **
 ** Several RecursionBreakers can be used at once; each is identified
 ** by the string tag in its constructor.  If a single function is
 ** involved in the detection of recursion, a good choice is to use
 ** __FUNCTION__:
 **
 **   RecursionBreaker<Foo*>(__FUNCTION__, this) breaker;
 **
 ** Of course, if you're using GNU, you might prefer
 ** __PRETTY_FUNCTION__, since it's robust to overloading, namespaces,
 ** and containing classes.  But neither is a good choice if two
 ** functions need to access the same RecursionBreaker mechanism.
 **
 ** For non-primitive datatypes, it might be a good idea to use a
 ** pointer type to instantiate RecursionBreaker<>, for example with
 ** RecursionBreaker<Foo*>.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__RECURSION_BREAKER_H
#define __CVC4__RECURSION_BREAKER_H

#include <string>
#include <map>
#include <ext/hash_set>
#include "util/hash.h"
#include "util/tls.h"
#include "util/cvc4_assert.h"

namespace CVC4 {

template <class T, class Hasher = std::hash<T> >
class RecursionBreaker {
  typedef std::hash_set<T, Hasher> Set;
  typedef std::map<std::string, Set> Map;
  static CVC4_THREADLOCAL(Map*) s_maps;

  std::string d_tag;
  const T d_item;
  bool d_firstToTag;
  bool d_recursion;

public:
  /** Mark that item has been seen for tag. */
  RecursionBreaker(std::string tag, const T& item) :
    d_tag(tag),
    d_item(item) {
    if(s_maps == NULL) {
      s_maps = new Map();
    }
    d_firstToTag = s_maps->find(tag) == s_maps->end();
    Set& set = (*s_maps)[tag];
    d_recursion = (set.find(item) != set.end());
    Assert(!d_recursion || !d_firstToTag);
    if(!d_recursion) {
      set.insert(item);
    }
  }

  /** Clean up the seen trail. */
  ~RecursionBreaker() {
    Assert(s_maps->find(d_tag) != s_maps->end());
    if(!d_recursion) {
      (*s_maps)[d_tag].erase(d_item);
    }
    if(d_firstToTag) {
      Assert((*s_maps)[d_tag].empty());
      s_maps->erase(d_tag);
      Assert(s_maps->find(d_tag) == s_maps->end());
    }
  }

  /** Return true iff recursion has been detected. */
  bool isRecursion() const throw() {
    return d_recursion;
  }

};/* class RecursionBreaker<T> */

template <class T, class Hasher>
CVC4_THREADLOCAL(typename RecursionBreaker<T, Hasher>::Map*) RecursionBreaker<T, Hasher>::s_maps;

}/* CVC4 namespace */

#endif /* __CVC4__RECURSION_BREAKER_H */
