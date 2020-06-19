/*********************                                                        */
/*! \file java_iterator_adapter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An iterator adapter for the Java bindings, giving Java iterators
 ** the ability to access elements from STL iterators.
 **
 ** An iterator adapter for the Java bindings, giving Java iterators the
 ** ability to access elements from STL iterators.  This class is mapped
 ** into Java by SWIG, where it implements Iterator (some additional
 ** Java-side functions are added by the SWIG layer to implement the full
 ** interface).
 **
 ** The functionality requires significant assistance from the ".i" SWIG
 ** interface files, applying a variety of typemaps.
 **/

// private to the bindings layer
#ifndef SWIGJAVA
#  error This should only be included from the Java bindings layer.
#endif /* SWIGJAVA */

#ifndef CVC4__BINDINGS__JAVA_ITERATOR_ADAPTER_H
#define CVC4__BINDINGS__JAVA_ITERATOR_ADAPTER_H

#include <type_traits>

namespace CVC4 {

template <class T, class value_type>
class JavaIteratorAdapter
{
 public:
  JavaIteratorAdapter(const T& t) : d_t(t), d_it(d_t.begin())
  {
    static_assert(
        std::is_convertible<typename T::const_iterator::value_type,
                            value_type>(),
        "value_type must be convertible from T::const_iterator::value_type");
  }

  JavaIteratorAdapter() = delete;

  bool hasNext() { return d_it != d_t.end(); }

  value_type getNext()
  {
    value_type ret = *d_it;
    ++d_it;
    return ret;
  }

 private:
  const T& d_t;
  typename T::const_iterator d_it;
}; /* class JavaIteratorAdapter<T, value_type> */

}  // namespace CVC4

#endif /* CVC4__BINDINGS__JAVA_ITERATOR_ADAPTER_H */
