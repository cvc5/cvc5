/*********************                                                        */
/*! \file tuple.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Tuple operators
 **
 ** Tuple operators.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__TUPLE_H
#define __CVC4__TUPLE_H

#include <iostream>
#include <string>
#include <vector>
#include <utility>

namespace CVC4 {

class CVC4_PUBLIC TupleSelect {
  unsigned d_index;
public:
  TupleSelect(unsigned index) throw() : d_index(index) { }
  unsigned getIndex() const throw() { return d_index; }
  bool operator==(const TupleSelect& t) const throw() { return d_index == t.d_index; }
  bool operator!=(const TupleSelect& t) const throw() { return d_index != t.d_index; }
};/* class TupleSelect */

class CVC4_PUBLIC TupleUpdate {
  unsigned d_index;
public:
  TupleUpdate(unsigned index) throw() : d_index(index) { }
  unsigned getIndex() const throw() { return d_index; }
  bool operator==(const TupleUpdate& t) const throw() { return d_index == t.d_index; }
  bool operator!=(const TupleUpdate& t) const throw() { return d_index != t.d_index; }
};/* class TupleUpdate */

struct CVC4_PUBLIC TupleSelectHashFunction {
  inline size_t operator()(const TupleSelect& t) const {
    return t.getIndex();
  }
};/* struct TupleSelectHashFunction */

struct CVC4_PUBLIC TupleUpdateHashFunction {
  inline size_t operator()(const TupleUpdate& t) const {
    return t.getIndex();
  }
};/* struct TupleUpdateHashFunction */

std::ostream& operator<<(std::ostream& out, const TupleSelect& t) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out, const TupleUpdate& t) CVC4_PUBLIC;

inline std::ostream& operator<<(std::ostream& out, const TupleSelect& t) {
  return out << "[" << t.getIndex() << "]";
}

inline std::ostream& operator<<(std::ostream& out, const TupleUpdate& t) {
  return out << "[" << t.getIndex() << "]";
}

}/* CVC4 namespace */

#endif /* __CVC4__TUPLE_H */
