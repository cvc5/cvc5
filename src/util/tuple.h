/*********************                                                        */
/*! \file tuple.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Tuple operators
 **
 ** Tuple operators.
 **/

#include "cvc4_public.h"

#ifndef CVC4__TUPLE_H
#define CVC4__TUPLE_H

#include <iostream>
#include <string>
#include <vector>
#include <utility>

namespace CVC4 {

class CVC4_PUBLIC TupleUpdate {
  unsigned d_index;

 public:
  TupleUpdate(unsigned index) : d_index(index) {}
  unsigned getIndex() const { return d_index; }
  bool operator==(const TupleUpdate& t) const { return d_index == t.d_index; }
  bool operator!=(const TupleUpdate& t) const { return d_index != t.d_index; }
};/* class TupleUpdate */

struct CVC4_PUBLIC TupleUpdateHashFunction {
  inline size_t operator()(const TupleUpdate& t) const {
    return t.getIndex();
  }
};/* struct TupleUpdateHashFunction */

std::ostream& operator<<(std::ostream& out, const TupleUpdate& t) CVC4_PUBLIC;

inline std::ostream& operator<<(std::ostream& out, const TupleUpdate& t) {
  return out << "[" << t.getIndex() << "]";
}

}/* CVC4 namespace */

#endif /* CVC4__TUPLE_H */
