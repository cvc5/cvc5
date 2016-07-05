/*********************                                                        */
/*! \file sepconst.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#pragma once

namespace CVC4 {
  // messy; Expr needs NilRef (because it's the payload of a
  // CONSTANT-kinded expression), and NilRef needs Expr.
  class CVC4_PUBLIC NilRef;
  //class CVC4_PUBLIC EmpStar;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC NilRef {
  const Type d_type;
  NilRef() { }
public:
  NilRef(Type refType):d_type(refType) { }

  ~NilRef() throw() {
  }
  Type getType() const { return d_type; }
  bool operator==(const NilRef& es) const throw() {
    return d_type == es.d_type;
  }
  bool operator!=(const NilRef& es) const throw() {
    return !(*this == es);
  }
  bool operator<(const NilRef& es) const throw() {
    return d_type < es.d_type;
  }
  bool operator<=(const NilRef& es) const throw() {
    return d_type <= es.d_type;
  }
  bool operator>(const NilRef& es) const throw() {
    return !(*this <= es);
  }
  bool operator>=(const NilRef& es) const throw() {
    return !(*this < es);
  }
};/* class NilRef */

std::ostream& operator<<(std::ostream& out, const NilRef& es) CVC4_PUBLIC;

struct CVC4_PUBLIC NilRefHashFunction {
  inline size_t operator()(const NilRef& es) const {
    return TypeHashFunction()(es.getType());
  }
};/* struct NilRefHashFunction */

}/* CVC4 namespace */
