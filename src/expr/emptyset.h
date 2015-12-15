/*********************                                                        */
/*! \file emptyset.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
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
  // messy; Expr needs EmptySet (because it's the payload of a
  // CONSTANT-kinded expression), and EmptySet needs Expr.
  class CVC4_PUBLIC EmptySet;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC EmptySet {

  const SetType d_type;

  EmptySet() { }
public:

  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  EmptySet(SetType setType):d_type(setType) { }


  ~EmptySet() throw() {
  }

  SetType getType() const { return d_type; }

  bool operator==(const EmptySet& es) const throw() {
    return d_type == es.d_type;
  }
  bool operator!=(const EmptySet& es) const throw() {
    return !(*this == es);
  }

  bool operator<(const EmptySet& es) const throw() {
    return d_type < es.d_type;
  }
  bool operator<=(const EmptySet& es) const throw() {
    return d_type <= es.d_type;
  }
  bool operator>(const EmptySet& es) const throw() {
    return !(*this <= es);
  }
  bool operator>=(const EmptySet& es) const throw() {
    return !(*this < es);
  }

};/* class EmptySet */

std::ostream& operator<<(std::ostream& out, const EmptySet& es) CVC4_PUBLIC;

struct CVC4_PUBLIC EmptySetHashFunction {
  inline size_t operator()(const EmptySet& es) const {
    return TypeHashFunction()(es.getType());
  }
};/* struct EmptySetHashFunction */

}/* CVC4 namespace */
