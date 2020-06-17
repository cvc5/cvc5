/*********************                                                        */
/*! \file ascription_type.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a type ascription
 **
 ** A class representing a parameter for the type ascription operator.
 **/

#include "cvc4_public.h"

#ifndef CVC4__ASCRIPTION_TYPE_H
#define CVC4__ASCRIPTION_TYPE_H

#include "expr/type.h"

namespace CVC4 {

/**
 * A class used to parameterize a type ascription.  For example,
 * "nil :: list<nat>" is an expression of kind APPLY_TYPE_ASCRIPTION.
 * The parameter is an ASCRIPTION_TYPE-kinded expression with an
 * AscriptionType payload.  (Essentially, all of this is a way to
 * coerce a Type into the expression tree.)
 */
class CVC4_PUBLIC AscriptionType {
  Type d_type;

 public:
  AscriptionType(Type t) : d_type(t) {}
  Type getType() const { return d_type; }
  bool operator==(const AscriptionType& other) const
  {
    return d_type == other.d_type;
  }
  bool operator!=(const AscriptionType& other) const
  {
    return d_type != other.d_type;
  }
};/* class AscriptionType */

/**
 * A hash function for type ascription operators.
 */
struct CVC4_PUBLIC AscriptionTypeHashFunction {
  inline size_t operator()(const AscriptionType& at) const {
    return TypeHashFunction()(at.getType());
  }
};/* struct AscriptionTypeHashFunction */

/** An output routine for AscriptionTypes */
inline std::ostream& operator<<(std::ostream& out, AscriptionType at) {
  out << at.getType();
  return out;
}

}/* CVC4 namespace */

#endif /* CVC4__ASCRIPTION_TYPE_H */
