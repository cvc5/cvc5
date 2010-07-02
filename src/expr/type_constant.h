/*********************                                                        */
/*! \file type_constant.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interface for expression types.
 **
 ** Interface for expression types
 **/

#ifndef __CVC4__TYPE_CONSTANT_H_
#define __CVC4__TYPE_CONSTANT_H_

namespace CVC4 {

/**
 * The enumeration for the built-in atomic types.
 */
enum TypeConstant {
  /** The Boolean type */
  BOOLEAN_TYPE,
  /** The integer type */
  INTEGER_TYPE,
  /** The real type */
  REAL_TYPE,
  /** The kind type (type of types) */
  KIND_TYPE
};

/**
 * We hash the constants with their values.
 */
struct TypeConstantHashStrategy {
  static inline size_t hash(TypeConstant tc) {
    return tc;
  }
};/* struct BoolHashStrategy */

inline std::ostream& operator<<(std::ostream& out, TypeConstant typeConstant) {

  switch(typeConstant) {
  case BOOLEAN_TYPE:
    out << "BOOLEAN";
    break;
  case INTEGER_TYPE:
    out << "INTEGER";
    break;
  case REAL_TYPE:
    out << "REAL";
    break;
  case KIND_TYPE:
    out << "KIND";
    break;
  default:
    out << "UNKNOWN_TYPE_CONSTANT";
    break;
  }
  return out;
}

}

#endif /* __CVC4__TYPE_CONSTANT_H_ */
