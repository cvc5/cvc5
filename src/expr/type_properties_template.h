/*********************                                                        */
/*! \file type_properties_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Template for the Type properties header
 **
 ** Template for the Type properties header.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__TYPE_PROPERTIES_H
#define __CVC4__TYPE_PROPERTIES_H

#line 23 "${template}"

#include <sstream>

#include "base/cvc4_assert.h"
#include "options/language.h"
#include "expr/type_node.h"
#include "expr/kind.h"
#include "expr/expr.h"

${type_properties_includes}

#line 35 "${template}"

namespace CVC4 {
namespace kind {

/**
 * Return the cardinality of the type constant represented by the
 * TypeConstant argument.  This function is auto-generated from Theory
 * "kinds" files, so includes contributions from each theory regarding
 * that theory's types.
 */
inline Cardinality getCardinality(TypeConstant tc) {
  switch(tc) {
${type_constant_cardinalities}
#line 49 "${template}"
  default: {
    std::stringstream ss;
    ss << "No cardinality known for type constant " << tc;
    InternalError(ss.str());
  }
  }
}/* getCardinality(TypeConstant) */

/**
 * Return the cardinality of the type represented by the TypeNode
 * argument.  This function is auto-generated from Theory "kinds"
 * files, so includes contributions from each theory regarding that
 * theory's types.
 */
inline Cardinality getCardinality(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return getCardinality(typeNode.getConst<TypeConstant>());
${type_cardinalities}
#line 70 "${template}"
  default: {
    std::stringstream ss;
    ss << "A theory kinds file did not provide a cardinality "
       << "or cardinality computer for type:\n" << typeNode
       << "\nof kind " << k;
    InternalError(ss.str());
  }
  }
}/* getCardinality(TypeNode) */

inline bool isWellFounded(TypeConstant tc) {
  switch(tc) {
${type_constant_wellfoundednesses}
#line 84 "${template}"
  default: {
    std::stringstream ss;
    ss << "No well-foundedness status known for type constant: " << tc;
    InternalError(ss.str());
  }
  }
}/* isWellFounded(TypeConstant) */

inline bool isWellFounded(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return isWellFounded(typeNode.getConst<TypeConstant>());
${type_wellfoundednesses}
#line 99 "${template}"
  default: {
    std::stringstream ss;
    ss << "A theory kinds file did not provide a well-foundedness "
       << "or well-foundedness computer for type:\n" << typeNode
       << "\nof kind " << k;
    InternalError(ss.str());
  }
  }
}/* isWellFounded(TypeNode) */

inline Node mkGroundTerm(TypeConstant tc) {
  switch(tc) {
${type_constant_groundterms}
#line 113 "${template}"
  default: {
    std::stringstream ss;
    ss << "No ground term known for type constant: " << tc;
    InternalError(ss.str());
  }
  }
}/* mkGroundTerm(TypeConstant) */

inline Node mkGroundTerm(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return mkGroundTerm(typeNode.getConst<TypeConstant>());
${type_groundterms}
#line 128 "${template}"
  default: {
    std::stringstream ss;
    ss << "A theory kinds file did not provide a ground term "
       << "or ground term computer for type:\n" << typeNode
       << "\nof kind " << k;
    InternalError(ss.str());
  }
  }
}/* mkGroundTerm(TypeNode) */

}/* CVC4::kind namespace */
}/* CVC4 namespace */

#endif /* __CVC4__TYPE_PROPERTIES_H */
