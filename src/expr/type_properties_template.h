/*********************                                                        */
/*! \file type_properties_template.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Template for the Type properties header
 **
 ** Template for the Type properties header.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__TYPE_PROPERTIES_H
#define __CVC4__TYPE_PROPERTIES_H

#line 25 "${template}"

#include "expr/type_node.h"
#include "util/Assert.h"
#include "expr/kind.h"
#include "expr/expr.h"
#include "util/language.h"

#include <sstream>

${type_properties_includes}

#line 37 "${template}"

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
#line 51 "${template}"
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
#line 72 "${template}"
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
#line 86 "${template}"
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
#line 101 "${template}"
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
#line 115 "${template}"
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
#line 130 "${template}"
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
