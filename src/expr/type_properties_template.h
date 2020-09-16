/*********************                                                        */
/*! \file type_properties_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Template for the Type properties header
 **
 ** Template for the Type properties header.
 **/

#include "cvc4_private.h"

#ifndef CVC4__TYPE_PROPERTIES_H
#define CVC4__TYPE_PROPERTIES_H

#include <sstream>

#include "base/check.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type_node.h"
#include "options/language.h"

${type_properties_includes}

namespace CVC4 {
namespace kind {

/**
 * Return the cardinality of the type constant represented by the
 * TypeConstant argument.  This function is auto-generated from Theory
 * "kinds" files, so includes contributions from each theory regarding
 * that theory's types.
 */
inline Cardinality getCardinality(TypeConstant tc)
{
  switch (tc)
  {
${type_constant_cardinalities}
    default: InternalError() << "No cardinality known for type constant " << tc;
  }
} /* getCardinality(TypeConstant) */

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
  default:
    InternalError() << "A theory kinds file did not provide a cardinality "
                    << "or cardinality computer for type:\n"
                    << typeNode << "\nof kind " << k;
  }
}/* getCardinality(TypeNode) */

inline bool isWellFounded(TypeConstant tc) {
  switch(tc) {
${type_constant_wellfoundednesses}
default:
  InternalError() << "No well-foundedness status known for type constant: "
                  << tc;
  }
}/* isWellFounded(TypeConstant) */

inline bool isWellFounded(TypeNode typeNode) {
  AssertArgument(!typeNode.isNull(), typeNode);
  switch(Kind k = typeNode.getKind()) {
  case TYPE_CONSTANT:
    return isWellFounded(typeNode.getConst<TypeConstant>());
${type_wellfoundednesses}
  default:
    InternalError() << "A theory kinds file did not provide a well-foundedness "
                    << "or well-foundedness computer for type:\n"
                    << typeNode << "\nof kind " << k;
  }
}/* isWellFounded(TypeNode) */

inline Node mkGroundTerm(TypeConstant tc)
{
  switch (tc)
  {
${type_constant_groundterms}
    default:
      InternalError() << "No ground term known for type constant: " << tc;
  }
} /* mkGroundTerm(TypeConstant) */

inline Node mkGroundTerm(TypeNode typeNode)
{
  AssertArgument(!typeNode.isNull(), typeNode);
  switch (Kind k = typeNode.getKind())
  {
    case TYPE_CONSTANT:
      return mkGroundTerm(typeNode.getConst<TypeConstant>());
${type_groundterms}
    default:
      InternalError() << "A theory kinds file did not provide a ground term "
                      << "or ground term computer for type:\n"
                      << typeNode << "\nof kind " << k;
  }
} /* mkGroundTerm(TypeNode) */

}/* CVC4::kind namespace */
}/* CVC4 namespace */

#endif /* CVC4__TYPE_PROPERTIES_H */
