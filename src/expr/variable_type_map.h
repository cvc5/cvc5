/*********************                                                        */
/*! \file variable_type_map.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef CVC4__VARIABLE_TYPE_MAP_H
#define CVC4__VARIABLE_TYPE_MAP_H

#include <unordered_map>

#include "expr/expr.h"

namespace CVC4 {

class Expr;
struct ExprHashFunction;
class Type;
struct TypeHashFunction;

class CVC4_PUBLIC VariableTypeMap {
  /**
   * A map Expr -> Expr, intended to be used for a mapping of variables
   * between two ExprManagers.
   */
  std::unordered_map<Expr, Expr, ExprHashFunction> d_variables;

  /**
   * A map Type -> Type, intended to be used for a mapping of types
   * between two ExprManagers.
   */
  std::unordered_map<Type, Type, TypeHashFunction> d_types;

public:
  Expr& operator[](Expr e) { return d_variables[e]; }
  Type& operator[](Type t) { return d_types[t]; }

};/* class VariableTypeMap */

typedef std::unordered_map<uint64_t, uint64_t> VarMap;

struct CVC4_PUBLIC ExprManagerMapCollection {
  VariableTypeMap d_typeMap;
  VarMap d_to;
  VarMap d_from;
};/* struct ExprManagerMapCollection */

}/* CVC4 namespace */

#endif /* CVC4__VARIABLE_MAP_H */
