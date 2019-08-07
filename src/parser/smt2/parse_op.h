/*********************                                                        */
/*! \file parse_op.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of parsed operators in smt2.
 **/

#include "cvc4parser_private.h"

#ifndef CVC4__PARSER__SMT2__PARSE_OP_H
#define CVC4__PARSER__SMT2__PARSE_OP_H

#include <string>

#include "expr/expr.h"
#include "expr/kind.h"

namespace CVC4 {

/** A parsed operator
 * 
 */
class ParseOp
{
public:
  ParseOp() : d_kind(kind::NULL_EXPR){}
  Kind d_kind;
  std::string d_name;
  Expr d_expr; 
  Type d_type;
};
  
}/* CVC4 namespace */

#endif /* CVC4__PARSER__SMT2__PARSE_OP_H */
