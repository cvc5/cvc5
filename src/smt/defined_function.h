/*********************                                                        */
/*! \file defined_function.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Defined function data structure
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__DEFINED_FUNCTION_H
#define CVC4__SMT__DEFINED_FUNCTION_H

#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace smt {

/**
 * Representation of a defined function.  We keep these around in
 * SmtEngine to permit expanding definitions late (and lazily), to
 * support getValue() over defined functions, to support user output
 * in terms of defined functions, etc.
 */
class DefinedFunction
{
 public:
  DefinedFunction() {}
  DefinedFunction(Node func, std::vector<Node>& formals, Node formula)
      : d_func(func), d_formals(formals), d_formula(formula)
  {
  }
  /** get the function */
  Node getFunction() const { return d_func; }
  /** get the formal argument list of the function */
  const std::vector<Node>& getFormals() const { return d_formals; }
  /** get the formula that defines it */
  Node getFormula() const { return d_formula; }

 private:
  /** the function */
  Node d_func;
  /** the formal argument list */
  std::vector<Node> d_formals;
  /** the formula */
  Node d_formula;
}; /* class DefinedFunction */

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__DEFINED_FUNCTION_H */
