/*********************                                                        */
/*! \file expr_names.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Aina Niemetz, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for maintaining expression names.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__EXPR_NAMES_H
#define CVC4__SMT__EXPR_NAMES_H

#include <string>

#include "context/cdhashmap.h"
#include "expr/node.h"

namespace CVC4 {
namespace smt {

/**
 * This utility is responsible for maintaining names for expressions.
 */
class ExprNames
{
 public:
  ExprNames(context::UserContext* u);
  /**
   * Get expression name.
   *
   * Return true if given expression has a name in the current context.
   * If it returns true, the name of expression 'e' is stored in 'name'.
   */
  bool getExpressionName(const Node& e, std::string& name) const;

  /**
   * Set name of given expression 'e' to 'name'.
   *
   * This information is user-context-dependent.
   * If 'e' already has a name, it is overwritten.
   */
  void setExpressionName(const Node& e, const std::string& name);

 private:
  /** mapping from expressions to name */
  context::CDHashMap< Node, std::string, NodeHashFunction > d_exprNames;
};

}  // namespace smt
}  // namespace CVC4

#endif
