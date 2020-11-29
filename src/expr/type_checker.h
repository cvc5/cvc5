/*********************                                                        */
/*! \file type_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A type checker
 **
 ** A type checker.
 **/

#include "cvc4_private.h"

// ordering dependence
#include "expr/node.h"

#ifndef CVC4__EXPR__TYPE_CHECKER_H
#define CVC4__EXPR__TYPE_CHECKER_H

namespace CVC4 {
namespace expr {

class TypeChecker {
public:
 static TypeNode computeType(NodeManager* nodeManager,
                             TNode n,
                             bool check = false);

 static bool computeIsConst(NodeManager* nodeManager, TNode n);

};/* class TypeChecker */

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* CVC4__EXPR__TYPE_CHECKER_H */
