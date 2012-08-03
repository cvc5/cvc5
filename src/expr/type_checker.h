/*********************                                                        */
/*! \file type_checker.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, dejan
 ** Minor contributors (to current version): acsys, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A type checker
 **
 ** A type checker.
 **/

#include "cvc4_private.h"

// ordering dependence
#include "expr/node.h"

#ifndef __CVC4__EXPR__TYPE_CHECKER_H
#define __CVC4__EXPR__TYPE_CHECKER_H

namespace CVC4 {
namespace expr {

class TypeChecker {
public:

  static TypeNode computeType(NodeManager* nodeManager, TNode n, bool check = false)
    throw (TypeCheckingExceptionPrivate, AssertionException);

  static bool computeIsConst(NodeManager* nodeManager, TNode n)
    throw (AssertionException);

};/* class TypeChecker */

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__TYPE_CHECKER_H */
