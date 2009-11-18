/*********************                                           -*- C++ -*-  */
/** expr_manager.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Expression manager implementation.
 **/

#include "expr_builder.h"
#include "expr_manager.h"
#include "cvc4_expr.h"

namespace CVC4 {

__thread ExprManager* ExprManager::s_current = 0;

// general expression-builders

Expr ExprManager::mkExpr(Kind kind) {
  return ExprBuilder(this, kind);
}

Expr ExprManager::mkExpr(Kind kind, Expr child1) {
  return ExprBuilder(this, kind) << child1;
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2) {
  return ExprBuilder(this, kind) << child1 << child2;
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3) {
  return ExprBuilder(this, kind) << child1 << child2 << child3;
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4) {
  return ExprBuilder(this, kind) << child1 << child2 << child3 << child4;
}

Expr ExprManager::mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5) {
  return ExprBuilder(this, kind) << child1 << child2 << child3 << child4 << child5;
}

// N-ary version
Expr ExprManager::mkExpr(Kind kind, std::vector<Expr> children) {
  return ExprBuilder(this, kind).append(children);
}

} /* CVC4 namespace */
