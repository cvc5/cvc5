/*********************                                           -*- C++ -*-  */
/** expr_manager.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4__EXPR_MANAGER_H
#define __CVC4__EXPR_MANAGER_H

#include <vector>
#include <map>

#include "expr/expr.h"
#include "kind.h"

namespace CVC4 {

namespace expr {
  class ExprBuilder;
}/* CVC4::expr namespace */

class CVC4_PUBLIC ExprManager {
  static __thread ExprManager* s_current;

  friend class CVC4::ExprBuilder;

  typedef std::map<uint64_t, std::vector<Expr> > hash_t;
  hash_t d_hash;

  Expr lookup(uint64_t hash, const Expr& e);

public:
  static ExprManager* currentEM() { return s_current; }

  // general expression-builders
  Expr mkExpr(Kind kind);
  Expr mkExpr(Kind kind, const Expr& child1);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3, const Expr& child4);
  Expr mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3, const Expr& child4, const Expr& child5);
  // N-ary version
  Expr mkExpr(Kind kind, std::vector<Expr> children);

  // variables are special, because duplicates are permitted
  Expr mkVar();

  // TODO: these use the current EM (but must be renamed)
  /*
  static Expr mkExpr(Kind kind)
  { currentEM()->mkExpr(kind); }
  static Expr mkExpr(Kind kind, Expr child1);
  { currentEM()->mkExpr(kind, child1); }
  static Expr mkExpr(Kind kind, Expr child1, Expr child2);
  { currentEM()->mkExpr(kind, child1, child2); }
  static Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3);
  { currentEM()->mkExpr(kind, child1, child2, child3); }
  static Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4);
  { currentEM()->mkExpr(kind, child1, child2, child3, child4); }
  static Expr mkExpr(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5);
  { currentEM()->mkExpr(kind, child1, child2, child3, child4, child5); }
  */

  // do we want a varargs one?  perhaps not..
};

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
