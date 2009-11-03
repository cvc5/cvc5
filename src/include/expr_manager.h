/*********************                                           -*- C++ -*-  */
/** expr_manager.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXPR_MANAGER_H
#define __CVC4_EXPR_MANAGER_H

#include <vector>
#include "expr.h"
#include "kind.h"

namespace CVC4 {

class ExprManager {
  static __thread ExprManager* s_current;

public:
  static ExprManager* currentEM() { return s_current; }

  // general expression-builders
  Expr build(Kind kind);
  Expr build(Kind kind, Expr child1);
  Expr build(Kind kind, Expr child1, Expr child2);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8, Expr child9);
  Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8, Expr child9, Expr child10);
  // N-ary version
  Expr build(Kind kind, std::vector<Expr> children);

  // TODO: these use the current EM (but must be renamed)
  /*
  static Expr build(Kind kind)
  { currentEM()->build(kind); }
  static Expr build(Kind kind, Expr child1);
  { currentEM()->build(kind, child1); }
  static Expr build(Kind kind, Expr child1, Expr child2);
  { currentEM()->build(kind, child1, child2); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3);
  { currentEM()->build(kind, child1, child2, child3); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4);
  { currentEM()->build(kind, child1, child2, child3, child4); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5);
  { currentEM()->build(kind, child1, child2, child3, child4, child5); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6);
  { currentEM()->build(kind, child1, child2, child3, child4, child5, child6); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7);
  { currentEM()->build(kind, child1, child2, child3, child4, child5, child6, child7); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8);
  { currentEM()->build(kind, child1, child2, child3, child4, child5, child6, child7, child8); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8, Expr child9);
  { currentEM()->build(kind, child1, child2, child3, child4, child5, child6, child7, child8, child9); }
  static Expr build(Kind kind, Expr child1, Expr child2, Expr child3, Expr child4, Expr child5, Expr child6, Expr child7, Expr child8, Expr child9, Expr child10);
  { currentEM()->build(kind, child1, child2, child3, child4, child5, child6, child7, child8, child9, child10); }
  // N-ary version
  static Expr build(Kind kind, vector<Expr> children)
  { currentEM()->build(kind, children); }
  */

  // do we want a varargs one?  perhaps not..
};

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_MANAGER_H */
