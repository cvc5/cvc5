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
#include "expr/expr.h"

namespace CVC4 {

__thread ExprManager* ExprManager::s_current = 0;

Expr ExprManager::lookup(uint64_t hash, const Expr& e) {
  Assert(this != NULL, "Woops, we have a bad expression manager!");
  hash_t::iterator i = d_hash.find(hash);
  if(i == d_hash.end()) {
    // insert
    std::vector<Expr> v;
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  } else {
    for(std::vector<Expr>::iterator j = i->second.begin(); j != i->second.end(); ++j) {
      if(e.getKind() != j->getKind())
        continue;

      if(e.numChildren() != j->numChildren())
        continue;

      Expr::const_iterator c1 = e.begin();
      Expr::iterator c2 = j->begin();
      for(; c1 != e.end() && c2 != j->end(); ++c1, ++c2) {
        if(c1->d_ev != c2->d_ev)
          break;
      }

      if(c1 != e.end() || c2 != j->end())
        continue;

      return *j;
    }
    // didn't find it, insert
    std::vector<Expr> v;
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  }
}

// general expression-builders

Expr ExprManager::mkExpr(Kind kind) {
  return ExprBuilder(this, kind);
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  return ExprBuilder(this, kind) << child1;
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  return ExprBuilder(this, kind) << child1 << child2;
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3) {
  return ExprBuilder(this, kind) << child1 << child2 << child3;
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3, const Expr& child4) {
  return ExprBuilder(this, kind) << child1 << child2 << child3 << child4;
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2, const Expr& child3, const Expr& child4, const Expr& child5) {
  return ExprBuilder(this, kind) << child1 << child2 << child3 << child4 << child5;
}

// N-ary version
Expr ExprManager::mkExpr(Kind kind, std::vector<Expr> children) {
  return ExprBuilder(this, kind).append(children);
}

Expr ExprManager::mkVar() {
  return ExprBuilder(this, VARIABLE);
}

}/* CVC4 namespace */
