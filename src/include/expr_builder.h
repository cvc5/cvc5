/*********************                                           -*- C++ -*-  */
/** expr_builder.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4_EXPR_BUILDER_H
#define __CVC4_EXPR_BUILDER_H

#include <vector>
#include "expr_manager.h"
#include "kind.h"

namespace CVC4 {

class AndExprBuilder;
class OrExprBuilder;
class PlusExprBuilder;
class MinusExprBuilder;
class MultExprBuilder;

class ExprBuilder {
  ExprManager* d_em;

  Kind d_kind;

  // TODO: store some flags here and install into attribute map when
  // the expr is created?  (we'd have to do that since we don't know
  // it's hash code yet)

  // initially false, when you extract the Expr this is set and you can't
  // extract another
  bool d_used;

  unsigned d_nchildren;
  union {
    ExprValue*         u_arr[10];
    std::vector<Expr>* u_vec;
  } d_children;

public:

  ExprBuilder();
  ExprBuilder(const Expr&);
  ExprBuilder(const ExprBuilder&);

  // Compound expression constructors
  ExprBuilder& eqExpr(const Expr& right);
  ExprBuilder& notExpr();
  ExprBuilder& negate(); // avoid double-negatives
  ExprBuilder& andExpr(const Expr& right);
  ExprBuilder& orExpr(const Expr& right);
  ExprBuilder& iteExpr(const Expr& thenpart, const Expr& elsepart);
  ExprBuilder& iffExpr(const Expr& right);
  ExprBuilder& impExpr(const Expr& right);
  ExprBuilder& xorExpr(const Expr& right);
  ExprBuilder& skolemExpr(int i);
  ExprBuilder& substExpr(const std::vector<Expr>& oldTerms,
                         const std::vector<Expr>& newTerms);
  /*
  ExprBuilder& substExpr(const ExprHashMap<Expr>& oldToNew);
  */

  /* TODO design: these modify ExprBuilder */
  ExprBuilder& operator!() { return notExpr(); }
  ExprBuilder& operator&&(const Expr& right) { return andExpr(right); }
  ExprBuilder& operator||(const Expr& right) { return orExpr(right);  }

  // "Stream" expression constructor syntax
  ExprBuilder& operator<<(const Kind& op);
  ExprBuilder& operator<<(const Expr& child);

  // For pushing sequences of children
  ExprBuilder& append(const std::vector<Expr>& children) { return append(children.begin(), children.end()); }
  template <class Iterator> ExprBuilder& append(const Iterator& begin, const Iterator& end);

  operator Expr();// not const

  AndExprBuilder   operator&&(Expr);
  OrExprBuilder    operator||(Expr);
  PlusExprBuilder  operator+ (Expr);
  PlusExprBuilder  operator- (Expr);
  MultExprBuilder  operator* (Expr);

};/* class ExprBuilder */

class AndExprBuilder {
  ExprManager* d_em;

public:

  AndExprBuilder&   operator&&(Expr);
  OrExprBuilder     operator||(Expr);

  operator ExprBuilder();

};/* class AndExprBuilder */

class OrExprBuilder {
  ExprManager* d_em;

public:

  AndExprBuilder    operator&&(Expr);
  OrExprBuilder&    operator||(Expr);

  operator ExprBuilder();

};/* class OrExprBuilder */

class PlusExprBuilder {
  ExprManager* d_em;

public:

  PlusExprBuilder&  operator+(Expr);
  PlusExprBuilder&  operator-(Expr);
  MultExprBuilder   operator*(Expr);

  operator ExprBuilder();

};/* class PlusExprBuilder */

class MultExprBuilder {
  ExprManager* d_em;

public:

  PlusExprBuilder   operator+(Expr);
  PlusExprBuilder   operator-(Expr);
  MultExprBuilder&  operator*(Expr);

  operator ExprBuilder();

};/* class MultExprBuilder */

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_BUILDER_H */
