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

#ifndef __CVC4__EXPR_BUILDER_H
#define __CVC4__EXPR_BUILDER_H

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

  // initially false, when you extract the Expr this is set and you can't
  // extract another
  bool d_used;

  static const unsigned nchild_thresh = 10;

  unsigned d_nchildren;
  union {
    ExprValue*         u_arr[nchild_thresh];
    std::vector<Expr>* u_vec;
  } d_children;

  void addChild(const Expr&);
  void addChild(ExprValue*);
  void collapse();

  typedef ExprValue** ev_iterator;
  typedef ExprValue const** const_ev_iterator;

  ExprBuilder& reset(const ExprValue*);

public:

  ExprBuilder();
  ExprBuilder(Kind k);
  ExprBuilder(const Expr&);
  ExprBuilder(const ExprBuilder&);

  ExprBuilder(ExprManager*);
  ExprBuilder(ExprManager*, Kind k);
  ExprBuilder(ExprManager*, const Expr&);
  ExprBuilder(ExprManager*, const ExprBuilder&);

  ~ExprBuilder();

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

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_BUILDER_H */
