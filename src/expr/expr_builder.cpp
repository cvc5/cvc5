/*********************                                           -*- C++ -*-  */
/** expr_builder.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "core/expr_builder.h"
#include "core/expr_manager.h"
#include "core/expr_value.h"

using namespace std;

namespace CVC4 {

ExprBuilder::ExprBuilder() : d_em(ExprManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(0) {}

ExprBuilder::ExprBuilder(Kind k) : d_em(ExprManager::currentEM()), d_kind(k), d_used(false), d_nchildren(0) {}

ExprBuilder::ExprBuilder(const Expr& e) : d_em(ExprManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  ExprValue *v = e->inc();
  d_children.u_arr[0] = v;
}

ExprBuilder::ExprBuilder(const ExprBuilder& eb) : d_em(eb.d_em), d_kind(eb.d_kind), d_used(eb.d_used), d_nchildren(eb.d_nchildren) {
  cvc4assert(!d_used);

  if(d_nchildren > nchild_thresh) {
    d_children.u_vec = new vector<Expr>();
    d_children.u_vec->reserve(d_nchildren + 5);
    copy(eb.d_children.u_vec->begin(), eb.d_children.u_vec->end(), back_inserter(*d_children.u_vec));
  } else {
    iterator j = d_children.u_arr;
    for(iterator i = eb.d_children.u_arr; i != eb.d_children.u_arr + eb.d_nchildren; ++i, ++j)
      *j = i->inc();
  }
}

ExprBuilder::ExprBuilder(ExprManager* em) : d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(0) {
}

ExprBuilder::ExprBuilder(ExprManager* em, Kind k) : d_em(em), d_kind(k), d_used(false), d_nchildren(0) {
}

ExprBuilder::ExprBuilder(ExprManager* em, const Expr&) : d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  ExprValue *v = e->inc();
  d_children.u_arr[0] = v;
}

ExprBuilder::~ExprBuilder() {
  if(d_nchildren > nchild_thresh) {
    delete d_children.u_vec;
  } else {
    for(iterator i = d_children.u_arr; i != d_children.u_arr + d_nchildren; ++i) {
      *i
    }
  }
}

// Compound expression constructors
ExprBuilder& ExprBuilder::eqExpr(const Expr& right) {
  if(d_kind != UNDEFINED_KIND && d_kind != EQUAL)
    collapse();
  d_kind = EQUAL;
  return *this;
}

ExprBuilder& ExprBuilder::notExpr() {
}

// avoid double-negatives
ExprBuilder& ExprBuilder::negate() {
}

ExprBuilder& ExprBuilder::andExpr(const Expr& right) {
}

ExprBuilder& ExprBuilder::orExpr(const Expr& right) {
}

ExprBuilder& ExprBuilder::iteExpr(const Expr& thenpart, const Expr& elsepart) {
}

ExprBuilder& ExprBuilder::iffExpr(const Expr& right) {
}

ExprBuilder& ExprBuilder::impExpr(const Expr& right) {
}

ExprBuilder& ExprBuilder::xorExpr(const Expr& right) {
}

ExprBuilder& ExprBuilder::skolemExpr(int i) {
}

ExprBuilder& ExprBuilder::substExpr(const std::vector<Expr>& oldTerms,
                                    const std::vector<Expr>& newTerms) {
}

// "Stream" expression constructor syntax
ExprBuilder& ExprBuilder::operator<<(const Kind& op) {
}

ExprBuilder& ExprBuilder::operator<<(const Expr& child) {
}

template <class Iterator>
ExprBuilder& ExprBuilder::append(const Iterator& begin, const Iterator& end) {
}

void ExprBuilder::addChild(const Expr& e) {
  if(d_nchildren == nchild_thresh) {
    vector<Expr>* v = new vector<Expr>();
    v->reserve(nchild_thresh + 5);
    
  }
  return *this;
}

void ExprBuilder::collapse() {
  if(d_nchildren == nchild_thresh) {
    vector<Expr>* v = new vector<Expr>();
    v->reserve(nchild_thresh + 5);
    
  }
  return *this;
}

// not const
ExprBuilder::operator Expr() {
}

AndExprBuilder   ExprBuilder::operator&&(Expr) {
}

OrExprBuilder    ExprBuilder::operator||(Expr) {
}

PlusExprBuilder  ExprBuilder::operator+ (Expr) {
}

PlusExprBuilder  ExprBuilder::operator- (Expr) {
}

MultExprBuilder  ExprBuilder::operator* (Expr) {
}

} /* CVC4 namespace */
