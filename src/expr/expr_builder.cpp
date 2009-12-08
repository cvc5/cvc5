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

#include "expr_builder.h"
#include "expr_manager.h"
#include "expr_value.h"
#include "util/Assert.h"
#include "util/output.h"

using namespace std;

namespace CVC4 {

ExprBuilder::ExprBuilder() : d_em(ExprManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(0) {}

ExprBuilder::ExprBuilder(Kind k) : d_em(ExprManager::currentEM()), d_kind(k), d_used(false), d_nchildren(0) {}

ExprBuilder::ExprBuilder(const Expr& e) : d_em(ExprManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  ExprValue *v = e->inc();
  d_children.u_arr[0] = v;
}

ExprBuilder& ExprBuilder::reset(const ExprValue* ev) {
  this->~ExprBuilder();
  d_kind = Kind(ev->d_kind);
  d_used = false;
  d_nchildren = ev->d_nchildren;
  for(Expr::const_iterator i = ev->begin(); i != ev->end(); ++i)
    addChild(i->d_ev);
  return *this;
}

ExprBuilder::ExprBuilder(const ExprBuilder& eb) : d_em(eb.d_em), d_kind(eb.d_kind), d_used(eb.d_used), d_nchildren(eb.d_nchildren) {
  Assert( !d_used );

  if(d_nchildren > nchild_thresh) {
    d_children.u_vec = new vector<Expr>();
    d_children.u_vec->reserve(d_nchildren + 5);
    copy(eb.d_children.u_vec->begin(), eb.d_children.u_vec->end(), back_inserter(*d_children.u_vec));
  } else {
    ev_iterator j = d_children.u_arr;
    for(ExprValue* const* i = eb.d_children.u_arr; i != eb.d_children.u_arr + eb.d_nchildren; ++i, ++j)
      *j = (*i)->inc();
  }
}

ExprBuilder::ExprBuilder(ExprManager* em) : d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(0) {
}

ExprBuilder::ExprBuilder(ExprManager* em, Kind k) : d_em(em), d_kind(k), d_used(false), d_nchildren(0) {
}

ExprBuilder::ExprBuilder(ExprManager* em, const Expr& e) : d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  ExprValue *v = e->inc();
  d_children.u_arr[0] = v;
}

ExprBuilder::~ExprBuilder() {
  if(d_nchildren > nchild_thresh) {
    delete d_children.u_vec;
  } else {
    for(ev_iterator i = d_children.u_arr; i != d_children.u_arr + d_nchildren; ++i) {
      (*i)->dec();
    }
  }
}

// Compound expression constructors
ExprBuilder& ExprBuilder::eqExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != EQUAL )) {
    collapse();
    d_kind = EQUAL;
  }
  addChild(right);
  return *this;
}

ExprBuilder& ExprBuilder::notExpr() {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = NOT;
  return *this;
}

// avoid double-negatives
ExprBuilder& ExprBuilder::negate() {
  if(EXPECT_FALSE( d_kind == NOT ))
    return reset(d_children.u_arr[0]);
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = NOT;
  return *this;
}

ExprBuilder& ExprBuilder::andExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(d_kind != AND) {
    collapse();
    d_kind = AND;
  }
  addChild(right);
  return *this;
}

ExprBuilder& ExprBuilder::orExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != OR )) {
    collapse();
    d_kind = OR;
  }
  addChild(right);
  return *this;
}

ExprBuilder& ExprBuilder::iteExpr(const Expr& thenpart, const Expr& elsepart) {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = ITE;
  addChild(thenpart);
  addChild(elsepart);
  return *this;
}

ExprBuilder& ExprBuilder::iffExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != IFF )) {
    collapse();
    d_kind = IFF;
  }
  addChild(right);
  return *this;
}

ExprBuilder& ExprBuilder::impExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = IMPLIES;
  addChild(right);
  return *this;
}

ExprBuilder& ExprBuilder::xorExpr(const Expr& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != XOR )) {
    collapse();
    d_kind = XOR;
  }
  addChild(right);
  return *this;
}

// "Stream" expression constructor syntax
ExprBuilder& ExprBuilder::operator<<(const Kind& op) {
  d_kind = op;
  return *this;
}

ExprBuilder& ExprBuilder::operator<<(const Expr& child) {
  addChild(child);
  return *this;
}

void ExprBuilder::addChild(const Expr& e) {
  Debug("expr") << "adding child E " << e << endl;
  if(d_nchildren == nchild_thresh) {
    Debug("expr") << "reached thresh " << nchild_thresh << ", copying" << endl;
    vector<Expr>* v = new vector<Expr>();
    v->reserve(nchild_thresh + 5);
    for(ExprValue** i = d_children.u_arr; i != d_children.u_arr + nchild_thresh; ++i) {
      v->push_back(Expr(*i));
      (*i)->dec();
    }
    v->push_back(e);
    d_children.u_vec = v;
    ++d_nchildren;
  } else if(d_nchildren > nchild_thresh) {
    Debug("expr") << "over thresh " << d_nchildren << " > " << nchild_thresh << endl;
    d_children.u_vec->push_back(e);
    ++d_nchildren;
  } else {
    Debug("expr") << "under thresh " << d_nchildren << " < " << nchild_thresh << endl;
    ExprValue *ev = e.d_ev;
    d_children.u_arr[d_nchildren] = ev;
    ev->inc();
    ++d_nchildren;
  }
}

void ExprBuilder::addChild(ExprValue* ev) {
  Debug("expr") << "adding child ev " << ev << endl;
  if(d_nchildren == nchild_thresh) {
    Debug("expr") << "reached thresh " << nchild_thresh << ", copying" << endl;
    vector<Expr>* v = new vector<Expr>();
    v->reserve(nchild_thresh + 5);
    for(ExprValue** i = d_children.u_arr; i != d_children.u_arr + nchild_thresh; ++i) {
      v->push_back(Expr(*i));
      (*i)->dec();
    }
    v->push_back(Expr(ev));
    d_children.u_vec = v;
    ++d_nchildren;
  } else if(d_nchildren > nchild_thresh) {
    Debug("expr") << "over thresh " << d_nchildren << " > " << nchild_thresh << endl;
    d_children.u_vec->push_back(Expr(ev));
    ++d_nchildren;
  } else {
    Debug("expr") << "under thresh " << d_nchildren << " < " << nchild_thresh << endl;
    d_children.u_arr[d_nchildren] = ev;
    ev->inc();
    ++d_nchildren;
  }
}

ExprBuilder& ExprBuilder::collapse() {
  if(d_nchildren == nchild_thresh) {
    vector<Expr>* v = new vector<Expr>();
    v->reserve(nchild_thresh + 5);
    //
    Unreachable();// unimplemented
  }
  return *this;
}

}/* CVC4 namespace */
