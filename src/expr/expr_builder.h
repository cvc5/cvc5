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
#include <cstdlib>

#include "expr_manager.h"
#include "kind.h"
#include "util/Assert.h"

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

  void addChild(const Expr& e) { addChild(e.d_ev); }
  void addChild(ExprValue*);
  ExprBuilder& collapse();

  typedef ExprValue** ev_iterator;
  typedef ExprValue const** const_ev_iterator;

  ev_iterator ev_begin() {
    return d_children.u_arr;
  }

  ev_iterator ev_end() {
    return d_children.u_arr + d_nchildren;
  }

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

  /* TODO design: these modify ExprBuilder */
  ExprBuilder& operator!() { return notExpr(); }
  ExprBuilder& operator&&(const Expr& right) { return andExpr(right); }
  ExprBuilder& operator||(const Expr& right) { return orExpr(right);  }

  // "Stream" expression constructor syntax
  ExprBuilder& operator<<(const Kind& op);
  ExprBuilder& operator<<(const Expr& child);

  // For pushing sequences of children
  ExprBuilder& append(const std::vector<Expr>& children) { return append(children.begin(), children.end()); }
  ExprBuilder& append(Expr child) { return append(&child, (&child) + 1); }
  template <class Iterator> ExprBuilder& append(const Iterator& begin, const Iterator& end);

  operator Expr();// not const

  AndExprBuilder   operator&&(Expr);
  OrExprBuilder    operator||(Expr);
  PlusExprBuilder  operator+ (Expr);
  PlusExprBuilder  operator- (Expr);
  MultExprBuilder  operator* (Expr);

  friend class AndExprBuilder;
  friend class OrExprBuilder;
  friend class PlusExprBuilder;
  friend class MultExprBuilder;
};/* class ExprBuilder */

class AndExprBuilder {
  ExprBuilder d_eb;

public:

  AndExprBuilder(const ExprBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != AND) {
      d_eb.collapse();
      d_eb.d_kind = AND;
    }
  }

  AndExprBuilder&   operator&&(Expr);
  OrExprBuilder     operator||(Expr);

  operator ExprBuilder() { return d_eb; }

};/* class AndExprBuilder */

class OrExprBuilder {
  ExprBuilder d_eb;

public:

  OrExprBuilder(const ExprBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != OR) {
      d_eb.collapse();
      d_eb.d_kind = OR;
    }
  }

  AndExprBuilder    operator&&(Expr);
  OrExprBuilder&    operator||(Expr);

  operator ExprBuilder() { return d_eb; }

};/* class OrExprBuilder */

class PlusExprBuilder {
  ExprBuilder d_eb;

public:

  PlusExprBuilder(const ExprBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != PLUS) {
      d_eb.collapse();
      d_eb.d_kind = PLUS;
    }
  }

  PlusExprBuilder&  operator+(Expr);
  PlusExprBuilder&  operator-(Expr);
  MultExprBuilder   operator*(Expr);

  operator ExprBuilder() { return d_eb; }

};/* class PlusExprBuilder */

class MultExprBuilder {
  ExprBuilder d_eb;

public:

  MultExprBuilder(const ExprBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != MULT) {
      d_eb.collapse();
      d_eb.d_kind = MULT;
    }
  }

  PlusExprBuilder   operator+(Expr);
  PlusExprBuilder   operator-(Expr);
  MultExprBuilder&  operator*(Expr);

  operator ExprBuilder() { return d_eb; }

};/* class MultExprBuilder */

template <class Iterator>
inline ExprBuilder& ExprBuilder::append(const Iterator& begin, const Iterator& end) {
  for(Iterator i = begin; i != end; ++i)
    addChild(*i);
  return *this;
}

// not const
inline ExprBuilder::operator Expr() {
  ExprValue *ev;
  uint64_t hash;

  Assert(d_kind != UNDEFINED_KIND, "Can't make an expression of an undefined kind!");

  // variables are permitted to be duplicates (from POV of the expression manager)
  if(d_kind == VARIABLE) {
    ev = new ExprValue;
    hash = reinterpret_cast<uint64_t>(ev);
  } else {
    if(d_nchildren <= nchild_thresh) {
      hash = ExprValue::computeHash<ev_iterator>(d_kind, ev_begin(), ev_end());
      void *space = std::calloc(1, sizeof(ExprValue) + d_nchildren * sizeof(Expr));
      ev = new (space) ExprValue;
      size_t nc = 0;
      ev_iterator i = ev_begin();
      ev_iterator i_end = ev_end();
      for(; i != i_end; ++i) {
        // The expressions in the allocated children are all 0, so we must
        // construct it withouth using an assignment operator
        ev->d_children[nc++].assignExprValue(*i);
      }
    } else {
      hash = ExprValue::computeHash<std::vector<Expr>::const_iterator>(d_kind, d_children.u_vec->begin(), d_children.u_vec->end());
      void *space = std::calloc(1, sizeof(ExprValue) + d_nchildren * sizeof(Expr));
      ev = new (space) ExprValue;
      size_t nc = 0;
      for(std::vector<Expr>::iterator i = d_children.u_vec->begin(); i != d_children.u_vec->end(); ++i)
        ev->d_children[nc++] = Expr(*i);
    }
  }

  ev->d_nchildren = d_nchildren;
  ev->d_kind = d_kind;
  ev->d_id = ExprValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  Expr e(ev);

  return d_em->lookup(hash, e);
}

inline AndExprBuilder   ExprBuilder::operator&&(Expr e) {
  return AndExprBuilder(*this) && e;
}

inline OrExprBuilder    ExprBuilder::operator||(Expr e) {
  return OrExprBuilder(*this) || e;
}

inline PlusExprBuilder  ExprBuilder::operator+ (Expr e) {
  return PlusExprBuilder(*this) + e;
}

inline PlusExprBuilder  ExprBuilder::operator- (Expr e) {
  return PlusExprBuilder(*this) - e;
}

inline MultExprBuilder  ExprBuilder::operator* (Expr e) {
  return MultExprBuilder(*this) * e;
}

inline AndExprBuilder&  AndExprBuilder::operator&&(Expr e) {
  d_eb.append(e);
  return *this;
}

inline OrExprBuilder    AndExprBuilder::operator||(Expr e) {
  return OrExprBuilder(d_eb.collapse()) || e;
}

inline AndExprBuilder   OrExprBuilder::operator&&(Expr e) {
  return AndExprBuilder(d_eb.collapse()) && e;
}

inline OrExprBuilder&   OrExprBuilder::operator||(Expr e) {
  d_eb.append(e);
  return *this;
}

inline PlusExprBuilder& PlusExprBuilder::operator+(Expr e) {
  d_eb.append(e);
  return *this;
}

inline PlusExprBuilder& PlusExprBuilder::operator-(Expr e) {
  d_eb.append(e.negate());
  return *this;
}

inline MultExprBuilder  PlusExprBuilder::operator*(Expr e) {
  return MultExprBuilder(d_eb.collapse()) * e;
}

inline PlusExprBuilder  MultExprBuilder::operator+(Expr e) {
  return MultExprBuilder(d_eb.collapse()) + e;
}

inline PlusExprBuilder  MultExprBuilder::operator-(Expr e) {
  return MultExprBuilder(d_eb.collapse()) - e;
}

inline MultExprBuilder& MultExprBuilder::operator*(Expr e) {
  d_eb.append(e);
  return *this;
}


}/* CVC4 namespace */

#endif /* __CVC4__EXPR_BUILDER_H */
