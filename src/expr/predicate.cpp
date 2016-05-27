/*********************                                                        */
/*! \file predicate.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of predicates for predicate subtyping
 **
 ** Simple class to represent predicates for predicate subtyping.
 ** Instances of this class are carried as the payload of
 ** the CONSTANT-metakinded SUBTYPE_TYPE types.
 **/
#include "expr/predicate.h"

#include "base/cvc4_assert.h"
#include "expr/expr.h"


using namespace std;

namespace CVC4 {

Predicate::Predicate(const Predicate& p)
    : d_predicate(new Expr(p.getExpression()))
    , d_witness(new Expr(p.getWitness()))
{}

Predicate::Predicate(const Expr& e) throw(IllegalArgumentException)
    : d_predicate(new Expr(e))
    , d_witness(new Expr())
{
  PrettyCheckArgument(! e.isNull(), e, "Predicate cannot be null");
  PrettyCheckArgument(e.getType().isPredicate(), e,
                      "Expression given is not predicate");
  PrettyCheckArgument(FunctionType(e.getType()).getArgTypes().size() == 1, e,
                      "Expression given is not predicate of a single argument");
}

Predicate::Predicate(const Expr& e, const Expr& w)
    throw(IllegalArgumentException)
    : d_predicate(new Expr(e))
    , d_witness(new Expr(w))
{
  PrettyCheckArgument(! e.isNull(), e, "Predicate cannot be null");
  PrettyCheckArgument(e.getType().isPredicate(), e,
                      "Expression given is not predicate");
  PrettyCheckArgument(FunctionType(e.getType()).getArgTypes().size() == 1, e,
                      "Expression given is not predicate of a single argument");
}

Predicate::~Predicate() {
  delete d_predicate;
  delete d_witness;
}

Predicate& Predicate::operator=(const Predicate& p){
  (*d_predicate) = p.getExpression();
  (*d_witness) = p.getWitness();
  return *this;
}


// Predicate::operator Expr() const {
//   return d_predicate;
// }

const Expr& Predicate::getExpression() const {
  return *d_predicate;
}

const Expr& Predicate::getWitness() const {
  return *d_witness;
}

bool Predicate::operator==(const Predicate& p) const {
  return getExpression() == p.getExpression() &&
      getWitness() == p.getWitness();
}

std::ostream& operator<<(std::ostream& out, const Predicate& p) {
  out << p.getExpression();
  const Expr& witness = p.getWitness();
  if(! witness.isNull()) {
    out << " : " << witness;
  }
  return out;
}

size_t PredicateHashFunction::operator()(const Predicate& p) const {
  ExprHashFunction h;
  return h(p.getWitness()) * 5039 + h(p.getExpression());
}

}/* CVC4 namespace */
