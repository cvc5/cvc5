/*********************                                                        */
/*! \file predicate.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

Predicate::Predicate(Expr e, Expr w) throw(IllegalArgumentException) : d_predicate(e), d_witness(w) {
  CheckArgument(! e.isNull(), e, "Predicate cannot be null");
  CheckArgument(e.getType().isPredicate(), e, "Expression given is not predicate");
  CheckArgument(FunctionType(e.getType()).getArgTypes().size() == 1, e, "Expression given is not predicate of a single argument");
}

Predicate::operator Expr() const {
  return d_predicate;
}

bool Predicate::operator==(const Predicate& p) const {
  return d_predicate == p.d_predicate && d_witness == p.d_witness;
}

std::ostream&
operator<<(std::ostream& out, const Predicate& p) {
  out << p.d_predicate;
  if(! p.d_witness.isNull()) {
    out << " : " << p.d_witness;
  }
  return out;
}

size_t PredicateHashFunction::operator()(const Predicate& p) const {
  ExprHashFunction h;
  return h(p.d_witness) * 5039 + h(p.d_predicate);
}

}/* CVC4 namespace */
