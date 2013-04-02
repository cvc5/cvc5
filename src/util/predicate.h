/*********************                                                        */
/*! \file predicate.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of predicates for predicate subtyping
 **
 ** Simple class to represent predicates for predicate subtyping.
 ** Instances of this class are carried as the payload of
 ** the CONSTANT-metakinded SUBTYPE_TYPE types.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PREDICATE_H
#define __CVC4__PREDICATE_H

#include "util/exception.h"

namespace CVC4 {

class Predicate;

std::ostream& operator<<(std::ostream& out, const Predicate& p) CVC4_PUBLIC;

struct CVC4_PUBLIC PredicateHashFunction {
  size_t operator()(const Predicate& p) const;
};/* class PredicateHashFunction */

}/* CVC4 namespace */

#include "expr/expr.h"

namespace CVC4 {

class CVC4_PUBLIC Predicate {

  Expr d_predicate;
  Expr d_witness;

public:

  Predicate(Expr e, Expr w = Expr()) throw(IllegalArgumentException);

  operator Expr() const;

  bool operator==(const Predicate& p) const;

  friend std::ostream& operator<<(std::ostream& out, const Predicate& p);
  friend size_t PredicateHashFunction::operator()(const Predicate& p) const;

};/* class Predicate */

}/* CVC4 namespace */

#endif /* __CVC4__PREDICATE_H */
