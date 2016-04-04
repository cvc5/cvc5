/*********************                                                        */
/*! \file predicate.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
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

#include "cvc4_public.h"

#ifndef __CVC4__PREDICATE_H
#define __CVC4__PREDICATE_H

#include "base/exception.h"

namespace CVC4 {

class Predicate;

std::ostream& operator<<(std::ostream& out, const Predicate& p) CVC4_PUBLIC;

struct CVC4_PUBLIC PredicateHashFunction {
  size_t operator()(const Predicate& p) const;
};/* class PredicateHashFunction */

}/* CVC4 namespace */


namespace CVC4 {
class CVC4_PUBLIC Expr;
}/* CVC4 namespace */


namespace CVC4 {
class CVC4_PUBLIC Predicate {
public:

  Predicate(const Expr& e) throw(IllegalArgumentException);
  Predicate(const Expr& e, const Expr& w) throw(IllegalArgumentException);

  Predicate(const Predicate& p);
  ~Predicate();
  Predicate& operator=(const Predicate& p);

  //operator Expr() const;

  const Expr& getExpression() const;
  const Expr& getWitness() const;

  bool operator==(const Predicate& p) const;

  friend std::ostream& CVC4::operator<<(std::ostream& out, const Predicate& p);
  friend size_t PredicateHashFunction::operator()(const Predicate& p) const;

private:
  Expr* d_predicate;
  Expr* d_witness;
};/* class Predicate */

}/* CVC4 namespace */

#endif /* __CVC4__PREDICATE_H */
