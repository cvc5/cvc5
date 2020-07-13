/*********************                                                        */
/*! \file expr_sequence.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The sequence data type.
 **/

#include "cvc4_public.h"

#ifndef CVC4__EXPR__EXPR_SEQUENCE_H
#define CVC4__EXPR__EXPR_SEQUENCE_H

#include <iosfwd>
#include <memory>
#include <vector>

namespace CVC4 {

// messy; Expr needs ExprSequence (because it's the payload of a
// CONSTANT-kinded expression), and ExprSequence needs Expr.
class Type;
class Expr;
class Sequence;

/** The CVC4 sequence class
 *
 * This data structure is the domain of values for the sequence type.
 */
class CVC4_PUBLIC ExprSequence
{
 public:
  /** constructors for ExprSequence
   *
   * Internally, a CVC4::ExprSequence is represented by a vector of Nodes
   * (d_seq), where each Node in this vector must be a constant.
   */
  ExprSequence(const Type& type, const std::vector<Expr>& seq);
  ~ExprSequence();

  ExprSequence(const ExprSequence& other);
  ExprSequence& operator=(const ExprSequence& other);

  bool operator==(const ExprSequence& es) const;
  bool operator!=(const ExprSequence& es) const;
  bool operator<(const ExprSequence& es) const;
  bool operator<=(const ExprSequence& es) const;
  bool operator>(const ExprSequence& es) const;
  bool operator>=(const ExprSequence& es) const;

  /** Get the element type of the sequence */
  const Type& getType() const;
  /** Get the underlying sequence */
  const Sequence& getSequence() const;

 private:
  /** The element type of the sequence */
  std::unique_ptr<Type> d_type;
  /** The data of the sequence */
  std::unique_ptr<Sequence> d_sequence;
}; /* class ExprSequence */

struct CVC4_PUBLIC ExprSequenceHashFunction
{
  size_t operator()(const ::CVC4::ExprSequence& s) const;
}; /* struct ExprSequenceHashFunction */

std::ostream& operator<<(std::ostream& os, const ExprSequence& s) CVC4_PUBLIC;

}  // namespace CVC4

#endif /* CVC4__EXPR__SEQUENCE_H */
