/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for sequence unit
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__STRINGS__SEQ_UNIT_OP_H
#define CVC5__THEORY__STRINGS__SEQ_UNIT_OP_H

#include <memory>

namespace cvc5 {

class TypeNode;

/**
 * The class is an operator for kind SEQ_UNIT used to construct sequences
 * of length one. It specifies the type of the single element especially when it
 * is a constant. e.g. the type of rational 1 is Int, however (seq.unit
 * (seq_unit_op Real) 1) is of type (Seq Real), not (Seq Int). Note that the
 * type passed to the constructor is the element's type, not the sequence type.
 */
class SeqUnitOp
{
 public:
  SeqUnitOp(const TypeNode& elementType);
  SeqUnitOp(const SeqUnitOp& op);

  /** return the type of the current object */
  const TypeNode& getType() const;

  bool operator==(const SeqUnitOp& op) const;

 private:
  SeqUnitOp();
  /** a pointer to the type of the singleton element */
  std::unique_ptr<TypeNode> d_type;
}; /* class SeqUnitOp */

std::ostream& operator<<(std::ostream& out, const SeqUnitOp& op);

/**
 * Hash function for the SeqUnitOp objects.
 */
struct SeqUnitOpHashFunction
{
  size_t operator()(const SeqUnitOp& op) const;
}; /* struct SeqUnitOpHashFunction */

}  // namespace cvc5

#endif /* CVC5__THEORY__STRINGS__SEQ_UNIT_OP_H */
