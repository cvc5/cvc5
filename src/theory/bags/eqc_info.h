/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Equivalence class info for the theory of bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__EQC_INFO_H
#define CVC5__THEORY__BAGS__EQC_INFO_H

#include <map>

#include "context/cdo.h"
#include "context/context.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

/**
 * SAT-context-dependent information about an equivalence class. This
 * information is updated eagerly as assertions are processed by the theory of
 * bags at standard effort.
 */
class EqcInfo
{
 public:
  EqcInfo(context::Context* c, Node eqc);
  ~EqcInfo() {}
  /** add prefix constant
   *
   * This informs this equivalence class info that a term t in its
   * equivalence class has a constant lower bound (if isLowerBound is true) or
   * an upper bound (if isLowerBound is false).
   * The constant c (if non-null) is the value of that constant,
   * if it has been computed already.
   *
   * If this method returns a non-null node ret, then ret is a conjunction
   * corresponding to a conflict that holds in the current context.
   * TODO: why do we need the parameter t here.
   */
  Node addBoundConst(Node t, Node c, bool isLowerBound);

  /** the bounded term */
  // TODO: delete this field if it is not absolutely necessary
  Node d_term;
  /**
   * If this is an integer equivalence class, this is the lower bound
   * of the value of this equivalence class.
   */
  context::CDO<Node> d_firstBound;
  /** same as above, for integer upper bounds. */
  context::CDO<Node> d_secondBound;
};

/**
 * Writes an inference info to a stream.
 *
 * @param out The stream to write to
 * @param ei The equivalence class info to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, const EqcInfo& ei);

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__EQC_INFO_H */
