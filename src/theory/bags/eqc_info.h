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
  EqcInfo(context::Context* c);
  ~EqcInfo() {}
  /**
   * an equivalent class
   */
  context::CDO<Node> d_representative;
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
