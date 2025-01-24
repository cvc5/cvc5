/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of witness elimination node conversion
 */
#include "cvc5_private.h"

#ifndef CVC5__EXPR__ELIM_WITNESS_NODE_CONVERTER_H
#define CVC5__EXPR__ELIM_WITNESS_NODE_CONVERTER_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

/**
 * Node converter to eliminate all terms of kind WITNESS. Each term replaced
 * in this way is captured by an existential, which can be obtained by
 * getExistentials.
 */
class ElimWitnessNodeConverter : protected EnvObj, public NodeConverter
{
 public:
  /** Eliminate witness terms.*/
  ElimWitnessNodeConverter(Env& env);
  ~ElimWitnessNodeConverter() {}
  /**
   * Convert node n as described above during post-order traversal.
   */
  Node postConvert(Node n) override;
  /**
   * Get the existentials
   */
  const std::vector<Node>& getExistentials() const;

  /**
   * Get the normal form of a quantified formula for which we are introducing
   * a skolem variable based on eliminating a witness term.
   */
  virtual Node getNormalFormFor(const Node& q);

 private:
  /** The list of existentials introduced by eliminating witness */
  std::vector<Node> d_exists;
};

}  // namespace cvc5::internal

#endif
