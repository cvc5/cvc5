/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The weight symbol operator interface
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__WEIGHT_SYMBOL_H
#define CVC5__EXPR__WEIGHT_SYMBOL_H

#include "node.h"

namespace cvc5::internal {

/**
 * The payload of the WEIGHT_SYMBOL_OP operator. It pairs a SyGuS weight
 * attribute with the function-to-synthesize whose accumulated term weight is
 * being constrained, as introduced by `(_ <weight> <function>)` in the SyGuS
 * IF 2.1 standard.
 */
class WeightSymbol
{
 public:
  /**
   * Construct a weight symbol.
   * @param weight The weight attribute (an integer variable carrying a
   * SygusWeightAttribute).
   * @param uf The function-to-synthesize whose term weight is constrained.
   */
  WeightSymbol(const Node& weight, const Node& uf);
  /** Get the weight attribute. */
  const Node& getWeight() const;
  /** Get the function-to-synthesize. */
  const Node& getUF() const;
  bool operator==(const WeightSymbol& ws) const;

 private:
  /** The weight attribute. */
  Node d_weight;
  /** The function-to-synthesize whose term weight is constrained. */
  Node d_uf;
};

std::ostream& operator<<(std::ostream& out, const WeightSymbol& ws);

struct WeightSymbolHashFunction
{
  size_t operator()(const WeightSymbol& ws) const;
};

}  // namespace cvc5::internal

#endif
