/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * A weight symbol, handled in the cardinality extension of the UF
 * solver, used for finite model finding.
 */
class WeightSymbol
{
 public:
  /**
   * Constructs a cardinality constraint of the specified type, which should
   * be an uninterpreted sort.
   */
  WeightSymbol(const Node& weight, const Node& uf);
  /** Get the type of the cardinality constraint */
  const Node& getWeight() const;
  /** Get the upper bound value of the cardinality constraint */
  const Node& getUF() const;
  bool operator==(const WeightSymbol& cc) const;

 private:
  /** The type that the cardinality constraint is for */
  Node d_weight;
  /** The upper bound on the cardinality of the above type */
  Node d_uf;
};

std::ostream& operator<<(std::ostream& out, const WeightSymbol& cc);

struct WeightSymbolHashFunction
{
  size_t operator()(const WeightSymbol& cc) const;
};

}  // namespace cvc5::internal

#endif
