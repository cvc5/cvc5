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
 * The weight symbol operator implementation
 */

#include "expr/weight_symbol.h"

namespace cvc5::internal {

WeightSymbol::WeightSymbol(const Node& weight, const Node& uf)
    : d_weight(weight), d_uf(uf)
{
}

const Node& WeightSymbol::getWeight() const { return d_weight; }

const Node& WeightSymbol::getUF() const { return d_uf; }

bool WeightSymbol::operator==(const WeightSymbol& cc) const
{
  return d_weight == cc.d_weight && d_uf == cc.d_uf;
}

std::ostream& operator<<(std::ostream& out, const WeightSymbol& cc)
{
  return out << cc.getWeight() << '(' << cc.getUF() << ')';
}

size_t WeightSymbolHashFunction::operator()(const WeightSymbol& cc) const
{
  return std::hash<Node>()(cc.getWeight()) * std::hash<Node>()(cc.getUF());
}

}  // namespace cvc5::internal
