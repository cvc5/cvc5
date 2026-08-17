/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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

bool WeightSymbol::operator==(const WeightSymbol& ws) const
{
  return d_weight == ws.d_weight && d_uf == ws.d_uf;
}

std::ostream& operator<<(std::ostream& out, const WeightSymbol& ws)
{
  return out << ws.getWeight() << '(' << ws.getUF() << ')';
}

size_t WeightSymbolHashFunction::operator()(const WeightSymbol& ws) const
{
  return std::hash<Node>()(ws.getWeight()) * std::hash<Node>()(ws.getUF());
}

}  // namespace cvc5::internal
