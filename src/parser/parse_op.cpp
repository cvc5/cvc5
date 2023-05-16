/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation for parsed operators.
 */

#include "parser/parse_op.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& os, const ParseOp& p)
{
  std::stringstream out;
  out << "(ParseOp";
  if (!p.d_expr.isNull())
  {
    out << " :expr " << p.d_expr;
  }
  if (p.d_kind != cvc5::NULL_TERM)
  {
    out << " :kind " << p.d_kind;
  }
  if (!p.d_name.empty())
  {
    out << " :name " << p.d_name;
  }
  if (!p.d_indices.empty())
  {
    out << " :indices [";
    bool first = true;
    for (uint32_t index : p.d_indices)
    {
      if (!first)
      {
        out << ", ";
      }
      first = false;
      out << index;
    }
    out << "]";
  }
  out << ")";
  return os << out.str();
}

}  // namespace cvc5
