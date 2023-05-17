/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utilities for printing expressions in proofs
 */

#include "proof/print_expr.h"

namespace cvc5::internal {
namespace proof {

PExprStream::PExprStream(std::vector<PExpr>& stream, Node tt, Node ff)
    : d_stream(stream), d_tt(tt), d_ff(ff)
{
}

PExprStream& PExprStream::operator<<(const ProofNode* pn)
{
  d_stream.push_back(PExpr(pn));
  return *this;
}

PExprStream& PExprStream::operator<<(Node n)
{
  d_stream.push_back(PExpr(n));
  return *this;
}

PExprStream& PExprStream::operator<<(TypeNode tn)
{
  d_stream.push_back(PExpr(tn));
  return *this;
}

PExprStream& PExprStream::operator<<(bool b)
{
  Assert(!d_tt.isNull() && !d_ff.isNull());
  d_stream.push_back(b ? d_tt : d_ff);
  return *this;
}

PExprStream& PExprStream::operator<<(PExpr p)
{
  d_stream.push_back(p);
  return *this;
}

}  // namespace proof
}  // namespace cvc5::internal
