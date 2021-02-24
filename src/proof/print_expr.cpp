/*********************                                                        */
/*! \file print_expr.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof print expression utility
 **/

#include "proof/proof_print_expr.h"

namespace CVC4 {
namespace proof {

PExprStream::PExprStream(std::vector<PExpr>& stream) : d_stream(stream) {
  NodeManager * nm = NodeManager::currentNM();
  // currently hardcoded for LFSC syntax
  d_tt = nm->mkBoundVar("tt", nm->booleanType());
  d_ff = nm->mkBoundVar("ff", nm->booleanType());
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

PExprStream& PExprStream::operator<<(bool b)
{
  d_stream.push_back(b ? d_tt : d_ff);
  return *this;
}

PExprStream& PExprStream::operator<<(PExpr p)
{
  d_stream.push_back(p);
  return *this;
}


}  // namespace proof
}  // namespace CVC4

#endif
