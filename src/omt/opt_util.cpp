/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The file containing utilities used in solving optimization queries.
 */

#include "opt_util.h"

using namespace cvc5::omt;
using namespace cvc5;

Objective::Objective(TNode target, Type type)
    : d_target(target), d_type(type), d_result()
{
  if (isBVUnsigned())
  {
    Assert(d_target.getType().isBitVector());
  }
}

bool Objective::isMaximize() const
{
  return d_type == MAXIMIZE || d_type == BV_MAXIMIZE_UNSIGNED;
}

bool Objective::isMinimize() const
{
  return d_type == MINIMIZE || d_type == BV_MINIMIZE_UNSIGNED;
}

bool Objective::isBVUnsigned() const
{
  return isBV()
         && (d_type == BV_MAXIMIZE_UNSIGNED || d_type == BV_MINIMIZE_UNSIGNED);
}

bool Objective::isBVSigned() const
{
  return isBV() && (d_type == MAXIMIZE || d_type == MINIMIZE);
}

bool Objective::isBV() const { return d_target.getType().isBitVector(); }

TNode Objective::getTarget() const { return d_target; }

Objective::Type Objective::getType() const { return d_type; }

bool Objective::hasResult() const { return !(d_result.isNull()); }

TNode Objective::getResult() const { return d_result; }

void Objective::setResult(TNode res) const { d_result = res; }
