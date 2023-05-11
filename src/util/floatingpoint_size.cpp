/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Martin Brain
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The class representing a floating-point format.
 */
#include "util/floatingpoint_size.h"

#include "base/check.h"

namespace cvc5::internal {

FloatingPointSize::FloatingPointSize(uint32_t exp_size, uint32_t sig_size)
    : d_exp_size(exp_size), d_sig_size(sig_size)
{
  Assert(validExponentSize(exp_size));
  Assert(validSignificandSize(sig_size));
}

FloatingPointSize::FloatingPointSize(const FloatingPointSize& old)
    : d_exp_size(old.d_exp_size), d_sig_size(old.d_sig_size)
{
  Assert(validExponentSize(d_exp_size));
  Assert(validSignificandSize(d_sig_size));
}

}  // namespace cvc5::internal
