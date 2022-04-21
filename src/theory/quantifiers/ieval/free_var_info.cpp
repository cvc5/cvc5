/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per free variable in CCFV.
 */

#include "theory/quantifiers/ieval/free_var_info.h"

#include "theory/quantifiers/ieval/state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

FreeVarInfo::FreeVarInfo(context::Context* c)
    : d_finalTerms(c), d_quantList(c), d_quantIndex(c, 0)
{
}


}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
