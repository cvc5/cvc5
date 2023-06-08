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
 * Info per free variable in instantiation evaluator.
 */

#include "theory/quantifiers/ieval/free_var_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

FreeVarInfo::FreeVarInfo(context::Context* c) : d_quantList(c) {}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
