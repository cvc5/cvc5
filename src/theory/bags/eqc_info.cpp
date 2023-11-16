/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equivalence class info for the theory of bags.
 */

#include "theory/bags/eqc_info.h"

#include "util/rational.h"

using namespace std;
using namespace cvc5::context;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

EqcInfo::EqcInfo(context::Context* c) : d_representative(c) {}

std::ostream& operator<<(std::ostream& out, const EqcInfo& ei)
{
  out << "(EqcInfo " << ei.d_representative.get() << ")";
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
