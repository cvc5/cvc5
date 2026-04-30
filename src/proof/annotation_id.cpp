/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof annotation identifier enumeration.
 */

#include "proof/annotation_id.h"

#include "proof/proof_checker.h"
#include "util/rational.h"

namespace cvc5::internal {

const char* toString(AnnotationId id)
{
  switch (id)
  {
    case AnnotationId::NONE: return "NONE";
    case AnnotationId::THEORY_LEMMA: return "THEORY_LEMMA";
    default: return "AnnotationId::Unknown";
  }
}

std::ostream& operator<<(std::ostream& out, AnnotationId id)
{
  out << toString(id);
  return out;
}

Node mkAnnotationId(NodeManager* nm, AnnotationId id)
{
  return nm->mkConstInt(Rational(static_cast<uint32_t>(id)));
}

bool getAnnotationId(TNode n, AnnotationId& id)
{
  uint32_t index;
  if (!ProofRuleChecker::getUInt32(n, index))
  {
    return false;
  }
  id = static_cast<AnnotationId>(index);
  return true;
}

}  // namespace cvc5::internal
