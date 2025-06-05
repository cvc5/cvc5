/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_term_enumerator
 */

#include "expr/sygus_term_enumerator.h"

#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace cvc5::internal {

SygusTermEnumerator::SygusTermEnumerator(Env& env,
                                         const TypeNode& tn,
                                         SygusTermEnumeratorCallback* sec,
                                         bool enumShapes,
                                         bool enumAnyConstHoles,
                                         size_t numConstants)
    : d_internal(new theory::quantifiers::SygusEnumerator(env,
                                                          nullptr,
                                                          sec,
                                                          nullptr,
                                                          enumShapes,
                                                          enumAnyConstHoles,
                                                          numConstants))
{
  // Ensure we have computed the expanded definition form of all operators in
  // grammar, which is important if the grammar involves terms that have
  // user definitions in env.
  theory::datatypes::utils::computeExpandedDefinitionForms(env, tn);
  d_enum = NodeManager::mkDummySkolem("enum", tn);
  d_internal->initialize(d_enum);
  // ensure current is non-null
  if (d_internal->getCurrent().isNull())
  {
    if (!increment())
    {
      Warning() << "Could not initialize enumeration for " << tn
                << ", no values found";
    }
  }
}

bool SygusTermEnumerator::increment()
{
  while (d_internal->increment())
  {
    if (!d_internal->getCurrent().isNull())
    {
      return true;
    }
  }
  return false;
}

bool SygusTermEnumerator::incrementPartial() { return d_internal->increment(); }

Node SygusTermEnumerator::getCurrent()
{
  const Node& c = d_internal->getCurrent();
  if (c.isNull())
  {
    return c;
  }
  return theory::datatypes::utils::sygusToBuiltin(c);
}

}  // namespace cvc5::internal
