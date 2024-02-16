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
 * sygus_term_enumerator
 */

#include "expr/sygus_term_enumerator.h"

#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"

namespace cvc5::internal {

SygusTermEnumerator::SygusTermEnumerator(Env& env,
                                         const TypeNode& tn,
                                         bool enumShapes,
                                         bool enumAnyConstHoles,
                                         size_t numConstants)
    : d_internal(env,
                 nullptr,
                 nullptr,
                 nullptr,
                 enumShapes,
                 enumAnyConstHoles,
                 numConstants)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_enum = sm->mkDummySkolem("enum", tn);
  d_internal.initialize(d_enum);
  // ensure current is non-null
  if (d_internal.getCurrent().isNull())
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
  while (d_internal.increment())
  {
    if (!d_internal.getCurrent().isNull())
    {
      return true;
    }
  }
  return false;
}

bool SygusTermEnumerator::incrementPartial() { return d_internal.increment(); }

Node SygusTermEnumerator::getCurrent()
{
  const Node& c = d_internal.getCurrent();
  if (c.isNull())
  {
    return c;
  }
  return theory::datatypes::utils::sygusToBuiltin(c);
}

}  // namespace cvc5::internal
