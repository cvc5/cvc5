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
 * sygus_enumerator
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
    : d_internal(
        env, nullptr, nullptr, nullptr, enumShapes, enumAnyConstHoles, numConstants)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  d_enum = sm->mkDummySkolem("enum", tn);
  d_internal.initialize(d_enum);
  d_current = getCurrent();
}

Node SygusTermEnumerator::getNext()
{
  if (!d_current.isNull())
  {
    const Node& ret = d_current;
    d_current = Node::null();
    return ret;
  }
  while (d_internal.increment())
  {
    const Node& c = getCurrent();
    if (!c.isNull())
    {
      d_current = Node::null();
      return c;
    }
  }
  return Node::null();
}

bool SygusTermEnumerator::increment() { return d_internal.increment(); }

Node SygusTermEnumerator::getCurrent()
{
  d_current = getSygusToBuiltin(d_internal.getCurrent());
  return d_current;
}

Node SygusTermEnumerator::getSygusToBuiltin(const Node& n)
{
  return theory::datatypes::utils::sygusToBuiltin(n);
}

}  // namespace cvc5::internal
