/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reconstruct Type Info class implementation.
 */

#include "theory/quantifiers/sygus/rcons_type_info.h"

#include "expr/skolem_manager.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/rcons_obligation.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

void RConsTypeInfo::initialize(TermDbSygus* tds,
                               SygusStatistics& s,
                               TypeNode stn,
                               const std::vector<Node>& builtinVars)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();

  d_enumerator.reset(new SygusEnumerator(tds, nullptr, s, true));
  d_enumerator->initialize(sm->mkDummySkolem("sygus_rcons", stn));
  d_crd.reset(new CandidateRewriteDatabase(true, false, true, false));
  // since initial samples are not always useful for equivalence checks, set
  // their number to 0
  d_sygusSampler.initialize(stn, builtinVars, 0);
  d_crd->initialize(builtinVars, &d_sygusSampler);
}

Node RConsTypeInfo::nextEnum()
{
  if (!d_enumerator->increment())
  {
    Trace("sygus-rcons") << "no increment" << std::endl;
    return Node::null();
  }

  Node sz = d_enumerator->getCurrent();

  Trace("sygus-rcons") << (sz == Node::null()
                               ? sz
                               : datatypes::utils::sygusToBuiltin(sz))
                       << std::endl;

  return sz;
}

Node RConsTypeInfo::addTerm(Node n)
{
  std::stringstream out;
  return d_crd->addTerm(n, false, out);
}

void RConsTypeInfo::setBuiltinToOb(Node t, RConsObligation* ob)
{
  d_ob.emplace(t, ob);
}

RConsObligation* RConsTypeInfo::builtinToOb(Node t)
{
  auto it = d_ob.find(t);
  if (it != d_ob.cend())
  {
    return it->second;
  }
  return nullptr;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
