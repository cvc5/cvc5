/******************************************************************************
 * Top contributors (to current version):
 *   Abdalrhman Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Reconstruct Type Info class implementation.
 */

#include "theory/quantifiers/sygus/rcons_type_info.h"

#include "expr/skolem_manager.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/sygus/rcons_obligation.h"
#include "theory/quantifiers/sygus_sampler.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void RConsTypeInfo::initialize(Env& env,
                               TermDbSygus* tds,
                               SygusStatistics& s,
                               TypeNode stn,
                               const std::vector<Node>& builtinVars)
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  // create a terms enumerator
  d_enumerators.push_back(
      std::make_unique<SygusEnumerator>(env, tds, nullptr, &s, false));
  d_enumerators[0]->initialize(sm->mkDummySkolem("sygus_rcons", stn));
  // create a patterns enumerator
  d_enumerators.push_back(
      std::make_unique<SygusEnumerator>(env, tds, nullptr, &s, true));
  d_enumerators[1]->initialize(sm->mkDummySkolem("sygus_rcons", stn));
  d_crd.reset(new CandidateRewriteDatabase(env, true, false, false));

  // since initial samples are not always useful for equivalence checks, set
  // their number to 0
  d_sygusSampler.reset(new SygusSampler(env));
  d_sygusSampler->initialize(stn, builtinVars, 0);
  d_crd->initialize(builtinVars, d_sygusSampler.get());
  // initialize current probability to be the initial probability.
  d_cp = d_p = env.getOptions().quantifiers.cegqiSingleInvReconstructP;
}

Node RConsTypeInfo::nextEnum()
{
  size_t i = Random::getRandom().pickWithProb(d_cp) ? 1 : 0;
  d_cp *= d_p;
  if (d_enumerators[i] == nullptr)
  {
    // the enumerator is already finished
    return Node::null();
  }
  Node sz = d_enumerators[i]->getCurrent();
  if (!d_enumerators[i]->increment())
  {
    Trace("sygus-rcons") << "no increment" << std::endl;
    // the enumerator is finished, clear it now
    d_enumerators[i] = nullptr;
  }

  Trace("sygus-rcons") << (sz == Node::null()
                               ? sz
                               : datatypes::utils::sygusToBuiltin(sz))
                       << std::endl;

  return sz;
}

Node RConsTypeInfo::addTerm(Node n)
{
  std::vector<Node> rewrites;
  return d_crd->addOrGetTerm(n, rewrites);
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
}  // namespace cvc5::internal
