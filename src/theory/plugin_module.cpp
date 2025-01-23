/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A theory engine module based on a user plugin.
 */

#include "theory/plugin_module.h"

#include "expr/skolem_manager.h"
#include "smt/env.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {
namespace theory {

PluginModule::PluginModule(Env& env, TheoryEngine* theoryEngine, Plugin* p)
    : TheoryEngineModule(env, theoryEngine, "Plugin::" + p->getName()),
      d_plugin(p)
{
}

void PluginModule::check(Theory::Effort e)
{
  // ignore the effort level?
  std::vector<Node> lems = d_plugin->check();
  // returned vector is taken as lemmas
  for (const Node& lem : lems)
  {
    Assert(lem.getType().isBoolean());
    // must apply top level substitutions here, since if this lemma was
    // sent externally, it may not have taken into account the internal
    // substitutions.
    Node slem = d_env.getTopLevelSubstitutions().apply(lem);
    // send the lemma
    d_out.lemma(slem, InferenceId::PLUGIN_LEMMA);
  }
}

void PluginModule::notifyLemma(TNode n,
                               InferenceId id,
                               LemmaProperty p,
                               const std::vector<Node>& skAsserts,
                               const std::vector<Node>& sks)
{
  // must take original form as a way to remove internal symbols from the lemma
  notifyLemmaInternal(n);
  // skolem lemmas are also included
  for (const Node& kn : skAsserts)
  {
    notifyLemmaInternal(kn);
  }
  // currently ignores the other fields, e.g. property and sks
}

void PluginModule::notifyLemmaInternal(const Node& n)
{
  Node ns = d_env.getSharableFormula(n);
  if (!ns.isNull())
  {
    d_plugin->notifyTheoryLemma(ns);
  }
}

}  // namespace theory
}  // namespace cvc5::internal
