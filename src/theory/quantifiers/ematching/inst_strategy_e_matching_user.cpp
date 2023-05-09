/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of e-matching instantiation strategies.
 */

#include "theory/quantifiers/ematching/inst_strategy_e_matching_user.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/ematching/trigger_database.h"
#include "theory/quantifiers/quantifiers_state.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::quantifiers::inst;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyUserPatterns::InstStrategyUserPatterns(
    Env& env,
    inst::TriggerDatabase& td,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : InstStrategy(env, td, qs, qim, qr, tr)
{
}
InstStrategyUserPatterns::~InstStrategyUserPatterns() {}

std::string InstStrategyUserPatterns::identify() const
{
  return std::string("UserPatterns");
}

void InstStrategyUserPatterns::processResetInstantiationRound(
    Theory::Effort effort)
{
  Trace("inst-alg-debug") << "reset user triggers" << std::endl;
  // reset triggers
  for (std::pair<const Node, std::vector<Trigger*> >& u : d_user_gen)
  {
    for (Trigger* t : u.second)
    {
      t->resetInstantiationRound();
      t->reset(Node::null());
    }
  }
  Trace("inst-alg-debug") << "done reset user triggers" << std::endl;
}

InstStrategyStatus InstStrategyUserPatterns::process(Node q,
                                                     Theory::Effort effort,
                                                     int e)
{
  if (e == 0)
  {
    return InstStrategyStatus::STATUS_UNFINISHED;
  }
  options::UserPatMode upm = getInstUserPatMode();
  int peffort = upm == options::UserPatMode::RESORT ? 2 : 1;
  if (e < peffort)
  {
    return InstStrategyStatus::STATUS_UNFINISHED;
  }
  if (e != peffort)
  {
    return InstStrategyStatus::STATUS_UNKNOWN;
  }
  d_counter[q]++;

  Trace("inst-alg") << "-> User-provided instantiate " << q << "..."
                    << std::endl;
  if (upm == options::UserPatMode::RESORT)
  {
    std::vector<std::vector<Node> >& ugw = d_user_gen_wait[q];
    for (size_t i = 0, usize = ugw.size(); i < usize; i++)
    {
      Trigger* t =
          d_td.mkTrigger(q, ugw[i], true, TriggerDatabase::TR_RETURN_NULL);
      if (t)
      {
        d_user_gen[q].push_back(t);
      }
    }
    ugw.clear();
  }

  std::vector<Trigger*>& ug = d_user_gen[q];
  for (Trigger* t : ug)
  {
    if (TraceIsOn("process-trigger"))
    {
      Trace("process-trigger") << "  Process (user) ";
      t->debugPrint("process-trigger");
      Trace("process-trigger") << "..." << std::endl;
    }
    unsigned numInst = t->addInstantiations();
    Trace("process-trigger")
        << "  Done, numInst = " << numInst << "." << std::endl;
    if (d_qstate.isInConflict())
    {
      // we are already in conflict
      break;
    }
  }
  return InstStrategyStatus::STATUS_UNKNOWN;
}

void InstStrategyUserPatterns::addUserPattern(Node q, Node pat)
{
  Assert(pat.getKind() == INST_PATTERN);
  // add to generators
  std::vector<Node> nodes;
  const Options& opts = d_env.getOptions();
  for (const Node& p : pat)
  {
    if (std::find(nodes.begin(), nodes.end(), p) != nodes.end())
    {
      // skip duplicate pattern term
      continue;
    }
    Node pat_use = PatternTermSelector::getIsUsableTrigger(opts, p, q);
    if (pat_use.isNull())
    {
      Trace("trigger-warn") << "User-provided trigger is not usable : " << pat
                            << " because of " << p << std::endl;
      return;
    }
    nodes.push_back(pat_use);
  }
  Trace("user-pat") << "Add user pattern: " << pat << " for " << q << std::endl;
  // check match option
  if (getInstUserPatMode() == options::UserPatMode::RESORT)
  {
    d_user_gen_wait[q].push_back(nodes);
    return;
  }
  Trigger* t = d_td.mkTrigger(q, nodes, true, TriggerDatabase::TR_MAKE_NEW);
  if (t)
  {
    d_user_gen[q].push_back(t);
  }
  else
  {
    Trace("trigger-warn") << "Failed to construct trigger : " << pat
                          << " due to variable mismatch" << std::endl;
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
