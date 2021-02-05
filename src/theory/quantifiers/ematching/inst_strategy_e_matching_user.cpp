/*********************                                                        */
/*! \file inst_strategy_e_matching_user.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of e matching instantiation strategies
 **/

#include "theory/quantifiers/ematching/inst_strategy_e_matching_user.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;
using namespace CVC4::theory::inst;

namespace CVC4 {
namespace theory {
namespace quantifiers {

InstStrategyUserPatterns::InstStrategyUserPatterns(
    QuantifiersEngine* ie,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim)
    : InstStrategy(ie, qs, qim)
{
}
InstStrategyUserPatterns::~InstStrategyUserPatterns() {}

size_t InstStrategyUserPatterns::getNumUserGenerators(Node q) const
{
  std::map<Node, std::vector<inst::Trigger*> >::const_iterator it =
      d_user_gen.find(q);
  if (it == d_user_gen.end())
  {
    return 0;
  }
  return it->second.size();
}

inst::Trigger* InstStrategyUserPatterns::getUserGenerator(Node q,
                                                          size_t i) const
{
  std::map<Node, std::vector<inst::Trigger*> >::const_iterator it =
      d_user_gen.find(q);
  if (it == d_user_gen.end())
  {
    return nullptr;
  }
  Assert(i < it->second.size());
  return it->second[i];
}

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
  options::UserPatMode upm = d_quantEngine->getInstUserPatMode();
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
      Trigger* t = Trigger::mkTrigger(
          d_quantEngine, d_qim, q, ugw[i], true, Trigger::TR_RETURN_NULL);
      if (t)
      {
        d_user_gen[q].push_back(t);
      }
    }
    ugw.clear();
  }

  std::vector<inst::Trigger*>& ug = d_user_gen[q];
  for (Trigger* t : ug)
  {
    if (Trace.isOn("process-trigger"))
    {
      Trace("process-trigger") << "  Process (user) ";
      t->debugPrint("process-trigger");
      Trace("process-trigger") << "..." << std::endl;
    }
    unsigned numInst = t->addInstantiations();
    Trace("process-trigger")
        << "  Done, numInst = " << numInst << "." << std::endl;
    d_quantEngine->d_statistics.d_instantiations_user_patterns += numInst;
    if (t->isMultiTrigger())
    {
      d_quantEngine->d_statistics.d_multi_trigger_instantiations += numInst;
    }
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
  for (const Node& p : pat)
  {
    Node pat_use = PatternTermSelector::getIsUsableTrigger(p, q);
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
  if (d_quantEngine->getInstUserPatMode() == options::UserPatMode::RESORT)
  {
    d_user_gen_wait[q].push_back(nodes);
    return;
  }
  Trigger* t = Trigger::mkTrigger(
      d_quantEngine, d_qim, q, nodes, true, Trigger::TR_MAKE_NEW);
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
}  // namespace CVC4
