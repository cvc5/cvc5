/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of trigger class.
 */

#include "theory/quantifiers/ematching/trigger.h"

#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/quantifiers/ematching/candidate_generator.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi_linear.h"
#include "theory/quantifiers/ematching/inst_match_generator_simple.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/ematching/trigger_trie.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/valuation.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** trigger class constructor */
Trigger::Trigger(Env& env,
                 QuantifiersState& qs,
                 QuantifiersInferenceManager& qim,
                 QuantifiersRegistry& qr,
                 TermRegistry& tr,
                 Node q,
                 std::vector<Node>& nodes)
    : EnvObj(env),
      d_qstate(qs),
      d_qim(qim),
      d_qreg(qr),
      d_treg(tr),
      d_quant(q),
      d_instMatch(env, qs, tr, q)
{
  // set evaluator mode to "no entail"
  d_instMatch.setEvaluatorMode(ieval::TermEvaluatorMode::NO_ENTAIL);
  // We must ensure that the ground subterms of the trigger have been
  // preprocessed.
  Valuation& val = d_qstate.getValuation();
  for (const Node& n : nodes)
  {
    Node np = ensureGroundTermPreprocessed(val, n, d_groundTerms);
    d_nodes.push_back(np);
  }
  if (TraceIsOn("trigger"))
  {
    QuantAttributes& qa = d_qreg.getQuantAttributes();
    Trace("trigger") << "Trigger for " << qa.quantToString(q) << ": "
                     << std::endl;
    for (const Node& n : d_nodes)
    {
      Trace("trigger") << "   " << n << std::endl;
    }
  }
  std::vector<Node> extNodes;
  for (const Node& nt : d_nodes)
  {
    // note we must display the original form, so we go back to bound vars
    Node ns = d_qreg.substituteInstConstantsToBoundVariables(nt, q);
    extNodes.push_back(ns);
  }
  d_trNode = NodeManager::currentNM()->mkNode(SEXPR, extNodes);
  if (isOutputOn(OutputTag::TRIGGER))
  {
    QuantAttributes& qa = d_qreg.getQuantAttributes();
    output(OutputTag::TRIGGER) << "(trigger " << qa.quantToString(q) << " "
                               << d_trNode << ")" << std::endl;
  }
  QuantifiersStatistics& stats = qs.getStats();
  if( d_nodes.size()==1 ){
    if (TriggerTermInfo::isSimpleTrigger(d_nodes[0]))
    {
      d_mg = new InstMatchGeneratorSimple(env, this, q, d_nodes[0]);
      ++(stats.d_triggers);
    }else{
      d_mg = InstMatchGenerator::mkInstMatchGenerator(env, this, q, d_nodes[0]);
      ++(stats.d_simple_triggers);
    }
  }else{
    if (options().quantifiers.multiTriggerCache)
    {
      d_mg = new InstMatchGeneratorMulti(env, this, q, d_nodes);
    }
    else
    {
      d_mg =
          InstMatchGenerator::mkInstMatchGeneratorMulti(env, this, q, d_nodes);
    }
    if (TraceIsOn("multi-trigger"))
    {
      Trace("multi-trigger") << "Trigger for " << q << ": " << std::endl;
      for (const Node& nc : d_nodes)
      {
        Trace("multi-trigger") << "   " << nc << std::endl;
      }
    }
    ++(stats.d_multi_triggers);
  }

  Trace("trigger-debug") << "Finished making trigger." << std::endl;
}

Trigger::~Trigger() {
  delete d_mg;
}

void Trigger::resetInstantiationRound() { d_mg->resetInstantiationRound(); }

void Trigger::reset(Node eqc) { d_mg->reset(eqc); }

bool Trigger::isMultiTrigger() const { return d_nodes.size() > 1; }

Node Trigger::getInstPattern() const
{
  return NodeManager::currentNM()->mkNode( INST_PATTERN, d_nodes );
}

uint64_t Trigger::addInstantiations()
{
  uint64_t gtAddedLemmas = 0;
  if (!d_groundTerms.empty())
  {
    // for each ground term t that does not exist in the equality engine, we
    // add a purification lemma of the form (k = t).
    eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
    for (const Node& gt : d_groundTerms)
    {
      if (!ee->hasTerm(gt))
      {
        SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
        Node k = sm->mkPurifySkolem(gt);
        Node eq = k.eqNode(gt);
        Trace("trigger-gt-lemma")
            << "Trigger: ground term purify lemma: " << eq << std::endl;
        d_qim.addPendingLemma(eq, InferenceId::QUANTIFIERS_GT_PURIFY);
        gtAddedLemmas++;
      }
    }
  }
  uint64_t addedLemmas = d_mg->addInstantiations(d_instMatch);
  if (TraceIsOn("inst-trigger"))
  {
    if (addedLemmas > 0)
    {
      Trace("inst-trigger") << "Added " << addedLemmas
                            << " lemmas, trigger was " << d_nodes << std::endl;
    }
  }
  return gtAddedLemmas + addedLemmas;
}

bool Trigger::sendInstantiation(std::vector<Node>& m, InferenceId id)
{
  return d_qim.getInstantiate()->addInstantiation(d_quant, m, id, d_trNode);
}

int Trigger::getActiveScore() { return d_mg->getActiveScore(); }

Node Trigger::ensureGroundTermPreprocessed(Valuation& val,
                                           Node n,
                                           std::vector<Node>& gts)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (cur.getNumChildren() == 0)
      {
        visited[cur] = cur;
      }
      else if (!TermUtil::hasInstConstAttr(cur))
      {
        // cur has no INST_CONSTANT, thus is ground.
        Node vcur = val.getPreprocessedTerm(cur);
        gts.push_back(vcur);
        visited[cur] = vcur;
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

void Trigger::debugPrint(const char* c) const
{
  Trace(c) << "TRIGGER( " << d_nodes << " )" << std::endl;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
