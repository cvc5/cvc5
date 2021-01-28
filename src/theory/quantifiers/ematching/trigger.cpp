/*********************                                                        */
/*! \file trigger.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of trigger class
 **/

#include "theory/quantifiers/ematching/trigger.h"

#include "expr/skolem_manager.h"
#include "theory/quantifiers/ematching/candidate_generator.h"
#include "theory/quantifiers/ematching/ho_trigger.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi.h"
#include "theory/quantifiers/ematching/inst_match_generator_multi_linear.h"
#include "theory/quantifiers/ematching/inst_match_generator_simple.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace inst {

/** trigger class constructor */
Trigger::Trigger(QuantifiersEngine* qe, Node q, std::vector<Node>& nodes)
    : d_quantEngine(qe), d_quant(q)
{
  // We must ensure that the ground subterms of the trigger have been
  // preprocessed.
  Valuation& val = qe->getValuation();
  for (const Node& n : nodes)
  {
    Node np = ensureGroundTermPreprocessed(val, n, d_groundTerms);
    d_nodes.push_back(np);
  }
  if (Trace.isOn("trigger"))
  {
    quantifiers::QuantAttributes* qa = d_quantEngine->getQuantAttributes();
    Trace("trigger") << "Trigger for " << qa->quantToString(q) << ": "
                     << std::endl;
    for (const Node& n : d_nodes)
    {
      Trace("trigger") << "   " << n << std::endl;
    }
  }
  if( d_nodes.size()==1 ){
    if (TriggerTermInfo::isSimpleTrigger(d_nodes[0]))
    {
      d_mg = new InstMatchGeneratorSimple(q, d_nodes[0], qe);
      ++(qe->d_statistics.d_triggers);
    }else{
      d_mg = InstMatchGenerator::mkInstMatchGenerator(q, d_nodes[0], qe);
      ++(qe->d_statistics.d_simple_triggers);
    }
  }else{
    if( options::multiTriggerCache() ){
      d_mg = new InstMatchGeneratorMulti(q, d_nodes, qe);
    }else{
      d_mg = InstMatchGenerator::mkInstMatchGeneratorMulti(q, d_nodes, qe);
    }
    if (Trace.isOn("multi-trigger"))
    {
      Trace("multi-trigger") << "Trigger for " << q << ": " << std::endl;
      for (const Node& nc : d_nodes)
      {
        Trace("multi-trigger") << "   " << nc << std::endl;
      }
    }
    ++(qe->d_statistics.d_multi_triggers);
  }

  Trace("trigger-debug") << "Finished making trigger." << std::endl;
}

Trigger::~Trigger() {
  delete d_mg;
}

void Trigger::resetInstantiationRound(){
  d_mg->resetInstantiationRound( d_quantEngine );
}

void Trigger::reset( Node eqc ){
  d_mg->reset( eqc, d_quantEngine );
}

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
    eq::EqualityEngine* ee = d_quantEngine->getState().getEqualityEngine();
    for (const Node& gt : d_groundTerms)
    {
      if (!ee->hasTerm(gt))
      {
        SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
        Node k = sm->mkPurifySkolem(gt, "gt");
        Node eq = k.eqNode(gt);
        Trace("trigger-gt-lemma")
            << "Trigger: ground term purify lemma: " << eq << std::endl;
        d_quantEngine->addLemma(eq);
        gtAddedLemmas++;
      }
    }
  }
  uint64_t addedLemmas = d_mg->addInstantiations(d_quant, d_quantEngine, this);
  if (Debug.isOn("inst-trigger"))
  {
    if (addedLemmas > 0)
    {
      Debug("inst-trigger") << "Added " << addedLemmas
                            << " lemmas, trigger was " << d_nodes << std::endl;
    }
  }
  return gtAddedLemmas + addedLemmas;
}

bool Trigger::sendInstantiation(InstMatch& m)
{
  return d_quantEngine->getInstantiate()->addInstantiation(d_quant, m);
}

bool Trigger::mkTriggerTerms(Node q,
                             std::vector<Node>& nodes,
                             size_t nvars,
                             std::vector<Node>& trNodes)
{
  //only take nodes that contribute variables to the trigger when added
  std::vector< Node > temp;
  temp.insert( temp.begin(), nodes.begin(), nodes.end() );
  std::map< Node, bool > vars;
  std::map< Node, std::vector< Node > > patterns;
  size_t varCount = 0;
  std::map< Node, std::vector< Node > > varContains;
  for (const Node& pat : temp)
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(
        q, pat, varContains[pat]);
  }
  for (const Node& t : temp)
  {
    const std::vector<Node>& vct = varContains[t];
    bool foundVar = false;
    for (const Node& v : vct)
    {
      Assert(quantifiers::TermUtil::getInstConstAttr(v) == q);
      if( vars.find( v )==vars.end() ){
        varCount++;
        vars[ v ] = true;
        foundVar = true;
      }
    }
    if( foundVar ){
      trNodes.push_back(t);
      for (const Node& v : vct)
      {
        patterns[v].push_back(t);
      }
    }
    if (varCount == nvars)
    {
      break;
    }
  }
  if (varCount < nvars)
  {
    Trace("trigger-debug") << "Don't consider trigger since it does not contain specified number of variables." << std::endl;
    Trace("trigger-debug") << nodes << std::endl;
    //do not generate multi-trigger if it does not contain all variables
    return false;
  }
  // now, minimize the trigger
  for (size_t i = 0, tsize = trNodes.size(); i < tsize; i++)
  {
    bool keepPattern = false;
    Node n = trNodes[i];
    const std::vector<Node>& vcn = varContains[n];
    for (const Node& v : vcn)
    {
      if (patterns[v].size() == 1)
      {
        keepPattern = true;
        break;
      }
    }
    if (!keepPattern)
    {
      // remove from pattern vector
      for (const Node& v : vcn)
      {
        std::vector<Node>& pv = patterns[v];
        for (size_t k = 0, pvsize = pv.size(); k < pvsize; k++)
        {
          if (pv[k] == n)
          {
            pv.erase(pv.begin() + k, pv.begin() + k + 1);
            break;
          }
        }
      }
      // remove from trigger nodes
      trNodes.erase(trNodes.begin() + i, trNodes.begin() + i + 1);
      i--;
    }
  }
  return true;
}

Trigger* Trigger::mkTrigger(QuantifiersEngine* qe,
                            Node f,
                            std::vector<Node>& nodes,
                            bool keepAll,
                            int trOption,
                            size_t useNVars)
{
  std::vector< Node > trNodes;
  if( !keepAll ){
    size_t nvars = useNVars == 0 ? f[0].getNumChildren() : useNVars;
    if (!mkTriggerTerms(f, nodes, nvars, trNodes))
    {
      return nullptr;
    }
  }else{
    trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
  }

  //check for duplicate?
  if( trOption!=TR_MAKE_NEW ){
    Trigger* t = qe->getTriggerDatabase()->getTrigger( trNodes );
    if( t ){
      if( trOption==TR_GET_OLD ){
        //just return old trigger
        return t;
      }else{
        return nullptr;
      }
    }
  }

  // check if higher-order
  Trace("trigger-debug") << "Collect higher-order variable triggers..."
                         << std::endl;
  std::map<Node, std::vector<Node> > ho_apps;
  HigherOrderTrigger::collectHoVarApplyTerms(f, trNodes, ho_apps);
  Trace("trigger-debug") << "...got " << ho_apps.size()
                         << " higher-order applications." << std::endl;
  Trigger* t;
  if (!ho_apps.empty())
  {
    t = new HigherOrderTrigger(qe, f, trNodes, ho_apps);
  }
  else
  {
    t = new Trigger(qe, f, trNodes);
  }

  qe->getTriggerDatabase()->addTrigger( trNodes, t );
  return t;
}

Trigger* Trigger::mkTrigger(QuantifiersEngine* qe,
                            Node f,
                            Node n,
                            bool keepAll,
                            int trOption,
                            size_t useNVars)
{
  std::vector< Node > nodes;
  nodes.push_back( n );
  return mkTrigger(qe, f, nodes, keepAll, trOption, useNVars);
}

int Trigger::getActiveScore() {
  return d_mg->getActiveScore( d_quantEngine );
}

Node Trigger::ensureGroundTermPreprocessed(Valuation& val,
                                           Node n,
                                           std::vector<Node>& gts)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
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
      else if (!quantifiers::TermUtil::hasInstConstAttr(cur))
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

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
