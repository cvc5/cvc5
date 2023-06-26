/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Multi inst match generator class.
 */

#include "theory/quantifiers/ematching/inst_match_generator_multi.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"
#include "theory/uf/equality_engine_iterator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstMatchGeneratorMulti::InstMatchGeneratorMulti(Env& env,
                                                 Trigger* tparent,
                                                 Node q,
                                                 std::vector<Node>& pats)
    : IMGenerator(env, tparent), d_quant(q)
{
  Trace("multi-trigger-cache")
      << "Making smart multi-trigger for " << q << std::endl;
  std::map<Node, std::vector<Node> > var_contains;
  for (const Node& pat : pats)
  {
    TermUtil::computeInstConstContainsForQuant(q, pat, var_contains[pat]);
  }
  // convert to indicies
  for (std::pair<const Node, std::vector<Node> >& vc : var_contains)
  {
    Trace("multi-trigger-cache") << "Pattern " << vc.first << " contains: ";
    for (const Node& vcn : vc.second)
    {
      Trace("multi-trigger-cache") << vcn << " ";
      uint64_t index = vcn.getAttribute(InstVarNumAttribute());
      d_var_contains[vc.first].push_back(index);
      d_var_to_node[index].push_back(vc.first);
    }
    Trace("multi-trigger-cache") << std::endl;
  }
  size_t patsSize = pats.size();
  for (size_t i = 0; i < patsSize; i++)
  {
    Node n = pats[i];
    // make the match generator
    InstMatchGenerator* img =
        InstMatchGenerator::mkInstMatchGenerator(env, tparent, q, n);
    img->setActiveAdd(false);
    d_children.push_back(img);
    // compute unique/shared variables
    std::vector<uint64_t> unique_vars;
    std::map<uint64_t, bool> shared_vars;
    unsigned numSharedVars = 0;
    std::vector<uint64_t>& vctn = d_var_contains[n];
    for (size_t j = 0, vctnSize = vctn.size(); j < vctnSize; j++)
    {
      if (d_var_to_node[vctn[j]].size() == 1)
      {
        Trace("multi-trigger-cache")
            << "Var " << vctn[j] << " is unique to " << pats[i] << std::endl;
        unique_vars.push_back(vctn[j]);
      }
      else
      {
        shared_vars[vctn[j]] = true;
        numSharedVars++;
      }
    }
    // we use the latest shared variables, then unique variables
    std::vector<uint64_t> vars;
    size_t index = i == 0 ? pats.size() - 1 : (i - 1);
    while (numSharedVars > 0 && index != i)
    {
      for (std::pair<const uint64_t, bool>& sv : shared_vars)
      {
        if (sv.second)
        {
          std::vector<uint64_t>& vctni = d_var_contains[pats[index]];
          if (std::find(vctni.begin(), vctni.end(), sv.first) != vctni.end())
          {
            vars.push_back(sv.first);
            shared_vars[sv.first] = false;
            numSharedVars--;
          }
        }
      }
      index = index == 0 ? patsSize - 1 : (index - 1);
    }
    vars.insert(vars.end(), unique_vars.begin(), unique_vars.end());
    if (TraceIsOn("multi-trigger-cache"))
    {
      Trace("multi-trigger-cache") << "   Index[" << i << "]: ";
      for (uint64_t v : vars)
      {
        Trace("multi-trigger-cache") << v << " ";
      }
      Trace("multi-trigger-cache") << std::endl;
    }
    // make ordered inst match trie
    d_imtio[i] = new InstMatchTrie::ImtIndexOrder;
    d_imtio[i]->d_order.insert(
        d_imtio[i]->d_order.begin(), vars.begin(), vars.end());
    d_children_trie.push_back(InstMatchTrieOrdered(d_imtio[i]));
  }
}

InstMatchGeneratorMulti::~InstMatchGeneratorMulti()
{
  for (size_t i = 0, csize = d_children.size(); i < csize; i++)
  {
    delete d_children[i];
  }
  for (std::pair<const size_t, InstMatchTrie::ImtIndexOrder*>& i : d_imtio)
  {
    delete i.second;
  }
}

/** reset instantiation round (call this whenever equivalence classes have
 * changed) */
void InstMatchGeneratorMulti::resetInstantiationRound()
{
  for (InstMatchGenerator* c : d_children)
  {
    c->resetInstantiationRound();
  }
}

/** reset, eqc is the equivalence class to search in (any if eqc=null) */
bool InstMatchGeneratorMulti::reset(Node eqc)
{
  for (InstMatchGenerator* c : d_children)
  {
    if (!c->reset(eqc))
    {
      // do not return false here
    }
  }
  return true;
}

uint64_t InstMatchGeneratorMulti::addInstantiations(InstMatch& m)
{
  uint64_t addedLemmas = 0;
  Trace("multi-trigger-cache") << "Process smart multi trigger" << std::endl;
  for (size_t i = 0, csize = d_children.size(); i < csize; i++)
  {
    Trace("multi-trigger-cache") << "Calculate matches " << i << std::endl;
    std::vector<InstMatch> newMatches;
    while (d_children[i]->getNextMatch(m) > 0)
    {
      Trace("multi-trigger-cache2")
          << "...processing new match, #lemmas = " << addedLemmas << std::endl;
      processNewMatch(m, i, addedLemmas);
      if (d_qstate.isInConflict())
      {
        return addedLemmas;
      }
      m.resetAll();
    }
  }
  return addedLemmas;
}

void InstMatchGeneratorMulti::processNewMatch(InstMatch& m,
                                              size_t fromChildIndex,
                                              uint64_t& addedLemmas)
{
  // see if these produce new matches
  d_children_trie[fromChildIndex].addInstMatch(d_quant, m.get());
  // possibly only do the following if we know that new matches will be
  // produced? the issue is that instantiations are filtered in quantifiers
  // engine, and so there is no guarentee that
  // we can safely skip the following lines, even when we have already produced
  // this match.
  Trace("multi-trigger-cache-debug")
      << "Child " << fromChildIndex << " produced match " << m << std::endl;
  // process new instantiations
  size_t childIndex = (fromChildIndex + 1) % d_children.size();
  processNewInstantiations(m,
                           addedLemmas,
                           d_children_trie[childIndex].getTrie(),
                           0,
                           childIndex,
                           fromChildIndex,
                           true);
}

void InstMatchGeneratorMulti::processNewInstantiations(InstMatch& m,
                                                       uint64_t& addedLemmas,
                                                       InstMatchTrie* tr,
                                                       size_t trieIndex,
                                                       size_t childIndex,
                                                       size_t endChildIndex,
                                                       bool modEq)
{
  Assert(!d_qstate.isInConflict());
  if (childIndex == endChildIndex)
  {
    // m is an instantiation
    std::vector<Node> mc = m.get();
    if (sendInstantiation(mc, InferenceId::QUANTIFIERS_INST_E_MATCHING_MT))
    {
      addedLemmas++;
      Trace("multi-trigger-cache-debug")
          << "-> Produced instantiation " << m << std::endl;
    }
    return;
  }
  InstMatchTrie::ImtIndexOrder* iio = d_children_trie[childIndex].getOrdering();
  if (trieIndex < iio->d_order.size())
  {
    size_t curr_index = iio->d_order[trieIndex];
    Node n = m.get(curr_index);
    QuantifiersState& qs = d_qstate;
    if (n.isNull())
    {
      // add to InstMatch
      for (std::pair<const Node, InstMatchTrie>& d : tr->d_data)
      {
        // try to set
        if (!m.set(curr_index, d.first))
        {
          continue;
        }
        processNewInstantiations(m,
                                 addedLemmas,
                                 &(d.second),
                                 trieIndex + 1,
                                 childIndex,
                                 endChildIndex,
                                 modEq);
        m.reset(curr_index);
        if (d_qstate.isInConflict())
        {
          break;
        }
      }
    }
    // shared and set variable, try to merge
    std::map<Node, InstMatchTrie>::iterator it = tr->d_data.find(n);
    if (it != tr->d_data.end())
    {
      processNewInstantiations(m,
                               addedLemmas,
                               &(it->second),
                               trieIndex + 1,
                               childIndex,
                               endChildIndex,
                               modEq);
    }
    if (!modEq)
    {
      return;
    }
    // check modulo equality for other possible instantiations
    if (!qs.hasTerm(n))
    {
      return;
    }
    for (std::pair<const Node, InstMatchTrie>& d : tr->d_data)
    {
      if (d.first != n && qs.areEqual(d.first, n))
      {
        processNewInstantiations(m,
                                 addedLemmas,
                                 &(d.second),
                                 trieIndex + 1,
                                 childIndex,
                                 endChildIndex,
                                 modEq);
        if (d_qstate.isInConflict())
        {
          break;
        }
      }
    }
  }
  else
  {
    size_t newChildIndex = (childIndex + 1) % d_children.size();
    processNewInstantiations(m,
                             addedLemmas,
                             d_children_trie[newChildIndex].getTrie(),
                             0,
                             newChildIndex,
                             endChildIndex,
                             modEq);
  }
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
