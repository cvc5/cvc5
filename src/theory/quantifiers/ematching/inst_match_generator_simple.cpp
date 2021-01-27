/*********************                                                        */
/*! \file inst_match_generator_simple.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief  simple inst match generator class
 **/
#include "theory/quantifiers/ematching/inst_match_generator_simple.h"

#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace inst {

InstMatchGeneratorSimple::InstMatchGeneratorSimple(Node q,
                                                   Node pat,
                                                   QuantifiersEngine* qe)
    : d_quant(q), d_match_pattern(pat)
{
  if (d_match_pattern.getKind() == NOT)
  {
    d_match_pattern = d_match_pattern[0];
    d_pol = false;
  }
  else
  {
    d_pol = true;
  }
  if (d_match_pattern.getKind() == EQUAL)
  {
    d_eqc = d_match_pattern[1];
    d_match_pattern = d_match_pattern[0];
    Assert(!quantifiers::TermUtil::hasInstConstAttr(d_eqc));
  }
  Assert(TriggerTermInfo::isSimpleTrigger(d_match_pattern));
  for (size_t i = 0, nchild = d_match_pattern.getNumChildren(); i < nchild; i++)
  {
    if (d_match_pattern[i].getKind() == INST_CONSTANT)
    {
      if (!options::cegqi()
          || quantifiers::TermUtil::getInstConstAttr(d_match_pattern[i]) == q)
      {
        d_var_num[i] = d_match_pattern[i].getAttribute(InstVarNumAttribute());
      }
      else
      {
        d_var_num[i] = -1;
      }
    }
    d_match_pattern_arg_types.push_back(d_match_pattern[i].getType());
  }
  d_op = qe->getTermDatabase()->getMatchOperator(d_match_pattern);
}

void InstMatchGeneratorSimple::resetInstantiationRound(QuantifiersEngine* qe) {}
uint64_t InstMatchGeneratorSimple::addInstantiations(Node q,
                                                     QuantifiersEngine* qe,
                                                     Trigger* tparent)
{
  uint64_t addedLemmas = 0;
  TNodeTrie* tat;
  if (d_eqc.isNull())
  {
    tat = qe->getTermDatabase()->getTermArgTrie(d_op);
  }
  else
  {
    if (d_pol)
    {
      tat = qe->getTermDatabase()->getTermArgTrie(d_eqc, d_op);
    }
    else
    {
      // iterate over all classes except r
      tat = qe->getTermDatabase()->getTermArgTrie(Node::null(), d_op);
      if (tat && !qe->inConflict())
      {
        Node r = qe->getEqualityQuery()->getRepresentative(d_eqc);
        for (std::pair<const TNode, TNodeTrie>& t : tat->d_data)
        {
          if (t.first != r)
          {
            InstMatch m(q);
            addInstantiations(m, qe, addedLemmas, 0, &(t.second));
            if (qe->inConflict())
            {
              break;
            }
          }
        }
      }
      tat = nullptr;
    }
  }
  Debug("simple-trigger-debug")
      << "Adding instantiations based on " << tat << " from " << d_op << " "
      << d_eqc << std::endl;
  if (tat && !qe->inConflict())
  {
    InstMatch m(q);
    addInstantiations(m, qe, addedLemmas, 0, tat);
  }
  return addedLemmas;
}

void InstMatchGeneratorSimple::addInstantiations(InstMatch& m,
                                                 QuantifiersEngine* qe,
                                                 uint64_t& addedLemmas,
                                                 size_t argIndex,
                                                 TNodeTrie* tat)
{
  Debug("simple-trigger-debug")
      << "Add inst " << argIndex << " " << d_match_pattern << std::endl;
  if (argIndex == d_match_pattern.getNumChildren())
  {
    Assert(!tat->d_data.empty());
    TNode t = tat->getData();
    Debug("simple-trigger") << "Actual term is " << t << std::endl;
    // convert to actual used terms
    for (const std::pair<unsigned, int>& v : d_var_num)
    {
      if (v.second >= 0)
      {
        Assert(v.first < t.getNumChildren());
        Debug("simple-trigger")
            << "...set " << v.second << " " << t[v.first] << std::endl;
        m.setValue(v.second, t[v.first]);
      }
    }
    // we do not need the trigger parent for simple triggers (no post-processing
    // required)
    if (qe->getInstantiate()->addInstantiation(d_quant, m))
    {
      addedLemmas++;
      Debug("simple-trigger") << "-> Produced instantiation " << m << std::endl;
    }
    return;
  }
  if (d_match_pattern[argIndex].getKind() == INST_CONSTANT)
  {
    int v = d_var_num[argIndex];
    if (v != -1)
    {
      for (std::pair<const TNode, TNodeTrie>& tt : tat->d_data)
      {
        Node t = tt.first;
        Node prev = m.get(v);
        // using representatives, just check if equal
        Assert(t.getType().isComparableTo(d_match_pattern_arg_types[argIndex]));
        if (prev.isNull() || prev == t)
        {
          m.setValue(v, t);
          addInstantiations(m, qe, addedLemmas, argIndex + 1, &(tt.second));
          m.setValue(v, prev);
          if (qe->inConflict())
          {
            break;
          }
        }
      }
      return;
    }
    // inst constant from another quantified formula, treat as ground term?
  }
  Node r = qe->getEqualityQuery()->getRepresentative(d_match_pattern[argIndex]);
  std::map<TNode, TNodeTrie>::iterator it = tat->d_data.find(r);
  if (it != tat->d_data.end())
  {
    addInstantiations(m, qe, addedLemmas, argIndex + 1, &(it->second));
  }
}

int InstMatchGeneratorSimple::getActiveScore(QuantifiersEngine* qe)
{
  Node f = qe->getTermDatabase()->getMatchOperator(d_match_pattern);
  size_t ngt = qe->getTermDatabase()->getNumGroundTerms(f);
  Trace("trigger-active-sel-debug") << "Number of ground terms for (simple) "
                                    << f << " is " << ngt << std::endl;
  return static_cast<int>(ngt);
}

}  // namespace inst
}  // namespace theory
}  // namespace CVC4
