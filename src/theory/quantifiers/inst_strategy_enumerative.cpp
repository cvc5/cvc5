/*********************                                                        */
/*! \file inst_strategy_enumerative.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of an enumerative instantiation strategy.
 **/

#include "theory/quantifiers/inst_strategy_enumerative.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

namespace CVC4 {

using namespace kind;
using namespace context;

namespace theory {

using namespace inst;

namespace quantifiers {

InstStrategyEnum::InstStrategyEnum(QuantifiersEngine* qe)
    : QuantifiersModule(qe)
{
}

bool InstStrategyEnum::needsCheck(Theory::Effort e)
{
  if (options::fullSaturateInterleave())
  {
    if (d_quantEngine->getInstWhenNeedsCheck(e))
    {
      return true;
    }
  }
  if (options::fullSaturateQuant())
  {
    if (e >= Theory::EFFORT_LAST_CALL)
    {
      return true;
    }
  }
  return false;
}

void InstStrategyEnum::reset_round(Theory::Effort e) {}
void InstStrategyEnum::check(Theory::Effort e, unsigned quant_e)
{
  bool doCheck = false;
  bool fullEffort = false;
  if (options::fullSaturateInterleave())
  {
    // we only add when interleaved with other strategies
    doCheck = quant_e == QuantifiersEngine::QEFFORT_STANDARD
              && d_quantEngine->hasAddedLemma();
  }
  if (options::fullSaturateQuant() && !doCheck)
  {
    doCheck = quant_e == QuantifiersEngine::QEFFORT_LAST_CALL;
    fullEffort = !d_quantEngine->hasAddedLemma();
  }
  if (doCheck)
  {
    double clSet = 0;
    if (Trace.isOn("fs-engine"))
    {
      clSet = double(clock()) / double(CLOCKS_PER_SEC);
      Trace("fs-engine") << "---Full Saturation Round, effort = " << e << "---"
                         << std::endl;
    }
    int addedLemmas = 0;
    for (unsigned i = 0;
         i < d_quantEngine->getModel()->getNumAssertedQuantifiers();
         i++)
    {
      Node q = d_quantEngine->getModel()->getAssertedQuantifier(i, true);
      if (d_quantEngine->hasOwnership(q, this)
          && d_quantEngine->getModel()->isQuantifierActive(q))
      {
        if (process(q, fullEffort))
        {
          // added lemma
          addedLemmas++;
          if (d_quantEngine->inConflict())
          {
            break;
          }
        }
      }
    }
    if (Trace.isOn("fs-engine"))
    {
      Trace("fs-engine") << "Added lemmas = " << addedLemmas << std::endl;
      double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
      Trace("fs-engine") << "Finished full saturation engine, time = "
                         << (clSet2 - clSet) << std::endl;
    }
  }
}

bool InstStrategyEnum::process(Node f, bool fullEffort)
{
  // ignore if constant true (rare case of non-standard quantifier whose body is
  // rewritten to true)
  if (f[1].isConst() && f[1].getConst<bool>())
  {
    return false;
  }
  // first, try from relevant domain
  RelevantDomain* rd = d_quantEngine->getRelevantDomain();
  unsigned rstart = options::fullSaturateQuantRd() ? 0 : 1;
  unsigned rend = fullEffort ? 1 : rstart;
  for (unsigned r = rstart; r <= rend; r++)
  {
    if (rd || r > 0)
    {
      if (r == 0)
      {
        Trace("inst-alg") << "-> Relevant domain instantiate " << f << "..."
                          << std::endl;
      }
      else
      {
        Trace("inst-alg") << "-> Ground term instantiate " << f << "..."
                          << std::endl;
      }
      AlwaysAssert(rd);
      Trace("inst-alg-debug") << "Compute relevant domain..." << std::endl;
      rd->compute();
      Trace("inst-alg-debug") << "...finished" << std::endl;
      unsigned final_max_i = 0;
      std::vector<unsigned> maxs;
      std::vector<bool> max_zero;
      bool has_zero = false;
      std::map<TypeNode, std::vector<Node> > term_db_list;
      std::vector<TypeNode> ftypes;
      // iterate over substitutions for variables
      for (unsigned i = 0; i < f[0].getNumChildren(); i++)
      {
        TypeNode tn = f[0][i].getType();
        ftypes.push_back(tn);
        unsigned ts;
        if (r == 0)
        {
          ts = rd->getRDomain(f, i)->d_terms.size();
        }
        else
        {
          ts = d_quantEngine->getTermDatabase()->getNumTypeGroundTerms(tn);
          std::map<TypeNode, std::vector<Node> >::iterator ittd =
              term_db_list.find(tn);
          if (ittd == term_db_list.end())
          {
            std::map<Node, Node> reps_found;
            for (unsigned j = 0; j < ts; j++)
            {
              Node gt = d_quantEngine->getTermDatabase()->getTypeGroundTerm(
                  ftypes[i], j);
              if (!options::cbqi()
                  || !quantifiers::TermUtil::hasInstConstAttr(gt))
              {
                Node r =
                    d_quantEngine->getEqualityQuery()->getRepresentative(gt);
                if (reps_found.find(r) == reps_found.end())
                {
                  reps_found[r] = gt;
                  term_db_list[tn].push_back(gt);
                }
              }
            }
            ts = term_db_list[tn].size();
          }
          else
          {
            ts = ittd->second.size();
          }
        }
        // consider a default value if at full effort
        max_zero.push_back(fullEffort && ts == 0);
        ts = (fullEffort && ts == 0) ? 1 : ts;
        Trace("inst-alg-rd") << "Variable " << i << " has " << ts
                             << " in relevant domain." << std::endl;
        if (ts == 0)
        {
          has_zero = true;
          break;
        }
        else
        {
          maxs.push_back(ts);
          if (ts > final_max_i)
          {
            final_max_i = ts;
          }
        }
      }
      if (!has_zero)
      {
        Trace("inst-alg-rd") << "Will do " << final_max_i
                             << " stages of instantiation." << std::endl;
        unsigned max_i = 0;
        bool success;
        while (max_i <= final_max_i)
        {
          Trace("inst-alg-rd") << "Try stage " << max_i << "..." << std::endl;
          std::vector<unsigned> childIndex;
          int index = 0;
          do
          {
            while (index >= 0 && index < (int)f[0].getNumChildren())
            {
              if (index == (int)childIndex.size())
              {
                childIndex.push_back(-1);
              }
              else
              {
                Assert(index == (int)(childIndex.size()) - 1);
                unsigned nv = childIndex[index] + 1;
                if (nv < maxs[index] && nv <= max_i)
                {
                  childIndex[index] = nv;
                  index++;
                }
                else
                {
                  childIndex.pop_back();
                  index--;
                }
              }
            }
            success = index >= 0;
            if (success)
            {
              Trace("inst-alg-rd") << "Try instantiation { ";
              for (unsigned j = 0; j < childIndex.size(); j++)
              {
                Trace("inst-alg-rd") << childIndex[j] << " ";
              }
              Trace("inst-alg-rd") << "}" << std::endl;
              // try instantiation
              std::vector<Node> terms;
              for (unsigned i = 0; i < f[0].getNumChildren(); i++)
              {
                if (max_zero[i])
                {
                  // no terms available, will report incomplete instantiation
                  terms.push_back(Node::null());
                  Trace("inst-alg-rd") << "  null" << std::endl;
                }
                else if (r == 0)
                {
                  terms.push_back(rd->getRDomain(f, i)->d_terms[childIndex[i]]);
                  Trace("inst-alg-rd")
                      << "  " << rd->getRDomain(f, i)->d_terms[childIndex[i]]
                      << std::endl;
                }
                else
                {
                  Assert(childIndex[i] < term_db_list[ftypes[i]].size());
                  terms.push_back(term_db_list[ftypes[i]][childIndex[i]]);
                  Trace("inst-alg-rd") << "  "
                                       << term_db_list[ftypes[i]][childIndex[i]]
                                       << std::endl;
                }
              }
              if (d_quantEngine->addInstantiation(f, terms))
              {
                Trace("inst-alg-rd") << "Success!" << std::endl;
                ++(d_quantEngine->d_statistics.d_instantiations_guess);
                return true;
              }
              else
              {
                index--;
              }
            }
          } while (success);
          max_i++;
        }
      }
    }
  }
  // TODO : term enumerator instantiation?
  return false;
}

void InstStrategyEnum::registerQuantifier(Node q) {}
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
