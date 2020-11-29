/*********************                                                        */
/*! \file inst_strategy_enumerative.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of an enumerative instantiation strategy.
 **/

#include "theory/quantifiers/inst_strategy_enumerative.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {

using namespace kind;
using namespace context;

namespace theory {

using namespace inst;

namespace quantifiers {

InstStrategyEnum::InstStrategyEnum(QuantifiersEngine* qe, RelevantDomain* rd)
    : QuantifiersModule(qe), d_rd(rd), d_fullSaturateLimit(-1)
{
}
void InstStrategyEnum::presolve()
{
  d_fullSaturateLimit = options::fullSaturateLimit();
}
bool InstStrategyEnum::needsCheck(Theory::Effort e)
{
  if (d_fullSaturateLimit == 0)
  {
    return false;
  }
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
void InstStrategyEnum::check(Theory::Effort e, QEffort quant_e)
{
  bool doCheck = false;
  bool fullEffort = false;
  if (d_fullSaturateLimit != 0)
  {
    if (options::fullSaturateInterleave())
    {
      // we only add when interleaved with other strategies
      doCheck = quant_e == QEFFORT_STANDARD && d_quantEngine->hasAddedLemma();
    }
    if (options::fullSaturateQuant() && !doCheck)
    {
      if (!d_quantEngine->theoryEngineNeedsCheck())
      {
        doCheck = quant_e == QEFFORT_LAST_CALL;
        fullEffort = true;
      }
    }
  }
  if (!doCheck)
  {
    return;
  }
  Assert(!d_quantEngine->inConflict());
  double clSet = 0;
  if (Trace.isOn("fs-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("fs-engine") << "---Full Saturation Round, effort = " << e << "---"
                       << std::endl;
  }
  unsigned rstart = options::fullSaturateQuantRd() ? 0 : 1;
  unsigned rend = fullEffort ? 1 : rstart;
  unsigned addedLemmas = 0;
  // First try in relevant domain of all quantified formulas, if no
  // instantiations exist, try arbitrary ground terms.
  // Notice that this stratification of effort levels makes it so that some
  // quantified formulas may not be instantiated (if they have no instances
  // at effort level r=0 but another quantified formula does). We prefer
  // this stratification since effort level r=1 may be highly expensive in the
  // case where we have a quantified formula with many entailed instances.
  FirstOrderModel* fm = d_quantEngine->getModel();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  std::map<Node, bool> alreadyProc;
  for (unsigned r = rstart; r <= rend; r++)
  {
    if (d_rd || r > 0)
    {
      if (r == 0)
      {
        Trace("inst-alg") << "-> Relevant domain instantiate..." << std::endl;
        Trace("inst-alg-debug") << "Compute relevant domain..." << std::endl;
        d_rd->compute();
        Trace("inst-alg-debug") << "...finished" << std::endl;
      }
      else
      {
        Trace("inst-alg") << "-> Ground term instantiate..." << std::endl;
      }
      for (unsigned i = 0; i < nquant; i++)
      {
        Node q = fm->getAssertedQuantifier(i, true);
        bool doProcess = d_quantEngine->hasOwnership(q, this)
                         && fm->isQuantifierActive(q)
                         && alreadyProc.find(q) == alreadyProc.end();
        if (doProcess)
        {
          if (process(q, fullEffort, r == 0))
          {
            // don't need to mark this if we are not stratifying
            if (!options::fullSaturateStratify())
            {
              alreadyProc[q] = true;
            }
            // added lemma
            addedLemmas++;
          }
          if (d_quantEngine->inConflict())
          {
            break;
          }
        }
      }
      if (d_quantEngine->inConflict()
          || (addedLemmas > 0 && options::fullSaturateStratify()))
      {
        // we break if we are in conflict, or if we added any lemma at this
        // effort level and we stratify effort levels.
        break;
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
  if (d_fullSaturateLimit > 0)
  {
    d_fullSaturateLimit--;
  }
}

bool InstStrategyEnum::process(Node f, bool fullEffort, bool isRd)
{
  // ignore if constant true (rare case of non-standard quantifier whose body is
  // rewritten to true)
  if (f[1].isConst() && f[1].getConst<bool>())
  {
    return false;
  }
  unsigned final_max_i = 0;
  std::vector<unsigned> maxs;
  std::vector<bool> max_zero;
  bool has_zero = false;
  std::map<TypeNode, std::vector<Node> > term_db_list;
  std::vector<TypeNode> ftypes;
  TermDb* tdb = d_quantEngine->getTermDatabase();
  EqualityQuery* qy = d_quantEngine->getEqualityQuery();
  // iterate over substitutions for variables
  for (unsigned i = 0; i < f[0].getNumChildren(); i++)
  {
    TypeNode tn = f[0][i].getType();
    ftypes.push_back(tn);
    unsigned ts;
    if (isRd)
    {
      ts = d_rd->getRDomain(f, i)->d_terms.size();
    }
    else
    {
      ts = tdb->getNumTypeGroundTerms(tn);
      std::map<TypeNode, std::vector<Node> >::iterator ittd =
          term_db_list.find(tn);
      if (ittd == term_db_list.end())
      {
        std::map<Node, Node> reps_found;
        for (unsigned j = 0; j < ts; j++)
        {
          Node gt = tdb->getTypeGroundTerm(ftypes[i], j);
          if (!options::cegqi() || !quantifiers::TermUtil::hasInstConstAttr(gt))
          {
            Node rep = qy->getRepresentative(gt);
            if (reps_found.find(rep) == reps_found.end())
            {
              reps_found[rep] = gt;
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
    maxs.push_back(ts);
    if (ts > final_max_i)
    {
      final_max_i = ts;
    }
  }
  if (!has_zero)
  {
    Trace("inst-alg-rd") << "Will do " << final_max_i
                         << " stages of instantiation." << std::endl;
    unsigned max_i = 0;
    bool success;
    Instantiate* ie = d_quantEngine->getInstantiate();
    while (max_i <= final_max_i)
    {
      Trace("inst-alg-rd") << "Try stage " << max_i << "..." << std::endl;
      std::vector<unsigned> childIndex;
      int index = 0;
      do
      {
        while (index >= 0 && index < (int)f[0].getNumChildren())
        {
          if (index == static_cast<int>(childIndex.size()))
          {
            childIndex.push_back(-1);
          }
          else
          {
            Assert(index == static_cast<int>(childIndex.size()) - 1);
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
          if (Trace.isOn("inst-alg-rd"))
          {
            Trace("inst-alg-rd") << "Try instantiation { ";
            for (unsigned i : childIndex)
            {
              Trace("inst-alg-rd") << i << " ";
            }
            Trace("inst-alg-rd") << "}" << std::endl;
          }
          // try instantiation
          std::vector<Node> terms;
          for (unsigned i = 0, nchild = f[0].getNumChildren(); i < nchild; i++)
          {
            if (max_zero[i])
            {
              // no terms available, will report incomplete instantiation
              terms.push_back(Node::null());
              Trace("inst-alg-rd") << "  null" << std::endl;
            }
            else if (isRd)
            {
              terms.push_back(d_rd->getRDomain(f, i)->d_terms[childIndex[i]]);
              Trace("inst-alg-rd")
                  << "  (rd) " << d_rd->getRDomain(f, i)->d_terms[childIndex[i]]
                  << std::endl;
            }
            else
            {
              Assert(childIndex[i] < term_db_list[ftypes[i]].size());
              terms.push_back(term_db_list[ftypes[i]][childIndex[i]]);
              Trace("inst-alg-rd")
                  << "  " << term_db_list[ftypes[i]][childIndex[i]]
                  << std::endl;
            }
            Assert(terms[i].isNull()
                   || terms[i].getType().isComparableTo(ftypes[i]));
          }
          if (ie->addInstantiation(f, terms))
          {
            Trace("inst-alg-rd") << "Success!" << std::endl;
            ++(d_quantEngine->d_statistics.d_instantiations_guess);
            return true;
          }
          else
          {
            index--;
          }
          if (d_quantEngine->inConflict())
          {
            // could be conflicting for an internal reason (such as term
            // indices computed in above calls)
            return false;
          }
        }
      } while (success);
      max_i++;
    }
  }
  // TODO : term enumerator instantiation?
  return false;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
