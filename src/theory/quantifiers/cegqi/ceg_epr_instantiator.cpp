/*********************                                                        */
/*! \file ceg_epr_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of ceg_epr_instantiator
 **/

#include "theory/quantifiers/cegqi/ceg_epr_instantiator.h"

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void EprInstantiator::reset(CegInstantiator* ci,
                            SolvedForm& sf,
                            Node pv,
                            CegInstEffort effort)
{
  d_equal_terms.clear();
}

bool EprInstantiator::hasProcessEqualTerm(CegInstantiator* ci,
                                          SolvedForm& sf,
                                          Node pv,
                                          CegInstEffort effort)
{
  return true;
}

bool EprInstantiator::processEqualTerm(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       TermProperties& pv_prop,
                                       Node n,
                                       CegInstEffort effort)
{
  if (options::quantEprMatching())
  {
    Assert(pv_prop.isBasic());
    d_equal_terms.push_back(n);
    return false;
  }
  pv_prop.d_type = CEG_TT_EQUAL;
  return ci->constructInstantiationInc(pv, n, pv_prop, sf);
}

struct sortEqTermsMatch
{
  std::map<Node, int> d_match_score;
  bool operator()(Node i, Node j)
  {
    int match_score_i = d_match_score[i];
    int match_score_j = d_match_score[j];
    return match_score_i > match_score_j
           || (match_score_i == match_score_j && i < j);
  }
};

bool EprInstantiator::processEqualTerms(CegInstantiator* ci,
                                        SolvedForm& sf,
                                        Node pv,
                                        std::vector<Node>& eqc,
                                        CegInstEffort effort)
{
  if (!options::quantEprMatching())
  {
    return false;
  }
  // heuristic for best matching constant
  sortEqTermsMatch setm;
  for (unsigned i = 0; i < ci->getNumCEAtoms(); i++)
  {
    Node catom = ci->getCEAtom(i);
    computeMatchScore(ci, pv, catom, catom, setm.d_match_score);
  }
  // sort by match score
  std::sort(d_equal_terms.begin(), d_equal_terms.end(), setm);
  TermProperties pv_prop;
  pv_prop.d_type = CEG_TT_EQUAL;
  for (unsigned i = 0, size = d_equal_terms.size(); i < size; i++)
  {
    if (ci->constructInstantiationInc(pv, d_equal_terms[i], pv_prop, sf))
    {
      return true;
    }
  }
  return false;
}

void EprInstantiator::computeMatchScore(CegInstantiator* ci,
                                        Node pv,
                                        Node catom,
                                        std::vector<Node>& arg_reps,
                                        TNodeTrie* tat,
                                        unsigned index,
                                        std::map<Node, int>& match_score)
{
  if (index == catom.getNumChildren())
  {
    Assert(tat->hasData());
    Node gcatom = tat->getData();
    Trace("cegqi-epr") << "Matched : " << catom << " and " << gcatom
                       << std::endl;
    for (unsigned i = 0, nchild = catom.getNumChildren(); i < nchild; i++)
    {
      if (catom[i] == pv)
      {
        Trace("cegqi-epr") << "...increment " << gcatom[i] << std::endl;
        match_score[gcatom[i]]++;
      }
      else
      {
        // recursive matching
        computeMatchScore(ci, pv, catom[i], gcatom[i], match_score);
      }
    }
    return;
  }
  std::map<TNode, TNodeTrie>::iterator it = tat->d_data.find(arg_reps[index]);
  if (it != tat->d_data.end())
  {
    computeMatchScore(
        ci, pv, catom, arg_reps, &it->second, index + 1, match_score);
  }
}

void EprInstantiator::computeMatchScore(CegInstantiator* ci,
                                        Node pv,
                                        Node catom,
                                        Node eqc,
                                        std::map<Node, int>& match_score)
{
  if (!inst::Trigger::isAtomicTrigger(catom) || !expr::hasSubterm(catom, pv))
  {
    return;
  }
  Trace("cegqi-epr") << "Find matches for " << catom << "..." << std::endl;
  eq::EqualityEngine* ee =
      ci->getQuantifiersEngine()->getMasterEqualityEngine();
  std::vector<Node> arg_reps;
  for (unsigned j = 0, nchild = catom.getNumChildren(); j < nchild; j++)
  {
    arg_reps.push_back(ee->getRepresentative(catom[j]));
  }
  if (!ee->hasTerm(eqc))
  {
    return;
  }
  TermDb* tdb = ci->getQuantifiersEngine()->getTermDatabase();
  Node rep = ee->getRepresentative(eqc);
  Node op = tdb->getMatchOperator(catom);
  TNodeTrie* tat = tdb->getTermArgTrie(rep, op);
  Trace("cegqi-epr") << "EPR instantiation match term : " << catom
                     << ", check ground terms=" << (tat != NULL) << std::endl;
  if (tat)
  {
    computeMatchScore(ci, pv, catom, arg_reps, tat, 0, match_score);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
