/*********************                                                        */
/*! \file quant_epr.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifier EPR.
 **/

#include "theory/quantifiers/quant_epr.h"

#include "theory/quantifiers/quant_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void QuantEPR::registerNode(Node n,
                            std::map<int, std::map<Node, bool> >& visited,
                            bool beneathQuant,
                            bool hasPol,
                            bool pol)
{
  int vindex = hasPol ? (pol ? 1 : -1) : 0;
  if (visited[vindex].find(n) == visited[vindex].end())
  {
    visited[vindex][n] = true;
    Trace("quant-epr-debug") << "QuantEPR::registerNode " << n << std::endl;
    if (n.getKind() == FORALL)
    {
      if (beneathQuant || !hasPol || !pol)
      {
        for (unsigned i = 0; i < n[0].getNumChildren(); i++)
        {
          TypeNode tn = n[0][i].getType();
          if (d_non_epr.find(tn) == d_non_epr.end())
          {
            Trace("quant-epr") << "Sort " << tn
                               << " is non-EPR because of nested or possible "
                                  "existential quantification."
                               << std::endl;
            d_non_epr[tn] = true;
          }
        }
      }
      else
      {
        beneathQuant = true;
      }
    }
    TypeNode tn = n.getType();

    if (n.getNumChildren() > 0)
    {
      if (tn.isSort())
      {
        if (d_non_epr.find(tn) == d_non_epr.end())
        {
          Trace("quant-epr") << "Sort " << tn << " is non-EPR because of " << n
                             << std::endl;
          d_non_epr[tn] = true;
        }
      }
      for (unsigned i = 0; i < n.getNumChildren(); i++)
      {
        bool newHasPol;
        bool newPol;
        QuantPhaseReq::getPolarity(n, i, hasPol, pol, newHasPol, newPol);
        registerNode(n[i], visited, beneathQuant, newHasPol, newPol);
      }
    }
    else if (tn.isSort())
    {
      if (n.getKind() == BOUND_VARIABLE)
      {
        if (d_consts.find(tn) == d_consts.end())
        {
          // mark that at least one constant must occur
          d_consts[tn].clear();
        }
      }
      else if (std::find(d_consts[tn].begin(), d_consts[tn].end(), n)
               == d_consts[tn].end())
      {
        d_consts[tn].push_back(n);
        Trace("quant-epr") << "...constant of type " << tn << " : " << n
                           << std::endl;
      }
    }
  }
}

void QuantEPR::registerAssertion(Node assertion)
{
  std::map<int, std::map<Node, bool> > visited;
  registerNode(assertion, visited, false, true, true);
}

void QuantEPR::finishInit()
{
  Trace("quant-epr-debug") << "QuantEPR::finishInit" << std::endl;
  for (std::map<TypeNode, std::vector<Node> >::iterator it = d_consts.begin();
       it != d_consts.end();
       ++it)
  {
    Assert(d_epr_axiom.find(it->first) == d_epr_axiom.end());
    Trace("quant-epr-debug") << "process " << it->first << std::endl;
    if (d_non_epr.find(it->first) != d_non_epr.end())
    {
      Trace("quant-epr-debug") << "...non-epr" << std::endl;
      it->second.clear();
    }
    else
    {
      Trace("quant-epr-debug") << "...epr, #consts = " << it->second.size()
                               << std::endl;
      if (it->second.empty())
      {
        it->second.push_back(NodeManager::currentNM()->mkSkolem(
            "e", it->first, "EPR base constant"));
      }
      if (Trace.isOn("quant-epr"))
      {
        Trace("quant-epr") << "Type " << it->first
                           << " is EPR, with constants : " << std::endl;
        for (unsigned i = 0; i < it->second.size(); i++)
        {
          Trace("quant-epr") << "  " << it->second[i] << std::endl;
        }
      }
    }
  }
}

bool QuantEPR::isEPRConstant(TypeNode tn, Node k)
{
  return std::find(d_consts[tn].begin(), d_consts[tn].end(), k)
         != d_consts[tn].end();
}

void QuantEPR::addEPRConstant(TypeNode tn, Node k)
{
  Assert(isEPR(tn));
  Assert(d_epr_axiom.find(tn) == d_epr_axiom.end());
  if (!isEPRConstant(tn, k))
  {
    d_consts[tn].push_back(k);
  }
}

Node QuantEPR::mkEPRAxiom(TypeNode tn)
{
  Assert(isEPR(tn));
  std::map<TypeNode, Node>::iterator ita = d_epr_axiom.find(tn);
  if (ita == d_epr_axiom.end())
  {
    std::vector<Node> disj;
    Node x = NodeManager::currentNM()->mkBoundVar(tn);
    for (unsigned i = 0; i < d_consts[tn].size(); i++)
    {
      disj.push_back(
          NodeManager::currentNM()->mkNode(EQUAL, x, d_consts[tn][i]));
    }
    Assert(!disj.empty());
    d_epr_axiom[tn] = NodeManager::currentNM()->mkNode(
        FORALL,
        NodeManager::currentNM()->mkNode(BOUND_VAR_LIST, x),
        disj.size() == 1 ? disj[0]
                         : NodeManager::currentNM()->mkNode(OR, disj));
    return d_epr_axiom[tn];
  }
  else
  {
    return ita->second;
  }
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
