/*********************                                                        */
/*! \file sygus_interpol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus interpolation utility, which
 ** transforms an input of axioms and conjecture into an interpolation problem,
 *and solve it.
 **/

#include "theory/quantifiers/sygus/sygus_interpol.h"

#include "expr/datatype.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "options/smt_options.h"
#include "printer/sygus_print_callback.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInterpol::SygusInterpol() {}

SygusInterpol::SygusInterpol(LogicInfo logic) : d_logic(logic) {}

void SygusInterpol::collectSymbols(const std::vector<Node>& axioms,
                                   const Node& conj)
{
  Trace("sygus-interpol-debug") << "Collect symbols..." << std::endl;
  std::unordered_set<Node, NodeHashFunction> symsetAxioms;
  std::unordered_set<Node, NodeHashFunction> symsetConj;
  for (size_t i = 0, size = axioms.size(); i < size; i++)
  {
    expr::getSymbols(axioms[i], symsetAxioms);
  }
  expr::getSymbols(conj, symsetConj);
  for (const Node& s : symsetAxioms)
  {
    d_syms.push_back(s);
  }
  for (const Node& s : symsetConj)
  {
    d_syms.push_back(s);
  }
  for (const auto& elem : symsetConj)
  {
    if (symsetAxioms.find(elem) != symsetAxioms.end())
    {
      d_symsetShared.insert(elem);
    }
  }
  Trace("sygus-interpol-debug")
      << "...finish, got " << d_syms.size() << " symbols in total. And "
      << d_symsetShared.size() << " shared symbols." << std::endl;
}

void SygusInterpol::createVariables(bool needsShared)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& s : d_syms)
  {
    TypeNode tn = s.getType();
    if (tn.isConstructor() || tn.isSelector() || tn.isTester())
    {
      // datatype symbols should be considered interpreted symbols here, not
      // (higher-order) variables.
      continue;
    }
    // Notice that we allow for non-first class (e.g. function) variables here.
    std::stringstream ss;
    ss << s;
    Node var = nm->mkBoundVar(tn);
    d_vars.push_back(var);
    Node vlv = nm->mkBoundVar(ss.str(), tn);
    d_vlvs.push_back(vlv);
    // TODO: bug fixed by hack (argument list for synthesis should be
    // consistent)
    if (!needsShared || d_symsetShared.find(s) != d_symsetShared.end())
    {
      d_varsShared.push_back(var);
      d_vlvsShared.push_back(vlv);
      d_varTypesShared.push_back(tn);
    }
  }
  // make the sygus variable list
  d_ibvlShared = nm->mkNode(kind::BOUND_VAR_LIST, d_vlvsShared);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;
}

std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > getIncludeCons(
    const std::vector<Node>& assumptions, const Node& conclusion)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(options::produceInterpols() != options::ProduceInterpols::NONE);
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > result =
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >();
  // ASSUMPTIONS
  if (options::produceInterpols() == options::ProduceInterpols::ASSUMPTIONS)
  {
    Node tmpAssumptions;
    if (assumptions.size() == 1)
    {
      tmpAssumptions = assumptions[0];
    }
    else
    {
      tmpAssumptions = nm->mkNode(kind::AND, assumptions);
    }
    expr::getOperatorsMap(tmpAssumptions, result);
  }
  // CONJECTURE
  else if (options::produceInterpols() == options::ProduceInterpols::CONJECTURE)
  {
    expr::getOperatorsMap(conclusion, result);
  }
  // SHARED
  else if (options::produceInterpols() == options::ProduceInterpols::SHARED)
  {
    // Get operators from assumptions
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >
        include_cons_assumptions =
            std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >();
    Node tmpAssumptions;
    if (assumptions.size() == 1)
    {
      tmpAssumptions = assumptions[0];
    }
    else
    {
      tmpAssumptions = nm->mkNode(kind::AND, assumptions);
    }
    expr::getOperatorsMap(tmpAssumptions, include_cons_assumptions);

    // Get operators from conclusion
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >
        include_cons_conclusion =
            std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >();
    expr::getOperatorsMap(conclusion, include_cons_conclusion);

    // Compute intersection
    for (std::map<TypeNode,
                  std::unordered_set<Node, NodeHashFunction> >::iterator itec =
             include_cons_assumptions.begin();
         itec != include_cons_assumptions.end();
         itec++)
    {
      TypeNode tn = itec->first;
      std::unordered_set<Node, NodeHashFunction> assumptionsOps = itec->second;
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >::iterator
          concIter = include_cons_conclusion.find(tn);
      if (concIter != include_cons_conclusion.end())
      {
        std::unordered_set<Node, NodeHashFunction> conclusionOps =
            concIter->second;
        std::unordered_set<Node, NodeHashFunction> conclusionOpsSet =
            std::unordered_set<Node, NodeHashFunction>(conclusionOps.begin(),
                                                       conclusionOps.end());
        for (Node n : assumptionsOps)
        {
          if (conclusionOpsSet.find(n) != conclusionOpsSet.end())
          {
            if (result.find(tn) == result.end())
            {
              result[tn] = std::unordered_set<Node, NodeHashFunction>();
            }
            result[tn].insert(n);
          }
        }
      }
    }
  }
  // ALL
  else if (options::produceInterpols() == options::ProduceInterpols::ALL)
  {
    Node tmpAssumptions;
    Node tmpConclusions;
    if (assumptions.size() == 1)
    {
      tmpAssumptions = assumptions[0];
    }
    else
    {
      Assert(assumptions.size() > 1);
      tmpAssumptions = nm->mkNode(kind::AND, assumptions);
    }
    Node tmpAll = nm->mkNode(kind::AND, tmpAssumptions, conclusion);
    expr::getOperatorsMap(tmpAll, result);
  }
  return result;
}

TypeNode SygusInterpol::setSynthGrammar(const TypeNode& itpGType,
                                        const std::vector<Node>& axioms,
                                        const Node& conj)
{
  Trace("sygus-interpol-debug") << "Setup grammar..." << std::endl;
  TypeNode itpGTypeS;
  if (!itpGType.isNull())
  {
    // set user-defined grammar
    Assert(itpGType.isDatatype() && itpGType.getDType().isSygus());
    itpGTypeS = datatypes::utils::substituteAndGeneralizeSygusType(
        itpGType, d_syms, d_vlvs);
    Assert(itpGTypeS.isDatatype() && itpGTypeS.getDType().isSygus());
    // TODO check if the vars in user-defined grammar, are consistent with the
    // shared vars
  }
  else
  {
    // set default grammar
    NodeManager* nm = NodeManager::currentNM();
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > extra_cons;
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >
        exclude_cons;
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >
        include_cons = getIncludeCons(axioms, conj);
    std::unordered_set<Node, NodeHashFunction> terms_irrelevant;
    itpGTypeS =
        CVC4::theory::quantifiers::CegGrammarConstructor::mkSygusDefaultType(
            nm->booleanType(),
            d_ibvlShared,
            "interpolation_grammar",
            extra_cons,
            exclude_cons,
            include_cons,
            terms_irrelevant);
  }
  Trace("sygus-interpol-debug") << "...finish setting up grammar" << std::endl;
  return itpGTypeS;
}

Node SygusInterpol::mkPredicate(const std::string& name)
{
  Node itp;
  return itp;
}

void SygusInterpol::mkSygusConjecture(Node itp,
                                      const std::vector<Node>& axioms,
                                      const Node& conj)
{
}

bool SygusInterpol::findInterpol(Expr& interpol, Node itp)
{
  return false;
}

bool SygusInterpol::SolveInterpolation(const std::string& name,
                                       const std::vector<Node>& axioms,
                                       const Node& conj,
                                       const TypeNode& itpGType,
                                       Expr& interpol)
{
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
