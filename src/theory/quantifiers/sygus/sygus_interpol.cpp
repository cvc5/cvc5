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
  std::unordered_set<Node, NodeHashFunction> symSetAxioms;
  std::unordered_set<Node, NodeHashFunction> symSetConj;
  for (size_t i = 0, size = axioms.size(); i < size; i++)
  {
    expr::getSymbols(axioms[i], symSetAxioms);
  }
  expr::getSymbols(conj, symSetConj);
  d_syms.insert(d_syms.end(), symSetAxioms.begin(), symSetAxioms.end());
  d_syms.insert(d_syms.end(), symSetConj.begin(), symSetConj.end());
  for (const Node& elem : symSetConj)
  {
    if (symSetAxioms.find(elem) != symSetAxioms.end())
    {
      d_symSetShared.insert(elem);
    }
  }
  Trace("sygus-interpol-debug")
      << "...finish, got " << d_syms.size() << " symbols in total. And "
      << d_symSetShared.size() << " shared symbols." << std::endl;
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
    if (!needsShared || d_symSetShared.find(s) != d_symSetShared.end())
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

void SygusInterpol::getIncludeCons(
    const std::vector<Node>& axioms,
    const Node& conj,
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>& result)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(options::produceInterpols() != options::ProduceInterpols::NONE);
  // ASSUMPTIONS
  if (options::produceInterpols() == options::ProduceInterpols::ASSUMPTIONS)
  {
    Node tmpAssumptions =
        (axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms));
    expr::getOperatorsMap(tmpAssumptions, result);
  }
  // CONJECTURE
  else if (options::produceInterpols() == options::ProduceInterpols::CONJECTURE)
  {
    expr::getOperatorsMap(conj, result);
  }
  // SHARED
  else if (options::produceInterpols() == options::ProduceInterpols::SHARED)
  {
    // Get operators from axioms
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>
        include_cons_axioms;
    Node tmpAssumptions =
        (axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms));
    expr::getOperatorsMap(tmpAssumptions, include_cons_axioms);

    // Get operators from conj
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>
        include_cons_conj;
    expr::getOperatorsMap(conj, include_cons_conj);

    // Compute intersection
    for (std::map<TypeNode,
                  std::unordered_set<Node, NodeHashFunction>>::iterator it =
             include_cons_axioms.begin();
         it != include_cons_axioms.end();
         it++)
    {
      TypeNode tn = it->first;
      std::unordered_set<Node, NodeHashFunction> axiomsOps = it->second;
      std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>>::iterator
          concIter = include_cons_conj.find(tn);
      if (concIter != include_cons_conj.end())
      {
        std::unordered_set<Node, NodeHashFunction> conjOps = concIter->second;
        for (const Node& n : axiomsOps)
        {
          if (conjOps.find(n) != conjOps.end())
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
    Node tmpAssumptions =
        (axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms));
    Node tmpAll = nm->mkNode(kind::AND, tmpAssumptions, conj);
    expr::getOperatorsMap(tmpAll, result);
  }
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
    // TODO(Ying Sheng) check if the vars in user-defined grammar, are
    // consistent with the shared vars
  }
  else
  {
    // set default grammar
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> extra_cons;
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> exclude_cons;
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction>> include_cons;
    getIncludeCons(axioms, conj, include_cons);
    std::unordered_set<Node, NodeHashFunction> terms_irrelevant;
    itpGTypeS =
        CVC4::theory::quantifiers::CegGrammarConstructor::mkSygusDefaultType(
            NodeManager::currentNM()->booleanType(),
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
