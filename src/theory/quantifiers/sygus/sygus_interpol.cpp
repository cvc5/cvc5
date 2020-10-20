/*********************                                                        */
/*! \file sygus_interpol.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus interpolation utility, which
 ** transforms an input of axioms and conjecture into an interpolation problem,
 *and solve it.
 **/

#include "theory/quantifiers/sygus/sygus_interpol.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/smt_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInterpol::SygusInterpol() {}

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
    // set that this variable encodes the term s
    SygusVarToTermAttribute sta;
    vlv.setAttribute(sta, s);
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
    itpGTypeS = CegGrammarConstructor::mkSygusDefaultType(
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
  NodeManager* nm = NodeManager::currentNM();
  // make the interpolation predicate to synthesize
  Trace("sygus-interpol-debug")
      << "Make interpolation predicate..." << std::endl;
  TypeNode itpType = d_varTypesShared.empty()
                         ? nm->booleanType()
                         : nm->mkPredicateType(d_varTypesShared);
  Node itp = nm->mkBoundVar(name.c_str(), itpType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;
  return itp;
}

void SygusInterpol::mkSygusConjecture(Node itp,
                                      const std::vector<Node>& axioms,
                                      const Node& conj)
{
  NodeManager* nm = NodeManager::currentNM();
  // make the interpolation application to synthesize
  Trace("sygus-interpol-debug")
      << "Make interpolation predicate app..." << std::endl;
  std::vector<Node> ichildren;
  ichildren.push_back(itp);
  ichildren.insert(ichildren.end(), d_varsShared.begin(), d_varsShared.end());
  Node itpApp =
      d_varsShared.empty() ? itp : nm->mkNode(kind::APPLY_UF, ichildren);
  Trace("sygus-interpol-debug") << "itpApp: " << itpApp << std::endl
                                << std::endl;
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // set the sygus bound variable list
  Trace("sygus-interpol-debug") << "Set attributes..." << std::endl;
  itp.setAttribute(SygusSynthFunVarListAttribute(), d_ibvlShared);
  // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(kind::INST_ATTRIBUTE, sygusVar);
  std::vector<Node> iplc;
  iplc.push_back(instAttr);
  Node instAttrList = nm->mkNode(kind::INST_PATTERN_LIST, iplc);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // Fa( x )
  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms);
  // Fa( x ) => A( x )
  Node firstImplication = nm->mkNode(kind::IMPLIES, Fa, itpApp);
  Trace("sygus-interpol-debug")
      << "first implication: " << firstImplication << std::endl
      << std::endl;
  // A( x ) => Fc( x )
  Node Fc = conj;
  Node secondImplication = nm->mkNode(kind::IMPLIES, itpApp, Fc);
  Trace("sygus-interpol-debug")
      << "second implication: " << secondImplication << std::endl
      << std::endl;
  // Fa( x ) => A( x ) ^ A( x ) => Fc( x )
  Node constraint = nm->mkNode(kind::AND, firstImplication, secondImplication);
  constraint = constraint.substitute(
      d_syms.begin(), d_syms.end(), d_vars.begin(), d_vars.end());
  Trace("sygus-interpol-debug") << constraint << "...finish" << std::endl;
  constraint = Rewriter::rewrite(constraint);

  d_sygusConj = constraint;
  Trace("sygus-interpol") << "Generate: " << d_sygusConj << std::endl;
}

bool SygusInterpol::findInterpol(Node& interpol, Node itp)
{
  // get the synthesis solution
  std::map<Node, Node> sols;
  d_subSolver->getSynthSolutions(sols);
  Assert(sols.size() == 1);
  std::map<Node, Node>::iterator its = sols.find(itp);
  if (its == sols.end())
  {
    Trace("sygus-interpol")
        << "SmtEngine::getInterpol: could not find solution!" << std::endl;
    throw RecoverableModalException(
        "Could not find solution for get-interpol.");
    return false;
  }
  Trace("sygus-interpol") << "SmtEngine::getInterpol: solution is "
                          << its->second << std::endl;
  interpol = its->second;
  // replace back the created variables to original symbols.
  if (interpol.getKind() == kind::LAMBDA)
  {
    interpol = interpol[1];
  }

  // get the grammar type for the interpolant
  Node igdtbv = itp.getAttribute(SygusSynthFunVarListAttribute());
  Assert(!igdtbv.isNull());
  Assert(igdtbv.getKind() == kind::BOUND_VAR_LIST);
  // convert back to original
  // must replace formal arguments of itp with the free variables in the
  // input problem that they correspond to.
  std::vector<Node> vars;
  std::vector<Node> syms;
  SygusVarToTermAttribute sta;
  for (const Node& bv : igdtbv)
  {
    vars.push_back(bv);
    syms.push_back(bv.hasAttribute(sta) ? bv.getAttribute(sta) : bv);
  }
  interpol =
      interpol.substitute(vars.begin(), vars.end(), syms.begin(), syms.end());

  return true;
}

bool SygusInterpol::SolveInterpolation(const std::string& name,
                                       const std::vector<Node>& axioms,
                                       const Node& conj,
                                       const TypeNode& itpGType,
                                       Node& interpol)
{
  initializeSubsolver(d_subSolver);
  // get the logic
  LogicInfo l = d_subSolver->getLogicInfo().getUnlockedCopy();
  // enable everything needed for sygus
  l.enableSygus();
  d_subSolver->setLogic(l);

  collectSymbols(axioms, conj);
  createVariables(itpGType.isNull());
  for (Node var : d_vars)
  {
    d_subSolver->declareSygusVar(name, var, var.getType());
  }
  std::vector<Node> vars_empty;
  TypeNode grammarType = setSynthGrammar(itpGType, axioms, conj);
  Node itp = mkPredicate(name);
  d_subSolver->declareSynthFun(name, itp, grammarType, false, vars_empty);
  mkSygusConjecture(itp, axioms, conj);
  Trace("sygus-interpol") << "SmtEngine::getInterpol: made conjecture : "
                          << d_sygusConj << ", solving for "
                          << d_sygusConj[0][0] << std::endl;
  d_subSolver->assertSygusConstraint(d_sygusConj);

  Trace("sygus-interpol") << "  SmtEngine::getInterpol check sat..."
                          << std::endl;
  Result r = d_subSolver->checkSynth();
  Trace("sygus-interpol") << "  SmtEngine::getInterpol result: " << r
                          << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
  {
    return findInterpol(interpol, itp);
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
