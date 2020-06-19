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
 ** transforms an arbitrary input into an interpolation problem.
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

using namespace CVC4::kind;
using namespace std;

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
    expr::getSymbols(axioms[i], d_symsetAll);
  }
  expr::getSymbols(conj, symsetConj);
  expr::getSymbols(conj, d_symsetAll);
  for (const auto& elem : symsetConj)
  {
    if (symsetAxioms.find(elem) != symsetAxioms.end())
    {
      d_symsetShared.insert(elem);
    }
  }
  Trace("sygus-interpol-debug")
      << "...finish, got " << d_symsetAll.size() << " symbols in total. And "
      << d_symsetShared.size() << " shared symbols." << std::endl;
}

void SygusInterpol::createVariables(bool needsShared)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-interpol-debug") << "Setup symbols..." << std::endl;
  for (const Node& s : d_symsetAll)
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
    d_syms.push_back(s);
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
      d_symsShared.push_back(s);
    }
    // set that this variable encodes the term s
    SygusVarToTermAttribute sta;
    vlv.setAttribute(sta, s);
    // TODO: why this is after vlvsShared.push_back()
  }
  // make the sygus variable list
  d_abvlShared = nm->mkNode(BOUND_VAR_LIST, d_vlvsShared);
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
  // CONCLUSION
  else if (options::produceInterpols() == options::ProduceInterpols::CONCLUSION)
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
    // itpGTypeS = itpGType;
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
            d_abvlShared,
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
  std::vector<Node> achildren;
  achildren.push_back(itp);
  achildren.insert(achildren.end(), d_varsShared.begin(), d_varsShared.end());
  Node itpApp = d_varsShared.empty() ? itp : nm->mkNode(APPLY_UF, achildren);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // set the sygus bound variable list
  Trace("sygus-interpol-debug") << "Set attributes..." << std::endl;
  itp.setAttribute(theory::SygusSynthFunVarListAttribute(), d_abvlShared);
  // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  std::vector<Node> iplc;
  iplc.push_back(instAttr);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, iplc);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // Fa( x )
  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = axioms.size() == 1 ? axioms[0] : nm->mkNode(AND, axioms);
  Trace("sygus-interpol-debug") << "Fa before substitution: " << Fa << std::endl
                                << std::endl;
  Fa =
      Fa.substitute(d_syms.begin(), d_syms.end(), d_vars.begin(), d_vars.end());
  Trace("sygus-interpol-debug") << "Fa after substitution: " << Fa << std::endl
                                << std::endl;
  Trace("sygus-interpol-debug") << "itpApp: " << itpApp << std::endl
                                << std::endl;
  // Fa( x ) => A( x )
  Node firstImplication = nm->mkNode(IMPLIES, Fa, itpApp);
  Trace("sygus-interpol-debug")
      << "first implication: " << firstImplication << std::endl
      << std::endl;
  // A( x ) => Fc( x )
  Node Fc = conj;
  Fc =
      Fc.substitute(d_syms.begin(), d_syms.end(), d_vars.begin(), d_vars.end());
  Node secondImplication = nm->mkNode(IMPLIES, itpApp, Fc);
  Trace("sygus-interpol-debug")
      << "second implication: " << secondImplication << std::endl
      << std::endl;
  // Fa( x ) => A( x ) ^ A( x ) => Fc( x )
  Node constraint = nm->mkNode(AND, firstImplication, secondImplication);
  Trace("sygus-interpol-debug") << constraint << "...finish" << std::endl;
  constraint = theory::Rewriter::rewrite(constraint);

  // forall A. exists x. ~( Fa( x ) => A( x ) ^ A( x ) => Fc( x ) )
  Trace("sygus-interpol-debug") << "Make conjecture..." << std::endl;
  d_sygusConj = constraint;
  Trace("sygus-interpol-debug") << "...finish" << std::endl;
  Trace("sygus-interpol") << "Generate: " << d_sygusConj << std::endl;

  // TODO: to be removed
  d_sygusConj = constraint.negate();
  Node bvl = nm->mkNode(BOUND_VAR_LIST,
                        d_vars);  // TODO difference between bvl and abvl??
  d_sygusConj = nm->mkNode(EXISTS, bvl, d_sygusConj);
  Node fbvl = nm->mkNode(BOUND_VAR_LIST, itp);
  d_sygusConj = nm->mkNode(FORALL, fbvl, d_sygusConj, instAttrList);
  d_sygusConj = theory::Rewriter::rewrite(d_sygusConj);
}

bool SygusInterpol::findInterpol(Expr& interpol, Node itp)
{
  // get the synthesis solution
  std::map<Expr, Expr> sols;
  d_subsolver->getSynthSolutions(sols);
  Assert(sols.size() == 1);
  std::map<Expr, Expr>::iterator its = sols.find(itp.toExpr());
  if (its != sols.end())
  {
    Trace("sygus-interpol")
        << "SmtEngine::getInterpol: solution is " << its->second << std::endl;
    Node interpoln = Node::fromExpr(its->second);
    Node interpoln_reduced;
    if (interpoln.getKind() == kind::LAMBDA)
    {
      interpoln_reduced = interpoln[1];
    } else {
      interpoln_reduced = interpoln;
    }
    if (interpoln.getNumChildren() != 0 && interpoln[0].getNumChildren() != 0) {
      vector<Node> formals;
      for (Node n : interpoln[0]) {
        formals.push_back(n);
      }
      interpoln_reduced = interpoln_reduced.substitute(
          formals.begin(), formals.end(), d_symsShared.begin(), d_symsShared.end());
    }
    // convert to expression
    interpol = interpoln_reduced.toExpr();
    // if check abducts option is set, we check the correctness
    return true;
  }
  Trace("sygus-interpol") << "SmtEngine::getInterpol: could not find solution!"
                          << std::endl;
  throw RecoverableModalException("Could not find solution for get-interpol.");
  return false;
}

bool SygusInterpol::SolveInterpolation(const std::string& name,
                                       const std::vector<Node>& axioms,
                                       const Node& conj,
                                       const TypeNode& itpGType,
                                       Expr& interpol)
{
  NodeManager* nm = NodeManager::currentNM();
  // we generate a new smt engine to do the interpolation query
  d_subsolver.reset(new SmtEngine(nm->toExprManager()));
  d_subsolver->setIsInternalSubsolver();
  // get the logic
  LogicInfo l = d_logic.getUnlockedCopy();
  // enable everything needed for sygus
  l.enableSygus();
  d_subsolver->setLogic(l);

  collectSymbols(axioms, conj);
  createVariables(itpGType.isNull());
  // TODO not sure if it should be var or vlv. -- should be var
  // for (Node var : d_vars)
  //{
  //  d_subsolver->declareSygusVar(name, var.toExpr(), var.getType().toType());
  //}
  std::vector<Expr> vars_empty;
  TypeNode grammarType = setSynthGrammar(itpGType, axioms, conj);
  Node itp = mkPredicate(name);
  // TODO: to be removed
  Node sym = nm->mkBoundVar("sfproxy_interpol", grammarType);
  theory::SygusSynthGrammarAttribute ssg;
  itp.setAttribute(ssg, sym);

  // d_subsolver->declareSynthFun(
  //    name, itp.toExpr(), grammarType.toType(), false, vars_empty);
  mkSygusConjecture(itp, axioms, conj);
  Trace("sygus-interpol") << "SmtEngine::getInterpol: made conjecture : "
                          << d_sygusConj << ", solving for "
                          << d_sygusConj[0][0].toExpr() << std::endl;
  // d_subsolver->assertSygusConstraint(d_sygusConj.toExpr());
  d_subsolver->assertFormula(d_sygusConj.toExpr());

  Trace("sygus-interpol") << "  SmtEngine::getInterpol check sat..."
                          << std::endl;
  // Result r = d_subsolver->checkSynth();
  Result r = d_subsolver->checkSat();
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
