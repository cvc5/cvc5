/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus interpolation utility, which transforms an input of
 * axioms and conjecture into an interpolation problem, and solve it.
 */

#include "theory/quantifiers/sygus/sygus_interpol.h"

#include <sstream>

#include "base/modal_exception.h"
#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons_new.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusInterpol::SygusInterpol(Env& env) : EnvObj(env) {}

void SygusInterpol::collectSymbols(const std::vector<Node>& axioms,
                                   const Node& conj)
{
  Trace("sygus-interpol-debug") << "Collect symbols..." << std::endl;
  std::unordered_set<Node> symSetAxioms;
  std::unordered_set<Node> symSetConj;
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
    if (tn.isDatatypeConstructor() || tn.isDatatypeSelector()
        || tn.isDatatypeTester() || tn.isDatatypeUpdater())
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
  if (!d_vlvsShared.empty())
  {
    d_ibvlShared = nm->mkNode(kind::BOUND_VAR_LIST, d_vlvsShared);
  }
  Trace("sygus-interpol-debug") << "...finish" << std::endl;
}

void SygusInterpol::getIncludeCons(
    const std::vector<Node>& axioms,
    const Node& conj,
    std::map<TypeNode, std::unordered_set<Node>>& result)
{
  NodeManager* nm = NodeManager::currentNM();
  Assert(options().smt.produceInterpolants);
  // ASSUMPTIONS
  if (options().smt.interpolantsMode == options::InterpolantsMode::ASSUMPTIONS)
  {
    Node tmpAssumptions =
        (axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms));
    expr::getOperatorsMap(tmpAssumptions, result);
  }
  // CONJECTURE
  else if (options().smt.interpolantsMode
           == options::InterpolantsMode::CONJECTURE)
  {
    expr::getOperatorsMap(conj, result);
  }
  // SHARED
  else if (options().smt.interpolantsMode == options::InterpolantsMode::SHARED)
  {
    // Get operators from axioms
    std::map<TypeNode, std::unordered_set<Node>> include_cons_axioms;
    Node tmpAssumptions =
        (axioms.size() == 1 ? axioms[0] : nm->mkNode(kind::AND, axioms));
    expr::getOperatorsMap(tmpAssumptions, include_cons_axioms);

    // Get operators from conj
    std::map<TypeNode, std::unordered_set<Node>> include_cons_conj;
    expr::getOperatorsMap(conj, include_cons_conj);

    // Compute intersection
    for (std::map<TypeNode, std::unordered_set<Node>>::iterator it =
             include_cons_axioms.begin();
         it != include_cons_axioms.end();
         it++)
    {
      TypeNode tn = it->first;
      std::unordered_set<Node> axiomsOps = it->second;
      std::map<TypeNode, std::unordered_set<Node>>::iterator concIter =
          include_cons_conj.find(tn);
      if (concIter != include_cons_conj.end())
      {
        std::unordered_set<Node> conjOps = concIter->second;
        for (const Node& n : axiomsOps)
        {
          if (conjOps.find(n) != conjOps.end())
          {
            if (result.find(tn) == result.end())
            {
              result[tn] = std::unordered_set<Node>();
            }
            result[tn].insert(n);
          }
        }
      }
    }
  }
  // ALL
  else if (options().smt.interpolantsMode == options::InterpolantsMode::ALL)
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
    TypeNode btype = NodeManager::currentNM()->booleanType();
    SygusGrammar g =
        SygusGrammarCons::mkDefaultGrammar(options(), btype, d_ibvlShared);
    // exclude rules that don't appear in operators
    std::map<TypeNode, std::unordered_set<Node>> include_cons;
    getIncludeCons(axioms, conj, include_cons);
    const std::vector<Node>& ntSyms = g.getNtSyms();
    for (const Node& ntSym : ntSyms)
    {
      std::vector<Node> rules = g.getRulesFor(ntSym);
      TypeNode stype = ntSym.getType();
      if (include_cons.find(stype) == include_cons.end())
      {
        continue;
      }
      const std::unordered_set<Node>& icons = include_cons[ntSym.getType()];
      for (const Node& r : rules)
      {
        if (r.hasOperator() && icons.find(r.getOperator()) == icons.end())
        {
          g.removeRule(ntSym, r);
        }
      }
    }
    itpGTypeS = g.resolve(true);
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
  if (!d_ibvlShared.isNull())
  {
    SygusUtils::setSygusArgumentList(itp, d_ibvlShared);
  }
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // Fa( x )
  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = nm->mkAnd(axioms);
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
  constraint = rewrite(constraint);

  d_sygusConj = constraint;
  Trace("sygus-interpol") << "Generate: " << d_sygusConj << std::endl;
}

bool SygusInterpol::findInterpol(SolverEngine* subSolver,
                                 Node& interpol,
                                 Node itp)
{
  // get the synthesis solution
  std::map<Node, Node> sols;
  if (!subSolver->getSynthSolutions(sols))
  {
    return false;
  }
  Assert(sols.size() == 1);
  std::map<Node, Node>::iterator its = sols.find(itp);
  if (its == sols.end())
  {
    Trace("sygus-interpol")
        << "SolverEngine::getInterpol: could not find solution!" << std::endl;
    throw RecoverableModalException(
        "Could not find solution for get-interpolant.");
    return false;
  }
  Trace("sygus-interpol") << "SolverEngine::getInterpol: solution is "
                          << its->second << std::endl;
  interpol = its->second;
  // replace back the created variables to original symbols.
  if (interpol.getKind() == kind::LAMBDA)
  {
    interpol = interpol[1];
  }

  // get the grammar type for the interpolant
  Node igdtbv = SygusUtils::getOrMkSygusArgumentList(itp);
  // could have no variables, in which case there is nothing to do
  if (igdtbv.isNull())
  {
    return true;
  }
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

bool SygusInterpol::solveInterpolation(const std::string& name,
                                       const std::vector<Node>& axioms,
                                       const Node& conj,
                                       const TypeNode& itpGType,
                                       Node& interpol)
{
  // Some instructions in setSynthGrammar and mkSygusConjecture need a fully
  // initialized solver to work properly. Notice, however, that the sub-solver
  // created below is not fully initialized by the time those two methods are
  // needed. Therefore, we call them while the current parent solver is in scope
  // (i.e., before creating the sub-solver).
  collectSymbols(axioms, conj);
  createVariables(itpGType.isNull());
  TypeNode grammarType = setSynthGrammar(itpGType, axioms, conj);

  d_itp = mkPredicate(name);
  mkSygusConjecture(d_itp, axioms, conj);

  Options subOptions;
  subOptions.copyValues(d_env.getOptions());
  subOptions.writeQuantifiers().sygus = true;
  smt::SetDefaults::disableChecking(subOptions);
  SubsolverSetupInfo ssi(d_env, subOptions);
  initializeSubsolver(d_subSolver, ssi);

  for (const Node& var : d_vars)
  {
    d_subSolver->declareSygusVar(var);
  }
  std::vector<Node> vars_empty;
  d_subSolver->declareSynthFun(d_itp, grammarType, false, vars_empty);
  Trace("sygus-interpol")
      << "SygusInterpol::solveInterpolation: made conjecture : " << d_sygusConj
      << ", solving for " << d_sygusConj[0][0] << std::endl;
  d_subSolver->assertSygusConstraint(d_sygusConj);

  Trace("sygus-interpol")
      << "  SygusInterpol::solveInterpolation check synth..." << std::endl;
  SynthResult r = d_subSolver->checkSynth();
  Trace("sygus-interpol") << "  SygusInterpol::solveInterpolation result: " << r
                          << std::endl;
  if (r.getStatus() == SynthResult::SOLUTION)
  {
    return findInterpol(d_subSolver.get(), interpol, d_itp);
  }
  return false;
}

bool SygusInterpol::solveInterpolationNext(Node& interpol)
{
  Trace("sygus-interpol")
      << "  SygusInterpol::solveInterpolationNext check synth..." << std::endl;
  // invoke the check-synth with isNext = true.
  SynthResult r = d_subSolver->checkSynth(true);
  Trace("sygus-interpol") << "  SygusInterpol::solveInterpolationNext result: "
                          << r << std::endl;
  if (r.getStatus() == SynthResult::SOLUTION)
  {
    return findInterpol(d_subSolver.get(), interpol, d_itp);
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
