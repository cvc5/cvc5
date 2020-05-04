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
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void collectSymbols(const std::vector<Node>& axioms, const Node& conj)
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

void createVariables()
{
	Trace("sygus-interpol-debug") << "Setup symbols..." << std::endl;
	for (const Node& s : d_symsetAll)
	{
    TypeNode tn = s.getType();
    // Notice that we allow for non-first class (e.g. function) variables here.
    std::stringstream ss;
    ss << s;
    Node var = nm->mkBoundVar(tn);
    d_syms.push_back(s);
    d_vars.push_back(var);
    Node vlv = nm->mkBoundVar(ss.str(), tn);
    if (d_symsetShared.find(s) != d_symsetShared.end())
    {
      d_varsShared.push_back(var);
      d_vlvsShared.push_back(vlv);
      d_varTypesShared.push_back(tn);
    }
    // set that this variable encodes the term s
    SygusVarToTermAttribute sta;
    vlv.setAttribute(sta, s);
		// TODO: why this is after vlvsShared.push_back()
	}
	// make the sygus variable list
	d_abvlShared = nm->mkNode(BOUND_VAR_LIST, varlistShared);
	Trace("sygus-interpol-debug") << "...finish" << std::endl;
}

void setSynthGrammar()
{
  Trace("sygus-interpol-debug") << "Setup grammar..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > extra_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > exclude_cons;
  std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > include_cons;

  std::unordered_set<Node, NodeHashFunction> terms_irrelevant;
  TypeNode itpGTypeS =
      CVC4::theory::quantifiers::CegGrammarConstructor::mkSygusDefaultType(
          nm->booleanType(),
          abvlShared,
          "interpolation_grammar",
          extra_cons,
          exclude_cons,
          include_cons,
          terms_irrelevant);
  Node sym = nm->mkBoundVar("sfproxy_interpol", itpGTypeS);
  theory::SygusSynthGrammarAttribute ssg;
  itp.setAttribute(ssg, sym);

  Trace("sygus-interpol-debug") << "...finish setting up grammar" << std::endl;
}

void mkSygusConjecture()
{
	// make the interpolation predicate to synthesize
	Trace("sygus-interpol-debug")
		<< "Make interpolation predicate..." << std::endl;
	TypeNode itpType = d_varTypesShared.empty()
		? nm->booleanType()
		: nm->mkPredicateType(d_varTypesShared);
  Node itp = nm->mkBoundVar(name.c_str(), itpType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

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
  Fa = Fa.substitute(d_syms.begin(), d_syms.end(), d_vars.begin(), d_vars.end());
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
  Fc = Fc.substitute(d_syms.begin(), d_syms.end(), d_vars.begin(), d_vars.end());
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
	d_sygusConj = constraint.negate();
	//TODO return here
	Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
  d_sygusConj = nm->mkNode(EXISTS, bvl, d_sygusConj);
  Trace("sygus-interpol-debug") << "exists body: " << d_sygusConj << std::endl;
  Node fbvl = nm->mkNode(BOUND_VAR_LIST, itp);
  d_sygusConj = nm->mkNode(FORALL, fbvl, d_sygusConj, instAttrList);
  d_sygusConj = theory::Rewriter::rewrite(d_sygusConj);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol") << "Generate: " << d_sygusConj << std::endl;
}

void findInterpol(Expr& interpol)
{
	// get the synthesis solution
	std::map<Expr, Expr> sols;
	d_subsolver->getSynthSolutions(sols);
	Assert(sols.size() == 1);
	std::map<Expr, Expr>::iterator its = sols.find(d_sygusConj[0][0].toExpr());
  if (its != sols.end())
	{
		Trace("sygus-interpol")
			<< "SmtEngine::getInterpol: solution is " << its->second << std::endl;
		Node interpoln = Node::fromExpr(its->second);
		if (interpoln.getKind() == kind::LAMBDA)
		{
			interpoln = interpoln[1];
		}
		interpoln = interpoln.substitute(
				d_vars.begin(), d_vars.end(), d_syms.begin(), d_syms.end());
		// convert to expression
		interpol = interpoln.toExpr();
		// if check abducts option is set, we check the correctness
		if (options::checkInterpols())
		{
			checkInterpol(interpol);
		}
		return;
	}
	Trace("sygus-interpol")
		<< "SmtEngine::getInterpol: could not find solution!" << std::endl;
	throw RecoverableModalException(
			"Could not find solution for get-interpol.");
}

// TODO change this function
void SmtEngine::checkInterpol(Expr a)
{
  Assert(a.getType().isBoolean());
  Trace("check-interpol") << "SmtEngine::checkInterpol: get expanded assertions"
                          << std::endl;

  std::vector<Expr> asserts = getExpandedAssertions();

  // two checks: first, assertions imply a, second, a implies goal.
  for (unsigned j = 0; j < 2; j++)
  {
    if (j == 1)
    {
      Trace("check-interpol") << "SmtEngine::checkInterpol: goal is "
                              << d_interpolConj << std::endl;
    }
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": make new SMT engine" << std::endl;
    // Start new SMT engine to check solution
    SmtEngine itpChecker(d_exprManager);
    itpChecker.setLogic(getLogicInfo());
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": asserting formulas" << std::endl;
    if (j == 0)
    {
      for (const Expr& e : asserts)
      {
        itpChecker.assertFormula(e);
      }
      Expr nega = a.notExpr();
      itpChecker.assertFormula(nega);
    }
    else
    {
      itpChecker.assertFormula(a);
      Assert(!d_interpolConj.isNull());
      itpChecker.assertFormula(d_interpolConj);
    }
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": check the assertions" << std::endl;
    Result r = itpChecker.checkSat();
    Trace("check-interpol") << "SmtEngine::checkInterpol: phase " << j
                            << ": result is " << r << endl;
    std::stringstream serr;
    if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
    {
      if (j == 0)
      {
        serr << "SmtEngine::checkInterpol(): negated produced solution cannot "
                "be shown "
                "unsatisfiable with assertions, result was "
             << r;
      }
      else
      {
        serr << "SmtEngine::checkInterpol(): negated goal cannot be shown "
                "unsatisfiable with produced solution, result was "
             << r;
      }
      InternalError() << serr.str();
    }
  }
}

bool SolveInterpolation(const std::string& name,
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
  createVariables();
	Type grammarType = setSynthGrammar();

	// TODO declare vars one by one
	d_subsolver->declareSygusVar(name, abvlShared.toExpr(), BOUND_VAR_LIST);
	std::vector<Expr> vars_empty;
	Expr func;
	// TODO func should be itp
  d_subsolver->declareSynthFun(name, func, grammarType, false, vars_empty);
	mkSygusConjecture();
	d_subsolver->assertSygusConstraints(d_sygusConj.toExpr());

	Trace("sygus-interpol") << "  SmtEngine::getInterpol check sat..."
		<< std::endl;
	Result r = d_subsolver->checkSynth();
	Trace("sygus-interpol") << "  SmtEngine::getInterpol result: " << r
		<< std::endl;
	if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
	{
		findInterpol(interpol);
		return true;
	}
	return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
