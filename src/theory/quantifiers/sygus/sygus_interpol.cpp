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

void sygus_interpol::mkInterpolationConjecture(const std::string& name,
                                               const std::vector<Node>& axioms,
                                               const Node& conj,
                                               TypeNode itpGType,
																							 Node& sygusConj,
																							 vector<Expr>& varsToSynth,
																							 TypeNode itpGrammar)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-interpol-debug") << "Collect symbols..." << std::endl;
  std::unordered_set<Node, NodeHashFunction> symsetAxioms;
  std::unordered_set<Node, NodeHashFunction> symsetConj;
  std::unordered_set<Node, NodeHashFunction> symsetAll;
  std::unordered_set<Node, NodeHashFunction> symsetShared;
  for (size_t i = 0, size = axioms.size(); i < size; i++)
  {
    expr::getSymbols(axioms[i], symsetAxioms);
    expr::getSymbols(axioms[i], symsetAll);
  }
  expr::getSymbols(conj, symsetConj);
  expr::getSymbols(conj, symsetAll);
  for (const auto& elem : symsetConj)
  {
    if (symsetAxioms.find(elem) != symsetAxioms.end())
    {
      symsetShared.insert(elem);
    }
  }
  Trace("sygus-interpol-debug")
      << "...finish, got " << symsetAll.size() << " symbols in total. And "
      << symsetShared.size() << " shared symbols." << std::endl;

  Trace("sygus-interpol-debug") << "Setup symbols..." << std::endl;
  std::vector<Node> syms;
  std::vector<Node> vars;
  std::vector<Node> varsShared;
  std::vector<Node> varlist;
  std::vector<Node> varlistShared;
  std::vector<TypeNode> varlistTypes;
  std::vector<TypeNode> varlistTypesShared;
  for (const Node& s : symsetAll)
  {
    TypeNode tn = s.getType();
    // Notice that we allow for non-first class (e.g. function) variables here.
    std::stringstream ss;
    ss << s;
    Node var = nm->mkBoundVar(tn);
    syms.push_back(s);
    vars.push_back(var);
    Node vlv =
        nm->mkBoundVar(ss.str(), tn);
    varlist.push_back(vlv);
    varlistTypes.push_back(tn);
    if (symsetShared.find(s) != symsetShared.end())
    {
      varsShared.push_back(var);
			varsToSynth.push_back(var.toExpr());
      varlistShared.push_back(vlv);
      varlistTypesShared.push_back(tn);
    }
    // set that this variable encodes the term s
    SygusVarToTermAttribute sta;
    vlv.setAttribute(sta, s);
  }
  // make the sygus variable list
  Node abvlShared = nm->mkNode(BOUND_VAR_LIST, varlistShared);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

	Trace("sygus-interpol-debug") << "Setup grammar..." << std::endl;
  // TODO 	
	Trace("sygus-interpol-debug") << "...finish setting up grammar" << std::endl;

  Trace("sygus-interpol-debug")
      << "Make interpolation predicate..." << std::endl;
  // make the interpolation predicate to synthesize
  TypeNode itpType = varlistTypesShared.empty()
                         ? nm->booleanType()
                         : nm->mkPredicateType(varlistTypesShared);
  Node itp = nm->mkBoundVar(name.c_str(), itpType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make interpolation predicate app..."
                                << std::endl;  
  std::vector<Node> achildren;                 
  achildren.push_back(itp);
  achildren.insert(achildren.end(), varsShared.begin(), varsShared.end());
  Node itpApp =
      varsShared.empty()
          ? itp
          : nm->mkNode(
              APPLY_UF,
              achildren); 
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Set attributes..." << std::endl;
  // set the sygus bound variable list
  itp.setAttribute(theory::SygusSynthFunVarListAttribute(), abvlShared);
  // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  std::vector<Node> iplc;  // TODO what is this?
  iplc.push_back(instAttr);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, iplc);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol-debug") << "Make conjecture body..." << std::endl;
  Node Fa = axioms.size() == 1 ? axioms[0] : nm->mkNode(AND, axioms);
  Trace("sygus-interpol-debug") << "Fa before substitution: " << Fa << std::endl
                                << std::endl;
  Fa = Fa.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
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
  Fc = Fc.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  Node secondImplication = nm->mkNode(IMPLIES, itpApp, Fc);
  Trace("sygus-interpol-debug")
      << "second implication: " << secondImplication << std::endl
      << std::endl;
  // Fa( x ) => A( x ) ^ A( x ) => Fc( x )
  Node constraint = nm->mkNode(AND, firstImplication, secondImplication);
  Trace("sygus-interpol-debug") << constraint << "...finish" << std::endl;
  constraint = theory::Rewriter::rewrite(constraint);

  Trace("sygus-interpol-debug") << "Make conjecture..." << std::endl;
  // forall A. exists x. ~( Fa( x ) => A( x ) ^ A( x ) => Fc( x ) )
  sygusConj = constraint.negate();
  Node bvl = nm->mkNode(BOUND_VAR_LIST,
                        vars);  // TODO difference between bvl and abvl??
  sygusConj = nm->mkNode(EXISTS, bvl, sygusConj);
  Trace("sygus-interpol-debug") << "exists body: " << sygusConj << std::endl;
  Node fbvl = nm->mkNode(BOUND_VAR_LIST, itp);
  sygusConj = nm->mkNode(FORALL, fbvl, sygusConj, instAttrList);
  sygusConj = theory::Rewriter::rewrite(sygusConj);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol") << "Generate: " << sygusConj << std::endl;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
