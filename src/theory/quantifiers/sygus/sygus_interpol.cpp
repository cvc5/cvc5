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

Node sygus_interpol::mkInterpolationConjecture(const std::string& name,
                                               const std::vector<Node>& axioms,
                                               const Node& conj,
											   TypeNode itpGType)
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
    // TODO do we allow non-first class? This is applicable to the case where we
    // are doing get-interpol in a logic with UF.
    std::stringstream ss;
    ss << s;
    Node var = nm->mkBoundVar(tn);
    syms.push_back(s);
    vars.push_back(var);
    Node vlv =
        nm->mkBoundVar(ss.str(), tn);  // TODO what is the difference with var?
    varlist.push_back(vlv);
    varlistTypes.push_back(tn);
    if (symsetShared.find(s) != symsetShared.end())
    {
      varsShared.push_back(var);
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

  Trace("sygus-interpol-debug")
      << "Make interpolation predicate..." << std::endl;
  // make the interpolation predicate to synthesize
  TypeNode itpType = varlistTypesShared.empty()
                         ? nm->booleanType()
                         : nm->mkPredicateType(varlistTypesShared);
  Node itp = nm->mkBoundVar(name.c_str(), itpType);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  // if provided, we will associate it with the function-to-synthesize
  if (!itpGType.isNull())
  {
	  Assert(itpGType.isDatatype() && itpGType.getDType().isSygus());
	  // must convert all constructors to version with bound variables in "vars"
	  std::vector<SygusDatatype> sdts;
	  std::set<Type> unres;

      Trace("sygus-interpol-debug") << "Process interpolation type:" << std::endl;
	  Trace("sygus-interpol-debug") << itpGType.getDType().getName() << std::endl;

	  // datatype types we need to process
	  std::vector<TypeNode> dtToProcess;
	  // datatype types we have processed
	  std::map<TypeNode, TypeNode> dtProcessed;
	  dtToProcess.push_back(itpGType);
	  std::stringstream ssutn0; // TODO why this name??
	  ssutn0 << itpGType.getDType().getName() << "_s"; // TODO ???
	  TypeNode itpTNew =
		  nm->mkSort(ssutn0.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
	  unres.insert(itpTNew.toType());
	  dtProcessed[itpGType] = itpTNew;

      // We must convert all symbols in the sygus datatype type itpGType to
	  // apply the substitution { syms -> varlist }, where syms is the free
	  // variables of the input problem, and varlist is the formal argument list
	  // of the interpol-to-synthesize. For example, given user-provided sygus grammar:
	  //   G -> a | +( b, G ) TODO
	  // we synthesize an interpol A with two arguments x_a and x_b corresponding to
	  // a and b, and reconstruct the grammar:
	  //   G' -> x_a | +( x_b, G' ) TODO
	  // In this way, x_a and x_b are treated as bound variables and handled as
	  // arguments of the interpol-to-synthesize instead of as free variables with
	  // no relation to A. We additionally require that x_a, when printed, prints
	  // "a", which we do with a custom sygus callback below.
	  
	  // We are traversing over the subfield types of the datatype to convert
	  // them into the form described above.
	  while (!dtToProcess.empty())
	  {
		  std::vector<TypeNode> dtNextToProcess;
		  for (const TypeNode& curr : dtToProcess)
		  {
			  Assert(curr.isDatatype() && curr.getDType().isSygus());
			  const DType& dtc = curr.getDType();
			  std::stringstream ssdtn;
			  ssdtn << dtc.getName() << "_s";
			  sdts.push_back(SygusDatatype(ssdtn.str()));
			  Trace("sygus-interpol-debug")
				  << "Process datatype " << sdts.back().getName() << "..."
				  << std::endl;
			  for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
			  {
				  Node op = dtc[j].getSygusOp();
				  // apply the substitution to the argument
				  Node ops = op.substitute(
						  syms.begin(), syms.end(), varlist.begin(), varlist.end());
				  Trace("sygus-interpol-debug") << "  Process constructor " << op << " / " << ops << "..." << std::endl;
				  std::vector<TypeNode> cargs;
				  for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
				  {
					  TypeNode argt = dtc[j].getArgType(k);
					  std::map<TypeNode, TypeNode>::iterator itdp =
						  dtProcessed.find(argt);
					  TypeNode argtNew;
					  if (itdp == dtProcessed.end())
					  {
						  std::stringstream ssutn;
						  ssutn << argt.getDType().getName() << "_s";
						  argtNew =
							  nm->mkSort(ssutn.str(), ExprManager::SORT_FLAG_PLACEHOLDER);
						  Trace("sygus-abduct-debug")
							  << "    ...unresolved type " << argtNew << " for " << argt
							  << std::endl;
						  unres.insert(argtNew.toType());
						  dtProcessed[argt] = argtNew;
						  dtNextToProcess.push_back(argt);
					  }
					  else
					  {
						  argtNew = itdp->second;
					  }
					  Trace("sygus-interpol-debug")
						  << "    Arg #" << k << ": " << argtNew << std::endl;
					  cargs.push_back(argtNew);
				  }
				  // callback prints as the expression
				  std::shared_ptr<SygusPrintCallback> spc;
				  std::vector<Expr> args;
				  if (op.getKind() == LAMBDA)
				  {
					  Node opBody = op[1];
					  for (const Node& v : op[0])
					  {
						  args.push_back(v.toExpr());
					  }
					  spc = std::make_shared<printer::SygusExprPrintCallback>(opBody.toExpr(), args);
				  }
				  else if (cargs.empty())
				  {
					  spc = std::make_shared<printer::SygusExprPrintCallback>(op.toExpr(), args);
				  }
				  std::stringstream ss;
				  ss << ops.getKind();
				  Trace("sygus-interpol-debug")
					  << "Add constructor : " << ops << std::endl;
				  sdts.back().addConstructor(ops, ss.str(), cargs, spc);
			  }
			  Trace("sygus-interpol-debug")
				  << "Set sygus : " << dtc.getSygusType() << " " << abvlShared << std::endl;
			  TypeNode stn = dtc.getSygusType();
			  sdts.back().initializeDatatype(
					  stn, abvlShared, dtc.getSygusAllowConst(), dtc.getSygusAllowAll());
		  }
		  dtToProcess.clear();
		  dtToProcess.insert(
				  dtToProcess.end(), dtNextToProcess.begin(), dtNextToProcess.end());
	  }
	  Trace("sygus-interpol-debug")
		  << "Make " << sdts.size() << " datatype types..." << std::endl;
	  // extract the datatypes
	  std::vector<Datatype> datatypes;
	  for (unsigned i = 0, ndts = sdts.size(); i < ndts; i++)
	  {
		  datatypes.push_back(sdts[i].getDatatype());
	  }
	  // make the datatype types
	  std::vector<DatatypeType> datatypeTypes =
		  nm->toExprManager()->mkMutualDatatypeTypes(
				  datatypes, unres, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
	  TypeNode itpGTypeS = TypeNode::fromType(datatypeTypes[0]);
	  if (Trace.isOn("sygus-interpol-debug"))
	  {
		  Trace("sygus-interpol-debug") << "Made datatype types:" << std::endl;
		  for (unsigned j = 0, ndts = datatypeType.size(); j < ndts; j++)
		  {
			  const DType& dtj = TypeNode::fromType(datatypeTypes[j]).getDType();
			  Trace("sygus-interpol-debug") << "#" << j << ": " << dtj << std::endl;
			  for (unsigned k = 0, ncons = dtj.getNumConstructors(); k < ncons; k++)
			  {
				  for (unsigned l = 0, nargs = dtj[k].getNumArgs(); l < nargs; l++)
				  {
					  if (!dtj[k].getArgType(l).isDatatype())
					  {
						  Trace("sygus-interpol-debug")
							  << "Argument " << l << " of " << dtj[k]
							  << " is not datatype : " << dtj[k].getArgType(l) << std::endl;
						  AlwaysAssert(false);
					  }
				  }
			  }
		  }
	  }

	  Trace("sygus-interpol-debug")
		  << "Make sygus grammar attribute..." << std::endl;
	  Node sym = nm->mkBoundVar("sfproxy_interpol", itpGTypeS);
	  // Set the sygus grammar attribute to indicate that itpGTypeS encodes the
	  // grammar for itp.
	  theory::SygusSynthGrammarAttribute ssg;
	  itp.setAttribute(ssg, sym);
	  Trace("sygus-interpol-debug") << "Finished setting up grammar." << std::endl;
  }

  Trace("sygus-interpol-debug") << "Make interpolation predicate app..."
                                << std::endl;  // TODO what is "app"?
  std::vector<Node> achildren;                 // TODO achildren? why this name?
  achildren.push_back(itp);
  achildren.insert(achildren.end(), varsShared.begin(), varsShared.end());
  Node itpApp =
      varsShared.empty()
          ? itp
          : nm->mkNode(
              APPLY_UF,
              achildren);  // TODO what's the meanning of apply_uf on itp
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
  Trace("sygus-interpol-debug") << "Fa before substitution: " << Fa << std::endl << std::endl; 
  Fa = Fa.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  Trace("sygus-interpol-debug") << "Fa after substitution: " << Fa << std::endl << std::endl;
  Trace("sygus-interpol-debug") << "itpApp: " << itpApp << std::endl << std::endl;
  // Fa( x ) => A( x )
  Node firstImplication = nm->mkNode(IMPLIES, Fa, itpApp);
  Trace("sygus-interpol-debug") << "first implication: " << firstImplication << std::endl << std::endl;
  // A( x ) => Fc( x )
  Node Fc = conj;
  Fc = Fc.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  Node secondImplication = nm->mkNode(IMPLIES, itpApp, Fc);
  Trace("sygus-interpol-debug") << "second implication: " << secondImplication << std::endl << std::endl;
  // Fa( x ) => A( x ) ^ A( x ) => Fc( x )
  Node constraint = nm->mkNode(AND, firstImplication, secondImplication);
  Trace("sygus-interpol-debug") << constraint <<  "...finish" << std::endl;
  constraint = theory::Rewriter::rewrite(constraint);

  Trace("sygus-interpol-debug") << "Make conjecture..." << std::endl;
  // forall A. exists x. ~( Fa( x ) => A( x ) ^ A( x ) => Fc( x ) )
  Node res = constraint.negate();
  Node bvl = nm->mkNode(BOUND_VAR_LIST,
                        vars);  // TODO difference between bvl and abvl??
  res = nm->mkNode(EXISTS, bvl, res);
  Trace("sygus-interpol-debug") << "exists body: " << res << std::endl;
  Node fbvl = nm->mkNode(BOUND_VAR_LIST, itp);
  res = nm->mkNode(FORALL, fbvl, res, instAttrList);
  res = theory::Rewriter::rewrite(res);
  Trace("sygus-interpol-debug") << "...finish" << std::endl;

  Trace("sygus-interpol") << "Generate: " << res << std::endl;

  return res;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
