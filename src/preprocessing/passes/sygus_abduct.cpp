/*********************                                                        */
/*! \file sygus_abduct.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus abduction preprocessing pass, which
 ** transforms an arbitrary input into an abduction problem.
 **/

#include "preprocessing/passes/sygus_abduct.h"

#include "expr/datatype.h"
#include "expr/node_algorithm.h"
#include "printer/sygus_print_callback.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SygusAbduct::SygusAbduct(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sygus-abduct"){};

PreprocessingPassResult SygusAbduct::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-abduct") << "Run sygus abduct..." << std::endl;

  Trace("sygus-abduct-debug") << "Collect symbols..." << std::endl;
  std::unordered_set<Node, NodeHashFunction> symset;
  std::vector<Node>& asserts = assertionsToPreprocess->ref();
  // do we have any assumptions, e.g. via check-sat-assuming?
  bool usingAssumptions = (assertionsToPreprocess->getNumAssumptions() > 0);
  // The following is our set of "axioms". We construct this set only when the
  // usingAssumptions (above) is true. In this case, our input formula is
  // partitioned into Fa ^ Fc as described in the header of this class, where:
  // - The conjunction of assertions marked as assumptions are the negated
  // conjecture Fc, and
  // - The conjunction of all other assertions are the axioms Fa.
  std::vector<Node> axioms;
  for (size_t i = 0, size = asserts.size(); i < size; i++)
  {
    expr::getSymbols(asserts[i], symset);
    // if we are not an assumption, add it to the set of axioms
    if (usingAssumptions && i < assertionsToPreprocess->getAssumptionsStart())
    {
      axioms.push_back(asserts[i]);
    }
  }
  Trace("sygus-abduct-debug")
      << "...finish, got " << symset.size() << " symbols." << std::endl;

  Trace("sygus-abduct-debug") << "Setup symbols..." << std::endl;
  std::vector<Node> syms;
  std::vector<Node> vars;
  std::vector<Node> varlist;
  std::vector<TypeNode> varlistTypes;
  for (const Node& s : symset)
  {
    TypeNode tn = s.getType();
    if (tn.isFirstClass())
    {
      std::stringstream ss;
      ss << s;
      Node var = nm->mkBoundVar(tn);
      syms.push_back(s);
      vars.push_back(var);
      Node vlv = nm->mkBoundVar(ss.str(), tn);
      varlist.push_back(vlv);
      varlistTypes.push_back(tn);
    }
  }
  // make the sygus variable list
  Node abvl = nm->mkNode(BOUND_VAR_LIST, varlist);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make abduction predicate..." << std::endl;
  // make the abduction predicate to synthesize
  TypeNode abdType = varlistTypes.empty() ? nm->booleanType()
                                          : nm->mkPredicateType(varlistTypes);
  Node abd = nm->mkBoundVar("A", abdType);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  // get the abduction type
  TypeNode abdGType =
      TypeNode::fromType(d_preprocContext->getSmt()->getAbductionType());
  // if provided, we will associate it with the function-to-synthesize
  if (!abdGType.isNull())
  {
    Assert(abdGType.isDatatype() && abdGType.getDatatype().isSygus());
    // must convert all constructors to version with bound variables in "vars"
    std::vector<Datatype> datatypes;
    std::set<Type> unres;

    Trace("sygus-abduct-debug") << "Process abduction type:" << std::endl;
    Trace("sygus-abduct-debug") << abdGType.getDatatype() << std::endl;

    // datatype types we have processed
    std::vector<TypeNode> dtToProcess;
    std::map<TypeNode, TypeNode> dtProcessed;
    dtToProcess.push_back(abdGType);
    std::stringstream ssutn0;
    ssutn0 << abdGType.getDatatype().getName() << "_s";
    dtProcessed[abdGType] =
        nm->mkSort(ssutn0.str(), ExprManager::SORT_FLAG_PLACEHOLDER);

    while (!dtToProcess.empty())
    {
      std::vector<TypeNode> dtNextToProcess;
      for (const TypeNode& curr : dtToProcess)
      {
        Assert(curr.isDatatype() && curr.getDatatype().isSygus());
        const Datatype& dtc = curr.getDatatype();
        std::stringstream ssdtn;
        ssdtn << dtc.getName() << "_s";
        datatypes.push_back(Datatype(ssdtn.str()));
        Trace("sygus-abduct-debug")
            << "Process datatype " << datatypes.back().getName() << "..."
            << std::endl;
        for (unsigned j = 0, ncons = dtc.getNumConstructors(); j < ncons; j++)
        {
          Node op = Node::fromExpr(dtc[j].getSygusOp());
          Node ops = op.substitute(
              syms.begin(), syms.end(), varlist.begin(), varlist.end());
          Trace("sygus-abduct-debug") << "  Process constructor " << op << " / "
                                      << ops << "..." << std::endl;
          std::vector<Type> cargs;
          for (unsigned k = 0, nargs = dtc[j].getNumArgs(); k < nargs; k++)
          {
            TypeNode argt = TypeNode::fromType(dtc[j].getArgType(k));
            std::map<TypeNode, TypeNode>::iterator itdp =
                dtProcessed.find(argt);
            TypeNode argtNew;
            if (itdp == dtProcessed.end())
            {
              std::stringstream ssutn;
              ssutn << argt.getDatatype().getName() << "_s";
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
            Trace("sygus-abduct-debug")
                << "    Arg #" << k << ": " << argtNew << std::endl;
            cargs.push_back(argtNew.toType());
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
            spc = std::make_shared<printer::SygusExprPrintCallback>(
                opBody.toExpr(), args);
          }
          else if (cargs.empty())
          {
            spc = std::make_shared<printer::SygusExprPrintCallback>(op.toExpr(),
                                                                    args);
          }
          std::stringstream ss;
          ss << ops.getKind();
          Trace("sygus-abduct-debug")
              << "Add constructor : " << ops << std::endl;
          datatypes.back().addSygusConstructor(
              ops.toExpr(), ss.str(), cargs, spc);
        }
        Trace("sygus-abduct-debug")
            << "Set sygus : " << dtc.getSygusType() << " " << abvl << std::endl;
        datatypes.back().setSygus(dtc.getSygusType(),
                                  abvl.toExpr(),
                                  dtc.getSygusAllowConst(),
                                  dtc.getSygusAllowAll());
      }
      dtToProcess.clear();
      dtToProcess.insert(
          dtToProcess.end(), dtNextToProcess.begin(), dtNextToProcess.end());
    }
    Trace("sygus-abduct-debug")
        << "Make " << datatypes.size() << " datatype types..." << std::endl;
    // make the datatype types
    std::vector<DatatypeType> datatypeTypes =
        nm->toExprManager()->mkMutualDatatypeTypes(
            datatypes, unres, ExprManager::DATATYPE_FLAG_PLACEHOLDER);
    TypeNode abdGTypeS = TypeNode::fromType(datatypeTypes[0]);
    if (Trace.isOn("sygus-abduct-debug"))
    {
      Trace("sygus-abduct-debug") << "Made datatype types:" << std::endl;
      for (unsigned j = 0, ndts = datatypeTypes.size(); j < ndts; j++)
      {
        const Datatype& dtj = datatypeTypes[j].getDatatype();
        Trace("sygus-abduct-debug") << "#" << j << ": " << dtj << std::endl;
        for (unsigned k = 0, ncons = dtj.getNumConstructors(); k < ncons; k++)
        {
          for (unsigned l = 0, nargs = dtj[k].getNumArgs(); l < nargs; l++)
          {
            if (!dtj[k].getArgType(l).isDatatype())
            {
              Trace("sygus-abduct-debug")
                  << "Argument " << l << " of " << dtj[k]
                  << " is not datatype : " << dtj[k].getArgType(l) << std::endl;
              AlwaysAssert(false);
            }
          }
        }
      }
    }

    Trace("sygus-abduct-debug")
        << "Make sygus grammar attribute..." << std::endl;
    Node sym = nm->mkBoundVar("sfproxy_abduct", abdGTypeS);
    std::vector<Expr> attrValue;
    attrValue.push_back(sym.toExpr());
    d_preprocContext->getSmt()->setUserAttribute(
        "sygus-synth-grammar", abd.toExpr(), attrValue, "");
    Trace("sygus-abduct-debug") << "Finished setting up grammar." << std::endl;
  }

  Trace("sygus-abduct-debug") << "Make abduction predicate app..." << std::endl;
  std::vector<Node> achildren;
  achildren.push_back(abd);
  achildren.insert(achildren.end(), vars.begin(), vars.end());
  Node abdApp = vars.empty() ? abd : nm->mkNode(APPLY_UF, achildren);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Set attributes..." << std::endl;
  // set the sygus bound variable list
  abd.setAttribute(theory::SygusSynthFunVarListAttribute(), abvl);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make conjecture body..." << std::endl;
  Node input = asserts.size() == 1 ? asserts[0] : nm->mkNode(AND, asserts);
  input = input.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
  // A(x) => ~input( x )
  input = nm->mkNode(OR, abdApp.negate(), input.negate());
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  Trace("sygus-abduct-debug") << "Make conjecture..." << std::endl;
  Node res = input.negate();
  if (!vars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, vars);
    // exists x. ~( A( x ) => ~input( x ) )
    res = nm->mkNode(EXISTS, bvl, res);
  }
  // sygus attribute
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  std::vector<Node> iplc;
  iplc.push_back(instAttr);
  if (!axioms.empty())
  {
    Node aconj = axioms.size() == 1 ? axioms[0] : nm->mkNode(AND, axioms);
    aconj =
        aconj.substitute(syms.begin(), syms.end(), vars.begin(), vars.end());
    Trace("sygus-abduct") << "---> Assumptions: " << aconj << std::endl;
    Node sc = nm->mkNode(AND, aconj, abdApp);
    Node vbvl = nm->mkNode(BOUND_VAR_LIST, vars);
    sc = nm->mkNode(EXISTS, vbvl, sc);
    Node sygusScVar = nm->mkSkolem("sygus_sc", nm->booleanType());
    sygusScVar.setAttribute(theory::SygusSideConditionAttribute(), sc);
    instAttr = nm->mkNode(INST_ATTRIBUTE, sygusScVar);
    // build in the side condition
    //   exists x. A( x ) ^ input_axioms( x )
    // as an additional annotation on the sygus conjecture. In other words,
    // the abducts A we procedure must be consistent with our axioms.
    iplc.push_back(instAttr);
  }
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, iplc);

  Node fbvl = nm->mkNode(BOUND_VAR_LIST, abd);

  // forall A. exists x. ~( A( x ) => ~input( x ) )
  res = nm->mkNode(FORALL, fbvl, res, instAttrList);
  Trace("sygus-abduct-debug") << "...finish" << std::endl;

  res = theory::Rewriter::rewrite(res);

  Trace("sygus-abduct") << "Generate: " << res << std::endl;

  Node trueNode = nm->mkConst(true);

  assertionsToPreprocess->replace(0, res);
  for (size_t i = 1, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i, trueNode);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
