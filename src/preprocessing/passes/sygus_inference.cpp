/*********************                                                        */
/*! \file sygus_inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sygus inference module
 **/

#include "preprocessing/passes/sygus_inference.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace preprocessing {
namespace passes {

SygusInference::SygusInference(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "sygus-infer"){};

PreprocessingPassResult SygusInference::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  Trace("sygus-infer") << "Run sygus inference..." << std::endl;
  std::vector<Node> funs;
  std::vector<Node> sols;
  // see if we can succesfully solve the input as a sygus problem
  if (solveSygus(assertionsToPreprocess->ref(), funs, sols))
  {
    Assert(funs.size() == sols.size());
    // if so, sygus gives us function definitions
    SmtEngine* master_smte = smt::currentSmtEngine();
    for (unsigned i = 0, size = funs.size(); i < size; i++)
    {
      std::vector<Expr> args;
      Node sol = sols[i];
      // if it is a non-constant function
      if (sol.getKind() == LAMBDA)
      {
        for (const Node& v : sol[0])
        {
          args.push_back(v.toExpr());
        }
        sol = sol[1];
      }
      master_smte->defineFunction(funs[i].toExpr(), args, sol.toExpr());
    }

    // apply substitution to everything, should result in SAT
    for (unsigned i = 0, size = assertionsToPreprocess->ref().size(); i < size;
         i++)
    {
      Node prev = (*assertionsToPreprocess)[i];
      Node curr =
          prev.substitute(funs.begin(), funs.end(), sols.begin(), sols.end());
      if (curr != prev)
      {
        curr = theory::Rewriter::rewrite(curr);
        Trace("sygus-infer-debug")
            << "...rewrote " << prev << " to " << curr << std::endl;
        assertionsToPreprocess->replace(i, curr);
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

bool SygusInference::solveSygus(std::vector<Node>& assertions,
                                std::vector<Node>& funs,
                                std::vector<Node>& sols)
{
  if (assertions.empty())
  {
    Trace("sygus-infer") << "...fail: empty assertions." << std::endl;
    return false;
  }

  NodeManager* nm = NodeManager::currentNM();

  // collect free variables in all assertions
  std::vector<Node> qvars;
  std::map<TypeNode, std::vector<Node> > qtvars;
  std::vector<Node> free_functions;

  std::vector<TNode> visit;
  std::unordered_set<TNode, TNodeHashFunction> visited;

  // add top-level conjuncts to eassertions
  std::vector<Node> assertions_proc = assertions;
  std::vector<Node> eassertions;
  unsigned index = 0;
  while (index < assertions_proc.size())
  {
    Node ca = assertions_proc[index];
    if (ca.getKind() == AND)
    {
      for (const Node& ai : ca)
      {
        assertions_proc.push_back(ai);
      }
    }
    else
    {
      eassertions.push_back(ca);
    }
    index++;
  }

  // process eassertions
  std::vector<Node> processed_assertions;
  for (const Node& as : eassertions)
  {
    // substitution for this assertion
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::map<TypeNode, unsigned> type_count;
    Node pas = as;
    // rewrite
    pas = theory::Rewriter::rewrite(pas);
    Trace("sygus-infer") << "assertion : " << pas << std::endl;
    if (pas.getKind() == FORALL)
    {
      // preprocess the quantified formula
      pas = theory::quantifiers::QuantifiersRewriter::preprocess(pas);
      Trace("sygus-infer-debug") << "  ...preprocessed to " << pas << std::endl;
    }
    if (pas.getKind() == FORALL)
    {
      // it must be a standard quantifier
      theory::quantifiers::QAttributes qa;
      theory::quantifiers::QuantAttributes::computeQuantAttributes(pas, qa);
      if (!qa.isStandard())
      {
        Trace("sygus-infer")
            << "...fail: non-standard top-level quantifier." << std::endl;
        return false;
      }
      // infer prefix
      for (const Node& v : pas[0])
      {
        TypeNode tnv = v.getType();
        unsigned vnum = type_count[tnv];
        type_count[tnv]++;
        if (vnum < qtvars[tnv].size())
        {
          vars.push_back(v);
          subs.push_back(qtvars[tnv][vnum]);
        }
        else
        {
          Assert(vnum == qtvars[tnv].size());
          qtvars[tnv].push_back(v);
          qvars.push_back(v);
        }
      }
      pas = pas[1];
      if (!vars.empty())
      {
        pas =
            pas.substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
      }
    }
    Trace("sygus-infer-debug") << "  ...substituted to " << pas << std::endl;

    // collect free functions, ensure no quantified formulas
    TNode cur = pas;
    // compute free variables
    visit.push_back(cur);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.getKind() == APPLY_UF)
        {
          Node op = cur.getOperator();
          // visit the operator, which might not be a variable
          visit.push_back(op);
        }
        else if (cur.isVar() && cur.getKind() != BOUND_VARIABLE)
        {
          // We are either in the case of a free first-order constant or a
          // function in a higher-order context. We add to free_functions
          // in either case. Note that a free constant that is not in a
          // higher-order context is a 0-argument function-to-synthesize.
          // We should not have traversed here before due to our visited cache.
          Assert(std::find(free_functions.begin(), free_functions.end(), cur)
                 == free_functions.end());
          free_functions.push_back(cur);
        }
        else if (cur.isClosure())
        {
          Trace("sygus-infer")
              << "...fail: non-top-level quantifier." << std::endl;
          return false;
        }
        for (const TNode& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    } while (!visit.empty());
    processed_assertions.push_back(pas);
  }

  // no functions to synthesize
  if (free_functions.empty())
  {
    Trace("sygus-infer") << "...fail: no free function symbols." << std::endl;
    return false;
  }

  // Ensure the type of all free functions is handled by the sygus grammar
  // constructor utility.
  bool typeSuccess = true;
  for (const Node& f : free_functions)
  {
    TypeNode tn = f.getType();
    if (!theory::quantifiers::CegGrammarConstructor::isHandledType(tn))
    {
      Trace("sygus-infer") << "...fail: unhandled type " << tn << std::endl;
      typeSuccess = false;
      break;
    }
  }
  if (!typeSuccess)
  {
    return false;
  }

  Assert(!processed_assertions.empty());
  // conjunction of the assertions
  Trace("sygus-infer") << "Construct body..." << std::endl;
  Node body;
  if (processed_assertions.size() == 1)
  {
    body = processed_assertions[0];
  }
  else
  {
    body = nm->mkNode(AND, processed_assertions);
  }

  // for each free function symbol, make a bound variable of the same type
  Trace("sygus-infer") << "Do free function substitution..." << std::endl;
  std::vector<Node> ff_vars;
  std::map<Node, Node> ff_var_to_ff;
  for (const Node& ff : free_functions)
  {
    Node ffv = nm->mkBoundVar(ff.getType());
    ff_vars.push_back(ffv);
    Trace("sygus-infer") << "  synth-fun: " << ff << " as " << ffv << std::endl;
    ff_var_to_ff[ffv] = ff;
  }
  // substitute free functions -> variables
  body = body.substitute(free_functions.begin(),
                         free_functions.end(),
                         ff_vars.begin(),
                         ff_vars.end());
  Trace("sygus-infer-debug") << "...got : " << body << std::endl;

  // quantify the body
  Trace("sygus-infer") << "Make inner sygus conjecture..." << std::endl;
  body = body.negate();
  if (!qvars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, qvars);
    body = nm->mkNode(EXISTS, bvl, body);
  }

  // sygus attribute to mark the conjecture as a sygus conjecture
  Trace("sygus-infer") << "Make outer sygus conjecture..." << std::endl;
  Node sygusVar = nm->mkSkolem("sygus", nm->booleanType());
  theory::SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, instAttr);

  Node fbvl = nm->mkNode(BOUND_VAR_LIST, ff_vars);

  body = nm->mkNode(FORALL, fbvl, body, instAttrList);

  Trace("sygus-infer") << "*** Return sygus inference : " << body << std::endl;

  // make a separate smt call
  SmtEngine rrSygus(nm->toExprManager());
  rrSygus.setLogic(smt::currentSmtEngine()->getLogicInfo());
  rrSygus.assertFormula(body.toExpr());
  Trace("sygus-infer") << "*** Check sat..." << std::endl;
  Result r = rrSygus.checkSat();
  Trace("sygus-infer") << "...result : " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
  {
    // failed, conjecture was infeasible
    return false;
  }
  // get the synthesis solutions
  std::map<Expr, Expr> synth_sols;
  rrSygus.getSynthSolutions(synth_sols);

  std::vector<Node> final_ff;
  std::vector<Node> final_ff_sol;
  for (std::map<Expr, Expr>::iterator it = synth_sols.begin();
       it != synth_sols.end();
       ++it)
  {
    Trace("sygus-infer") << "  synth sol : " << it->first << " -> "
                         << it->second << std::endl;
    Node ffv = Node::fromExpr(it->first);
    std::map<Node, Node>::iterator itffv = ff_var_to_ff.find(ffv);
    // all synthesis solutions should correspond to a variable we introduced
    Assert(itffv != ff_var_to_ff.end());
    if (itffv != ff_var_to_ff.end())
    {
      Node ff = itffv->second;
      Node body2 = Node::fromExpr(it->second);
      Trace("sygus-infer") << "Define " << ff << " as " << body2 << std::endl;
      funs.push_back(ff);
      sols.push_back(body2);
    }
  }
  return true;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
