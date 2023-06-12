/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus inference module.
 */

#include "preprocessing/passes/sygus_inference.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "smt/solver_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_preprocess.h"
#include "theory/quantifiers/sygus/sygus_utils.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"

using namespace std;
using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
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
    Trace("sygus-infer") << "...Solved:" << std::endl;
    Assert(funs.size() == sols.size());
    // if so, sygus gives us function definitions, which we add as substitutions
    for (unsigned i = 0, size = funs.size(); i < size; i++)
    {
      Trace("sygus-infer") << funs[i] << " -> " << sols[i] << std::endl;
      d_preprocContext->addSubstitution(funs[i], sols[i]);
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
        curr = rewrite(curr);
        Trace("sygus-infer-debug")
            << "...rewrote " << prev << " to " << curr << std::endl;
        assertionsToPreprocess->replace(i, curr);
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

bool SygusInference::solveSygus(const std::vector<Node>& assertions,
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
  std::unordered_set<TNode> visited;

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
  quantifiers::QuantifiersPreprocess qp(d_env);
  for (const Node& as : eassertions)
  {
    // substitution for this assertion
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::map<TypeNode, unsigned> type_count;
    Node pas = as;
    // rewrite
    pas = rewrite(pas);
    Trace("sygus-infer") << "assertion : " << pas << std::endl;
    if (pas.getKind() == FORALL)
    {
      // preprocess the quantified formula
      TrustNode trn = qp.preprocess(pas);
      if (!trn.isNull())
      {
        pas = trn.getNode();
      }
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
        vars.push_back(v);
        if (vnum < qtvars[tnv].size())
        {
          subs.push_back(qtvars[tnv][vnum]);
        }
        else
        {
          Assert(vnum == qtvars[tnv].size());
          Node bv = nm->mkBoundVar(tnv);
          qtvars[tnv].push_back(bv);
          qvars.push_back(bv);
          subs.push_back(bv);
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

  // Note that we do not restrict based on the types of free functions here,
  // i.e. we assume that all types are handled in sygus grammar construction.

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

  body = quantifiers::SygusUtils::mkSygusConjecture(ff_vars, body);

  Trace("sygus-infer") << "*** Return sygus inference : " << body << std::endl;

  // make a separate smt call
  std::unique_ptr<SolverEngine> rrSygus;
  theory::initializeSubsolver(rrSygus, d_env);
  rrSygus->assertFormula(body);
  Trace("sygus-infer") << "*** Check sat..." << std::endl;
  Result r = rrSygus->checkSat();
  Trace("sygus-infer") << "...result : " << r << std::endl;
  // get the synthesis solutions
  std::map<Node, Node> synth_sols;
  if (!rrSygus->getSubsolverSynthSolutions(synth_sols))
  {
    // failed, conjecture was infeasible
    return false;
  }

  std::vector<Node> final_ff;
  std::vector<Node> final_ff_sol;
  for (std::map<Node, Node>::iterator it = synth_sols.begin();
       it != synth_sols.end();
       ++it)
  {
    Trace("sygus-infer") << "  synth sol : " << it->first << " -> "
                         << it->second << std::endl;
    Node ffv = it->first;
    std::map<Node, Node>::iterator itffv = ff_var_to_ff.find(ffv);
    // all synthesis solutions should correspond to a variable we introduced
    Assert(itffv != ff_var_to_ff.end());
    if (itffv != ff_var_to_ff.end())
    {
      Node ff = itffv->second;
      Node body2 = it->second;
      Trace("sygus-infer") << "Define " << ff << " as " << body2 << std::endl;
      funs.push_back(ff);
      sols.push_back(body2);
    }
  }
  return true;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
