/*********************                                                        */
/*! \file sygus_inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_inference
 **/

#include "theory/quantifiers/sygus_inference.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusInference::SygusInference() {}

bool SygusInference::simplify(std::vector<Node>& assertions)
{
  Trace("sygus-infer") << "Sygus inference : " << std::endl;

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

  std::vector<Node> processed_assertions;
  for (const Node& as : assertions)
  {
    // substitution for this assertion
    std::vector<Node> vars;
    std::vector<Node> subs;
    std::map<TypeNode, unsigned> type_count;
    Node pas = as;
    // rewrite
    pas = Rewriter::rewrite( pas );
    Trace("sygus-infer") << "  " << pas << std::endl;
    if (pas.getKind() == FORALL)
    {
      // preprocess the quantified formula
      pas = quantifiers::QuantifiersRewriter::preprocess(pas);
      Trace("sygus-infer-debug") << "  ...preprocessed to " << pas << std::endl;
      
      pas = pas[1];
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
          if (std::find(free_functions.begin(), free_functions.end(), op)
              == free_functions.end())
          {
            free_functions.push_back(op);
          }
        }
        else if (cur.getKind() == FORALL)
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

  // if no free function symbols, there is no use changing into SyGuS
  if (free_functions.empty())
  {
    Trace("sygus-infer") << "...fail: no free function symbols." << std::endl;
    return false;
  }

  // conjunction of the assertions
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
  std::vector<Node> ff_vars;
  for (const Node& ff : free_functions)
  {
    Node ffv = nm->mkBoundVar(ff.getType());
    ff_vars.push_back(ffv);
  }
  // substitute free functions -> variables
  body = body.substitute(free_functions.begin(),
                         free_functions.end(),
                         ff_vars.begin(),
                         ff_vars.end());

  // quantify the body
  if (!qvars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, qvars);
    body = nm->mkNode(EXISTS, bvl, body.negate());
  }

  // sygus attribute to mark the conjecture as a sygus conjecture
  Node sygusVar = nm->mkBoundVar("sygus", nm->booleanType());
  SygusAttribute ca;
  sygusVar.setAttribute(ca, true);
  Node instAttr = nm->mkNode(INST_ATTRIBUTE, sygusVar);
  Node instAttrList = nm->mkNode(INST_PATTERN_LIST, instAttr);

  Node fbvl = nm->mkNode(BOUND_VAR_LIST, ff_vars);

  body = nm->mkNode(FORALL, fbvl, body, instAttrList);

  Trace("sygus-infer") << "...return : " << body << std::endl;

  // replace all assertions except the first with true
  Node truen = nm->mkConst(true);
  for (unsigned i = 0, size = assertions.size(); i < size; i++)
  {
    if (i == 0)
    {
      assertions[i] = body;
    }
    else
    {
      assertions[i] = truen;
    }
  }
  return true;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
