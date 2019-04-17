/*********************                                                        */
/*! \file expr_miner.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expr_miner
 **/

#include "theory/quantifiers/expr_miner.h"

#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/term_util.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

void ExprMiner::initialize(const std::vector<Node>& vars, SygusSampler* ss)
{
  d_sampler = ss;
  d_vars.insert(d_vars.end(), vars.begin(), vars.end());
}

Node ExprMiner::convertToSkolem(Node n)
{
  std::vector<Node> fvs;
  TermUtil::computeVarContains(n, fvs);
  if (fvs.empty())
  {
    return n;
  }
  std::vector<Node> sfvs;
  std::vector<Node> sks;
  // map to skolems
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = fvs.size(); i < size; i++)
  {
    Node v = fvs[i];
    // only look at the sampler variables
    if (std::find(d_vars.begin(), d_vars.end(), v) != d_vars.end())
    {
      sfvs.push_back(v);
      std::map<Node, Node>::iterator itf = d_fv_to_skolem.find(v);
      if (itf == d_fv_to_skolem.end())
      {
        Node sk = nm->mkSkolem("rrck", v.getType());
        d_fv_to_skolem[v] = sk;
        sks.push_back(sk);
      }
      else
      {
        sks.push_back(itf->second);
      }
    }
  }
  return n.substitute(sfvs.begin(), sfvs.end(), sks.begin(), sks.end());
}

void ExprMiner::initializeChecker(std::unique_ptr<SmtEngine>& checker,
                                  ExprManager& em,
                                  ExprManagerMapCollection& varMap,
                                  Node query,
                                  bool& needExport)
{
  // Convert bound variables to skolems. This ensures the satisfiability
  // check is ground.
  Node squery = convertToSkolem(query);
  NodeManager* nm = NodeManager::currentNM();
  if (options::sygusExprMinerCheckUseExport())
  {
    // To support a separate timeout for the subsolver, we need to create
    // a separate ExprManager with its own options. This requires that
    // the expressions sent to the subsolver can be exported from on
    // ExprManager to another. If the export fails, we throw an
    // OptionException.
    try
    {
      checker.reset(new SmtEngine(&em));
      checker->setIsInternalSubsolver();
      checker->setTimeLimit(options::sygusExprMinerCheckTimeout(), true);
      checker->setLogic(smt::currentSmtEngine()->getLogicInfo());
      checker->setOption("sygus-rr-synth-input", false);
      checker->setOption("sygus-abduct", false);
      checker->setOption("input-language", "smt2");
      Expr equery = squery.toExpr().exportTo(&em, varMap);
      checker->assertFormula(equery);
    }
    catch (const CVC4::ExportUnsupportedException& e)
    {
      std::stringstream msg;
      msg << "Unable to export " << squery
          << " but exporting expressions is "
             "required for an expression "
             "miner check.";
      throw OptionException(msg.str());
    }
    needExport = true;
  }
  else
  {
    needExport = false;
    checker.reset(new SmtEngine(nm->toExprManager()));
    checker->assertFormula(squery.toExpr());
  }
}

Result ExprMiner::doCheck(Node query)
{
  Node queryr = Rewriter::rewrite(query);
  if (queryr.isConst())
  {
    if (!queryr.getConst<bool>())
    {
      return Result(Result::UNSAT);
    }
    else
    {
      return Result(Result::SAT);
    }
  }
  NodeManager* nm = NodeManager::currentNM();
  bool needExport = false;
  ExprManager em(nm->getOptions());
  std::unique_ptr<SmtEngine> smte;
  ExprManagerMapCollection varMap;
  initializeChecker(smte, em, varMap, queryr, needExport);
  return smte->checkSat();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
