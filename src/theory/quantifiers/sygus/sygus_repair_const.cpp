/*********************                                                        */
/*! \file sygus_repair_const.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_repair_const
 **/

#include "theory/quantifiers/sygus/sygus_repair_const.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/datatypes/datatypes_rewriter.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SygusRepairConst::SygusRepairConst(QuantifiersEngine* qe)
    : d_qe(qe), d_allow_constant_grammar(false)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

void SygusRepairConst::initialize(Node base_inst,
                                  const std::vector<Node>& candidates)
{
  Trace("sygus-repair-const") << "SygusRepairConst::initialize" << std::endl;
  Trace("sygus-repair-const") << "  conjecture : " << base_inst << std::endl;
  d_base_inst = base_inst;

  // compute whether there are "allow all constant" types in the variables of q
  std::map<TypeNode, bool> tprocessed;
  for (const Node& v : candidates)
  {
    TypeNode tn = v.getType();
    // do the type traversal of the sygus type
    registerSygusType(tn, tprocessed);
  }
  Trace("sygus-repair-const")
      << "  allow constants : " << d_allow_constant_grammar << std::endl;
}

// recursion depth bounded by number of types in grammar (small)
void SygusRepairConst::registerSygusType(TypeNode tn,
                                         std::map<TypeNode, bool>& tprocessed)
{
  if (tprocessed.find(tn) == tprocessed.end())
  {
    tprocessed[tn] = true;
    if (!tn.isDatatype())
    {
      // may have recursed to a non-datatype, e.g. in the case that we have
      // "any constant" constructors
      return;
    }
    const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
    if (!dt.isSygus())
    {
      // may have recursed to a non-sygus-datatype
      return;
    }
    // check if this datatype allows all constants
    if (dt.getSygusAllowConst())
    {
      d_allow_constant_grammar = true;
    }
    for (unsigned i = 0, ncons = dt.getNumConstructors(); i < ncons; i++)
    {
      const DatatypeConstructor& dtc = dt[i];
      // recurse on all subfields
      for (unsigned j = 0, nargs = dtc.getNumArgs(); j < nargs; j++)
      {
        TypeNode tnc = d_tds->getArgType(dtc, j);
        registerSygusType(tnc, tprocessed);
      }
    }
  }
}

bool SygusRepairConst::isActive() const
{
  return !d_base_inst.isNull() && d_allow_constant_grammar;
}

void SygusRepairConst::initializeChecker(std::unique_ptr<SmtEngine>& checker,
                                         ExprManager& em,
                                         ExprManagerMapCollection& varMap,
                                         Node query,
                                         bool& needExport)
{
  NodeManager* nm = NodeManager::currentNM();
  if (options::sygusRepairConstTimeout.wasSetByUser())
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
      checker->setTimeLimit(options::sygusRepairConstTimeout(), true);
      checker->setLogic(smt::currentSmtEngine()->getLogicInfo());
      // renable options disabled by sygus
      checker->setOption("miniscope-quant", true);
      checker->setOption("miniscope-quant-fv", true);
      checker->setOption("quant-split", true);
      // export
      Expr e_query = query.toExpr().exportTo(&em, varMap);
      checker->assertFormula(e_query);
    }
    catch (const CVC4::ExportUnsupportedException& e)
    {
      std::stringstream msg;
      msg << "Unable to export " << query
          << " but exporting expressions is required for "
             "--sygus-repair-const-timeout.";
      throw OptionException(msg.str());
    }
  }
  else
  {
    needExport = false;
    checker.reset(new SmtEngine(nm->toExprManager()));
    checker->assertFormula(query.toExpr());
  }
}

bool SygusRepairConst::repairSolution(const std::vector<Node>& candidates,
                                      const std::vector<Node>& candidate_values,
                                      std::vector<Node>& repair_cv,
                                      bool useConstantsAsHoles)
{
  return repairSolution(d_base_inst,
                        candidates,
                        candidate_values,
                        repair_cv,
                        useConstantsAsHoles);
}

bool SygusRepairConst::repairSolution(Node sygusBody,
                                      const std::vector<Node>& candidates,
                                      const std::vector<Node>& candidate_values,
                                      std::vector<Node>& repair_cv,
                                      bool useConstantsAsHoles)
{
  Assert(candidates.size() == candidate_values.size());

  // if no grammar type allows constants, no repair is possible
  if (!isActive())
  {
    return false;
  }
  if (Trace.isOn("sygus-repair-const"))
  {
    Trace("sygus-repair-const") << "Repair candidate solutions..." << std::endl;
    Printer* p = Printer::getPrinter(options::outputLanguage());
    for (unsigned i = 0, size = candidates.size(); i < size; i++)
    {
      std::stringstream ss;
      p->toStreamSygus(ss, candidate_values[i]);
      Trace("sygus-repair-const")
          << "  " << candidates[i] << " -> " << ss.str() << std::endl;
    }
    Trace("sygus-repair-const")
        << "Getting candidate skeletons : " << std::endl;
  }
  std::vector<Node> candidate_skeletons;
  std::map<TypeNode, int> free_var_count;
  std::vector<Node> sk_vars;
  std::map<Node, Node> sk_vars_to_subs;
  for (unsigned i = 0, size = candidates.size(); i < size; i++)
  {
    Node cv = candidate_values[i];
    Node skeleton = getSkeleton(
        cv, free_var_count, sk_vars, sk_vars_to_subs, useConstantsAsHoles);
    if (Trace.isOn("sygus-repair-const"))
    {
      Printer* p = Printer::getPrinter(options::outputLanguage());
      std::stringstream ss;
      p->toStreamSygus(ss, cv);
      Trace("sygus-repair-const")
          << "Solution #" << i << " : " << ss.str() << std::endl;
      if (skeleton == cv)
      {
        Trace("sygus-repair-const") << "...solution unchanged" << std::endl;
      }
      else
      {
        std::stringstream sss;
        p->toStreamSygus(sss, skeleton);
        Trace("sygus-repair-const")
            << "...inferred skeleton : " << sss.str() << std::endl;
      }
    }
    candidate_skeletons.push_back(skeleton);
  }

  if (sk_vars.empty())
  {
    Trace("sygus-repair-const") << "...no solutions repaired." << std::endl;
    return false;
  }

  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-repair-const") << "Get first-order query..." << std::endl;
  Node fo_body =
      getFoQuery(sygusBody, candidates, candidate_skeletons, sk_vars);

  Trace("sygus-repair-const-debug") << "...got : " << fo_body << std::endl;

  if (d_queries.find(fo_body) != d_queries.end())
  {
    Trace("sygus-repair-const") << "...duplicate query." << std::endl;
    return false;
  }
  d_queries.insert(fo_body);

  // check whether it is not in the current logic, e.g. non-linear arithmetic.
  // if so, undo replacements until it is in the current logic.
  LogicInfo logic = smt::currentSmtEngine()->getLogicInfo();
  if (logic.isTheoryEnabled(THEORY_ARITH) && logic.isLinear())
  {
    fo_body = fitToLogic(sygusBody,
                         logic,
                         fo_body,
                         candidates,
                         candidate_skeletons,
                         sk_vars,
                         sk_vars_to_subs);
  }

  if (fo_body.isNull() || sk_vars.empty())
  {
    Trace("sygus-repair-const")
        << "...all skeleton variables lead to bad logic." << std::endl;
    return false;
  }

  Trace("sygus-repair-const") << "Make satisfiabily query..." << std::endl;
  if (fo_body.getKind() == FORALL)
  {
    // must be a CBQI quantifier
    CegHandledStatus hstatus = CegInstantiator::isCbqiQuant(fo_body, d_qe);
    if (hstatus < CEG_HANDLED)
    {
      // abort if less than fully handled
      Trace("sygus-repair-const") << "...first-order query is not handlable by "
                                     "counterexample-guided instantiation."
                                  << std::endl;
      return false;
    }
  }

  Trace("cegqi-engine") << "Repairing previous solution..." << std::endl;
  // make the satisfiability query
  bool needExport = true;
  ExprManagerMapCollection varMap;
  ExprManager em(nm->getOptions());
  std::unique_ptr<SmtEngine> repcChecker;
  initializeChecker(repcChecker, em, varMap, fo_body, needExport);
  Result r = repcChecker->checkSat();
  Trace("sygus-repair-const") << "...got : " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::UNSAT
      || r.asSatisfiabilityResult().isUnknown())
  {
    Trace("cegqi-engine") << "...failed" << std::endl;
    return false;
  }
  std::vector<Node> sk_sygus_m;
  for (const Node& v : sk_vars)
  {
    Assert(d_sk_to_fo.find(v) != d_sk_to_fo.end());
    Node fov = d_sk_to_fo[v];
    Node fov_m;
    if (needExport)
    {
      Expr e_fov = fov.toExpr().exportTo(&em, varMap);
      fov_m = Node::fromExpr(
          repcChecker->getValue(e_fov).exportTo(nm->toExprManager(), varMap));
    }
    else
    {
      fov_m = Node::fromExpr(repcChecker->getValue(fov.toExpr()));
    }
    Trace("sygus-repair-const") << "  " << fov << " = " << fov_m << std::endl;
    // convert to sygus
    Node fov_m_to_sygus = d_tds->getProxyVariable(v.getType(), fov_m);
    sk_sygus_m.push_back(fov_m_to_sygus);
  }
  std::stringstream ss;
  // convert back to sygus
  for (unsigned i = 0, size = candidates.size(); i < size; i++)
  {
    Node csk = candidate_skeletons[i];
    Node scsk = csk.substitute(
        sk_vars.begin(), sk_vars.end(), sk_sygus_m.begin(), sk_sygus_m.end());
    repair_cv.push_back(scsk);
    if (Trace.isOn("sygus-repair-const") || Trace.isOn("cegqi-engine"))
    {
      std::stringstream sss;
      Printer::getPrinter(options::outputLanguage())
          ->toStreamSygus(sss, repair_cv[i]);
      ss << "  * " << candidates[i] << " -> " << sss.str() << std::endl;
    }
  }
  Trace("cegqi-engine") << "...success:" << std::endl;
  Trace("cegqi-engine") << ss.str();
  Trace("sygus-repair-const")
      << "Repaired constants in solution : " << std::endl;
  Trace("sygus-repair-const") << ss.str();
  return true;
}

bool SygusRepairConst::mustRepair(Node n)
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Assert(cur.getKind() == APPLY_CONSTRUCTOR);
      if (isRepairable(cur, false))
      {
        return true;
      }
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());

  return false;
}

bool SygusRepairConst::isRepairable(Node n, bool useConstantsAsHoles)
{
  if (n.getKind() != APPLY_CONSTRUCTOR)
  {
    return false;
  }
  TypeNode tn = n.getType();
  Assert(tn.isDatatype());
  const Datatype& dt = static_cast<DatatypeType>(tn.toType()).getDatatype();
  if (!dt.isSygus())
  {
    return false;
  }
  Node op = n.getOperator();
  unsigned cindex = datatypes::DatatypesRewriter::indexOf(op);
  Node sygusOp = Node::fromExpr(dt[cindex].getSygusOp());
  if (sygusOp.getAttribute(SygusAnyConstAttribute()))
  {
    // if it represents "any constant" then it is repairable
    return true;
  }
  if (dt[cindex].getNumArgs() > 0)
  {
    return false;
  }
  if (useConstantsAsHoles && dt.getSygusAllowConst())
  {
    if (sygusOp.isConst())
    {
      // if a constant, it is repairable
      return true;
    }
  }
  return false;
}

Node SygusRepairConst::getSkeleton(Node n,
                                   std::map<TypeNode, int>& free_var_count,
                                   std::vector<Node>& sk_vars,
                                   std::map<Node, Node>& sk_vars_to_subs,
                                   bool useConstantsAsHoles)
{
  if (isRepairable(n, useConstantsAsHoles))
  {
    Node sk_var = d_tds->getFreeVarInc(n.getType(), free_var_count);
    sk_vars.push_back(sk_var);
    sk_vars_to_subs[sk_var] = n;
    Trace("sygus-repair-const-debug")
        << "Var to subs : " << sk_var << " -> " << n << std::endl;
    return sk_var;
  }
  NodeManager* nm = NodeManager::currentNM();
  // get the most general candidate skeleton of n
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const Node& cn : cur)
      {
        visit.push_back(cn);
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        Node child;
        // if it is repairable
        if (isRepairable(cn, useConstantsAsHoles))
        {
          // replace it by the next free variable
          child = d_tds->getFreeVarInc(cn.getType(), free_var_count);
          sk_vars.push_back(child);
          sk_vars_to_subs[child] = cn;
          Trace("sygus-repair-const-debug")
              << "Var to subs : " << child << " -> " << cn << std::endl;
        }
        else
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          child = it->second;
        }
        childChanged = childChanged || cn != child;
        children.push_back(child);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node SygusRepairConst::getFoQuery(Node body,
                                  const std::vector<Node>& candidates,
                                  const std::vector<Node>& candidate_skeletons,
                                  const std::vector<Node>& sk_vars)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-repair-const") << "  Substitute skeletons..." << std::endl;
  body = body.substitute(candidates.begin(),
                         candidates.end(),
                         candidate_skeletons.begin(),
                         candidate_skeletons.end());
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;

  Trace("sygus-repair-const") << "  Unfold the specification..." << std::endl;
  body = d_tds->evaluateWithUnfolding(body);
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;

  Trace("sygus-repair-const") << "  Introduce first-order vars..." << std::endl;
  for (const Node& v : sk_vars)
  {
    std::map<Node, Node>::iterator itf = d_sk_to_fo.find(v);
    if (itf == d_sk_to_fo.end())
    {
      TypeNode builtinType = d_tds->sygusToBuiltinType(v.getType());
      Node sk_fov = nm->mkSkolem("k", builtinType);
      d_sk_to_fo[v] = sk_fov;
      d_fo_to_sk[sk_fov] = v;
      Trace("sygus-repair-const-debug")
          << "Map " << v << " -> " << sk_fov << std::endl;
    }
  }
  // now, we must replace all terms of the form eval( z_i, t1...tn ) with
  // a fresh first-order variable w_i, where z_i is a variable introduced in
  // the skeleton inference step (z_i is a variable in sk_vars).
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(body);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      if (cur.getKind() == DT_SYGUS_EVAL)
      {
        Node v = cur[0];
        if (std::find(sk_vars.begin(), sk_vars.end(), v) != sk_vars.end())
        {
          std::map<Node, Node>::iterator itf = d_sk_to_fo.find(v);
          Assert(itf != d_sk_to_fo.end());
          visited[cur] = itf->second;
        }
      }
      if (visited[cur].isNull())
      {
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(body) != visited.end());
  Assert(!visited.find(body)->second.isNull());
  Node fo_body = visited[body];
  Trace("sygus-repair-const-debug") << "  ...got : " << fo_body << std::endl;
  return fo_body;
}

Node SygusRepairConst::fitToLogic(Node body,
                                  LogicInfo& logic,
                                  Node n,
                                  const std::vector<Node>& candidates,
                                  std::vector<Node>& candidate_skeletons,
                                  std::vector<Node>& sk_vars,
                                  std::map<Node, Node>& sk_vars_to_subs)
{
  std::vector<Node> rm_var;
  Node exc_var;
  while (getFitToLogicExcludeVar(logic, n, exc_var))
  {
    if (exc_var.isNull())
    {
      return n;
    }
    Trace("sygus-repair-const") << "...exclude " << exc_var
                                << " due to logic restrictions." << std::endl;
    TNode tvar = exc_var;
    Assert(sk_vars_to_subs.find(exc_var) != sk_vars_to_subs.end());
    TNode tsubs = sk_vars_to_subs[exc_var];
    // revert the substitution
    for (unsigned i = 0, size = candidate_skeletons.size(); i < size; i++)
    {
      candidate_skeletons[i] = candidate_skeletons[i].substitute(tvar, tsubs);
    }
    // remove the variable
    sk_vars_to_subs.erase(exc_var);
    std::vector<Node>::iterator it =
        std::find(sk_vars.begin(), sk_vars.end(), exc_var);
    Assert(it != sk_vars.end());
    sk_vars.erase(it);
    // reconstruct the query
    n = getFoQuery(body, candidates, candidate_skeletons, sk_vars);
    // reset the exclusion variable
    exc_var = Node::null();
  }
  return Node::null();
}

bool SygusRepairConst::getFitToLogicExcludeVar(LogicInfo& logic,
                                               Node n,
                                               Node& exvar)
{
  bool restrictLA = logic.isTheoryEnabled(THEORY_ARITH) && logic.isLinear();

  // should have at least one restriction
  Assert(restrictLA);

  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::unordered_set<TNode, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      bool isArithDivKind = (ck == DIVISION_TOTAL || ck == INTS_DIVISION_TOTAL
                             || ck == INTS_MODULUS_TOTAL);
      Assert(ck != DIVISION && ck != INTS_DIVISION && ck != INTS_MODULUS);
      if (restrictLA && (ck == NONLINEAR_MULT || isArithDivKind))
      {
        for (unsigned j = 0, size = cur.getNumChildren(); j < size; j++)
        {
          Node ccur = cur[j];
          std::map<Node, Node>::iterator itf = d_fo_to_sk.find(ccur);
          if (itf != d_fo_to_sk.end())
          {
            if (ck == NONLINEAR_MULT || (isArithDivKind && j == 1))
            {
              exvar = itf->second;
              return true;
            }
          }
        }
        return false;
      }
      for (const Node& ccur : cur)
      {
        visit.push_back(ccur);
      }
    }
  } while (!visit.empty());

  return true;
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
