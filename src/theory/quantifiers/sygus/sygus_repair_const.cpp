/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sygus_repair_const.
 */

#include "theory/quantifiers/sygus/sygus_repair_const.h"

#include "expr/dtype_cons.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "printer/printer.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/cegqi/ceg_instantiator.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusRepairConst::SygusRepairConst(Env& env, TermDbSygus* tds)
    : EnvObj(env), d_tds(tds), d_allow_constant_grammar(false)
{
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
    const DType& dt = tn.getDType();
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
      const DTypeConstructor& dtc = dt[i];
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
  if (TraceIsOn("sygus-repair-const"))
  {
    Trace("sygus-repair-const") << "Repair candidate solutions..." << std::endl;
    for (unsigned i = 0, size = candidates.size(); i < size; i++)
    {
      std::stringstream ss;
      TermDbSygus::toStreamSygus(ss, candidate_values[i]);
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
    if (TraceIsOn("sygus-repair-const"))
    {
      std::stringstream ss;
      TermDbSygus::toStreamSygus(ss, cv);
      Trace("sygus-repair-const")
          << "Solution #" << i << " : " << ss.str() << std::endl;
      if (skeleton == cv)
      {
        Trace("sygus-repair-const") << "...solution unchanged" << std::endl;
      }
      else
      {
        std::stringstream sss;
        TermDbSygus::toStreamSygus(sss, skeleton);
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
  const LogicInfo& logic = logicInfo();
  if (logic.isTheoryEnabled(THEORY_ARITH) && logic.isLinear())
  {
    fo_body = fitToLogic(sygusBody,
                         logic,
                         fo_body,
                         candidates,
                         candidate_skeletons,
                         sk_vars,
                         sk_vars_to_subs);
    Trace("sygus-repair-const-debug")
        << "...after fit-to-logic : " << fo_body << std::endl;
  }
  Assert(!expr::hasFreeVar(fo_body));

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
    CegHandledStatus hstatus =
        CegInstantiator::isCbqiQuant(fo_body, options().quantifiers.cegqiAll);
    if (hstatus < CEG_HANDLED)
    {
      // abort if less than fully handled
      Trace("sygus-repair-const") << "...first-order query is not handlable by "
                                     "counterexample-guided instantiation."
                                  << std::endl;
      return false;
    }
  }

  Trace("sygus-engine") << "Repairing previous solution..." << std::endl;
  // make the satisfiability query
  std::unique_ptr<SolverEngine> repcChecker;
  SubsolverSetupInfo ssi(d_env);
  // initialize the subsolver using the standard method
  initializeSubsolver(repcChecker,
                      ssi,
                      options().quantifiers.sygusRepairConstTimeoutWasSetByUser,
                      options().quantifiers.sygusRepairConstTimeout);
  // renable options disabled by sygus
  repcChecker->setOption("miniscope-quant", "conj-and-fv");
  repcChecker->assertFormula(fo_body);
  // check satisfiability
  Result r = repcChecker->checkSat();
  Trace("sygus-repair-const") << "...got : " << r << std::endl;
  if (r.getStatus() == Result::UNSAT || r.isUnknown())
  {
    Trace("sygus-engine") << "...failed" << std::endl;
    return false;
  }
  std::vector<Node> sk_sygus_m;
  for (const Node& v : sk_vars)
  {
    Assert(d_sk_to_fo.find(v) != d_sk_to_fo.end());
    Node fov = d_sk_to_fo[v];
    Node fov_m = repcChecker->getValue(fov);
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
    if (TraceIsOn("sygus-repair-const") || TraceIsOn("sygus-engine"))
    {
      std::stringstream sss;
      TermDbSygus::toStreamSygus(sss, repair_cv[i]);
      ss << "  * " << candidates[i] << " -> " << sss.str() << std::endl;
    }
  }
  Trace("sygus-engine") << "...success:" << std::endl;
  Trace("sygus-engine") << ss.str();
  Trace("sygus-repair-const")
      << "Repaired constants in solution : " << std::endl;
  Trace("sygus-repair-const") << ss.str();
  return true;
}

bool SygusRepairConst::mustRepair(Node n)
{
  std::unordered_set<TNode> visited;
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
  const DType& dt = tn.getDType();
  if (!dt.isSygus())
  {
    return false;
  }
  Node op = n.getOperator();
  unsigned cindex = datatypes::utils::indexOf(op);
  if (dt[cindex].isSygusAnyConstant())
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
    if (dt[cindex].getSygusOp().isConst())
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
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
  SkolemManager* sm = nm->getSkolemManager();
  Trace("sygus-repair-const") << "  Substitute skeletons..." << std::endl;
  body = body.substitute(candidates.begin(),
                         candidates.end(),
                         candidate_skeletons.begin(),
                         candidate_skeletons.end());
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;

  Trace("sygus-repair-const") << "  Unfold the specification..." << std::endl;
  body = d_tds->rewriteNode(body);
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;

  Trace("sygus-repair-const") << "  Introduce first-order vars..." << std::endl;
  for (const Node& v : sk_vars)
  {
    std::map<Node, Node>::iterator itf = d_sk_to_fo.find(v);
    if (itf == d_sk_to_fo.end())
    {
      TypeNode builtinType = d_tds->sygusToBuiltinType(v.getType());
      Node sk_fov = sm->mkDummySkolem("k", builtinType);
      d_sk_to_fo[v] = sk_fov;
      d_fo_to_sk[sk_fov] = v;
      Trace("sygus-repair-const-debug")
          << "Map " << v << " -> " << sk_fov << std::endl;
    }
  }
  // now, we must replace all terms of the form eval( z_i, t1...tn ) with
  // a fresh first-order variable w_i, where z_i is a variable introduced in
  // the skeleton inference step (z_i is a variable in sk_vars).
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
                                  const LogicInfo& logic,
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

bool SygusRepairConst::getFitToLogicExcludeVar(const LogicInfo& logic,
                                               Node n,
                                               Node& exvar)
{
  bool restrictLA = logic.isTheoryEnabled(THEORY_ARITH) && logic.isLinear();

  // should have at least one restriction
  Assert(restrictLA);

  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
