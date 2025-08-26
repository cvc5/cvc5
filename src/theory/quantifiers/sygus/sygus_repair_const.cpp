/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/sygus/sygus_grammar_norm.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/smt_engine_subsolver.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SygusRepairConst::SygusRepairConst(Env& env,
                                   QuantifiersInferenceManager& qim,
                                   TermDbSygus* tds)
    : EnvObj(env), d_qim(qim), d_tds(tds), d_allow_constant_grammar(false)
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
                                      std::vector<Node>& repair_cv)
{
  return repairSolution(d_base_inst, candidates, candidate_values, repair_cv);
}

bool SygusRepairConst::repairSolution(Node sygusBody,
                                      const std::vector<Node>& candidates,
                                      const std::vector<Node>& candidate_values,
                                      std::vector<Node>& repair_cv)
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
      Trace("sygus-repair-const")
          << "From " << candidate_values[i] << std::endl;
    }
    Trace("sygus-repair-const")
        << "Getting candidate skeletons : " << std::endl;
  }
  std::vector<Node> candidate_skeletons;
  std::map<TypeNode, size_t> free_var_count;
  std::vector<Node> sk_vars;
  for (unsigned i = 0, size = candidates.size(); i < size; i++)
  {
    Node cv = candidate_values[i];
    Node skeleton = getSkeleton(cv, free_var_count, sk_vars);
    Assert(skeleton.getType() == cv.getType());
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
  Assert(!expr::hasFreeVar(fo_body));

  if (fo_body.isNull() || sk_vars.empty())
  {
    Trace("sygus-repair-const")
        << "...all skeleton variables lead to bad logic." << std::endl;
    return false;
  }
  if (d_queries.find(fo_body) != d_queries.end())
  {
    Trace("sygus-repair-const") << "...duplicate query." << std::endl;
    return false;
  }
  d_queries.insert(fo_body);

  Trace("sygus-repair-const") << "Make satisfiabily query..." << std::endl;
  if (fo_body.getKind() == Kind::FORALL)
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
  // Make the satisfiability query. We use the "ALL" logic, since the subcall
  // may e.g. introduce non-linear arithmetic in linear logics.
  std::unique_ptr<SolverEngine> repcChecker;
  LogicInfo lall("ALL");
  SubsolverSetupInfo ssi(
      d_env.getOptions(), lall, d_env.getSepLocType(), d_env.getSepDataType());
  // initialize the subsolver using the standard method
  initializeSubsolver(nodeManager(),
                      repcChecker,
                      ssi,
                      options().quantifiers.sygusRepairConstTimeoutWasSetByUser,
                      options().quantifiers.sygusRepairConstTimeout);
  // renable options disabled by sygus
  repcChecker->setOption("miniscope-quant", "conj-and-fv");
  repcChecker->assertFormula(fo_body);
  // check satisfiability
  Result r = repcChecker->checkSat();
  Trace("sygus-repair-const") << "...got : " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    d_unsatQueries.insert(fo_body);
    Trace("sygus-engine") << "...failed (unsat)" << std::endl;
    return false;
  }
  else if (r.isUnknown())
  {
    Trace("sygus-engine") << "...failed" << std::endl;
    return false;
  }
  std::vector<Node> sk_sygus_m;
  for (const Node& v : sk_vars)
  {
    Node fov_m = repcChecker->getValue(v);
    Trace("sygus-repair-const") << "  " << v << " = " << fov_m << std::endl;
    // convert to sygus
    sk_sygus_m.push_back(fov_m);
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
      Assert(cur.getKind() == Kind::APPLY_CONSTRUCTOR);
      if (isRepairable(cur))
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

bool SygusRepairConst::isRepairable(Node n)
{
  if (n.getKind() != Kind::APPLY_CONSTRUCTOR)
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
  // if it represents "any constant" then it is repairable
  return dt[cindex].isSygusAnyConstant();
}

Node SygusRepairConst::getSkeleton(Node n,
                                   std::map<TypeNode, size_t>& free_var_count,
                                   std::vector<Node>& sk_vars)
{
  NodeManager* nm = nodeManager();
  SkolemManager* skm = nm->getSkolemManager();
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
      if (isRepairable(cur))
      {
        // replace the argument of the any-constant constructor with a skolem
        Node sk_var = d_tds->getFreeVarInc(cur[0].getType(), free_var_count);
        sk_var = skm->mkPurifySkolem(sk_var);
        sk_vars.push_back(sk_var);
        visited[cur] = nm->mkNode(cur.getKind(), cur.getOperator(), sk_var);
        continue;
      }
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
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        Node child = it->second;
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
  Trace("sygus-repair-const") << "  Substitute skeletons..." << std::endl;
  body = body.substitute(candidates.begin(),
                         candidates.end(),
                         candidate_skeletons.begin(),
                         candidate_skeletons.end());
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;

  Trace("sygus-repair-const") << "  Unfold the specification..." << std::endl;
  body = d_tds->rewriteNode(body);
  Trace("sygus-repair-const-debug") << "  ...got : " << body << std::endl;
  return body;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
