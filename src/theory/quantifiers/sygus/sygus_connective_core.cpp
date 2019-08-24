/*********************                                                        */
/*! \file sygus_connective_core.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus connective core utility.
 **/

#include "theory/quantifiers/sygus/sygus_connective_core.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool FalseCoreTrie::add(Node n, std::vector<Node>& i)
{
  FalseCoreTrie* curr = this;
  for (const Node& ic : i)
  {
    curr = &(curr->d_children[ic]);
  }
  if (curr->d_data.isNull())
  {
    curr->d_data = n;
    return true;
  }
  return false;
}

Node FalseCoreTrie::getExclusion(
    std::unordered_set<Node, NodeHashFunction>& excAsserts,
    std::vector<Node>& ctx) const
{
  if (!d_data.isNull())
  {
    Assert(!ctx.empty());
    unsigned index = Random::getRandom().pick(0, ctx.size() - 1);
    Node e = ctx[index];
    return ctx[index];
  }
  std::vector<Node> toExclude;
  for (const std::pair<const Node, FalseCoreTrie>& p : d_children)
  {
    if (excAsserts.find(p.first) != excAsserts.end())
    {
      // already excluded this branch
      continue;
    }
    ctx.push_back(p.first);
    Node ec = p.second.getExclusion(excAsserts, ctx);
    ctx.pop_back();
    if (!ec.isNull())
    {
      if (std::find(ctx.begin(), ctx.end(), ec) != ctx.end())
      {
        // excluded for all
        Assert(excAsserts.find(ec) == excAsserts.end());
        excAsserts.insert(ec);
        return ec;
      }
      else
      {
        toExclude.push_back(ec);
      }
    }
  }
  for (const Node& e : toExclude)
  {
    Assert(excAsserts.find(e) == excAsserts.end());
    excAsserts.insert(e);
  }
  return Node::null();
}

SygusConnectiveCore::SygusConnectiveCore(QuantifiersEngine* qe,
                                         SynthConjecture* p)
    : Cegis(qe, p)
{
}

bool SygusConnectiveCore::processInitialize(Node conj,
                                            Node n,
                                            const std::vector<Node>& candidates,
                                            std::vector<Node>& lemmas)
{
  Trace("sygus-ccore") << "SygusConnectiveCore::initialize" << std::endl;
  Trace("sygus-ccore") << "  conjecture : " << conj << std::endl;
  Trace("sygus-ccore") << "  candidates : " << candidates << std::endl;
  if (candidates.size() != 1)
  {
    Trace("sygus-ccore") << "...only applies to single candidate conjectures."
                         << std::endl;
    return false;
  }
  d_candidate = candidates[0];
  Assert(conj.getKind() == FORALL);
  Node body = conj[1];
  if (body.getKind() == NOT && body[0].getKind() == FORALL)
  {
    body = body[0][1];
  }
  else
  {
    body = TermUtil::simpleNegate(body);
  }
  Trace("sygus-ccore") << "  body : " << body << std::endl;

  TransitionInference ti;
  ti.process(body);

  if (!ti.isComplete())
  {
    Trace("sygus-ccore") << "...could not infer predicate." << std::endl;
    return false;
  }
  Node trans = ti.getTransitionRelation();
  Trace("sygus-ccore") << "  transition relation: " << trans << std::endl;
  if (!trans.isConst() || trans.getConst<bool>())
  {
    Trace("sygus-ccore")
        << "...does not apply conjectures with transition relations."
        << std::endl;
    return false;
  }

  // the grammar must allow AND / OR when applicable
  TypeNode gt = d_candidate.getType();

  Node f = ti.getFunction();
  Assert(!f.isNull());
  Trace("sygus-ccore") << "  predicate: " << f << std::endl;
  ti.getVariables(d_vars);
  Trace("sygus-ccore") << "  variables: " << d_vars << std::endl;
  // make the evaluation function
  std::vector<Node> echildren;
  echildren.push_back(d_candidate);
  echildren.insert(echildren.end(), d_vars.begin(), d_vars.end());
  d_eterm = NodeManager::currentNM()->mkNode(DT_SYGUS_EVAL, echildren);
  Trace("sygus-ccore") << "  evaluation term: " << d_eterm << std::endl;

  d_pre.d_this = ti.getPreCondition();
  d_post.d_this = ti.getPostCondition();
  Trace("sygus-ccore") << "  precondition: " << d_pre.d_this << std::endl;
  Trace("sygus-ccore") << "  postcondition: " << d_post.d_this << std::endl;

  // We use the postcondition if it non-trivial and the grammar gt for our
  // candidate has the production rule gt -> AND( gt, gt ). Similarly for
  // precondition and OR.
  Assert(gt.isDatatype());
  const Datatype& gdt = gt.getDatatype();
  for (unsigned r = 0; r < 2; r++)
  {
    Component& c = r == 0 ? d_pre : d_post;
    if (c.d_this.isConst())
    {
      continue;
    }
    Kind rk = r == 0 ? OR : AND;
    int i = d_tds->getKindConsNum(gt, rk);
    if (i != -1 && gdt[i].getNumArgs() == 2
        && TypeNode::fromType(gdt[i].getArgType(0)) == gt
        && TypeNode::fromType(gdt[i].getArgType(1)) == gt)
    {
      Trace("sygus-ccore") << "  will do " << (r == 0 ? "pre" : "post")
                           << "condition." << std::endl;
      c.d_scons = Node::fromExpr(gdt[i].getConstructor());
      // register the symmetry breaking lemma
      // TODO
    }
  }
  if (!isActive())
  {
    return false;
  }
  // initialize the enumerator
  return Cegis::processInitialize(conj, n, candidates, lemmas);
}

bool SygusConnectiveCore::processConstructCandidates(
    const std::vector<Node>& enums,
    const std::vector<Node>& enum_values,
    const std::vector<Node>& candidates,
    std::vector<Node>& candidate_values,
    bool satisfiedRl,
    std::vector<Node>& lems)
{
  Assert(isActive());
  if (constructSolution(enums, enum_values, candidate_values))
  {
    return true;
  }
  // no special candidate, try the default
  // return Cegis::processConstructCandidates(
  //   enums, enum_values, candidates, candidate_values, satisfiedRl, lems);
  return false;
}

bool SygusConnectiveCore::isActive() const
{
  return d_pre.isActive() || d_post.isActive();
}

bool SygusConnectiveCore::constructSolution(
    const std::vector<Node>& candidates,
    const std::vector<Node>& candidate_values,
    std::vector<Node>& solv)
{
  // if the conjecture is not the right shape, no repair is possible
  if (!isActive())
  {
    return false;
  }
  Assert(candidates.size() == candidate_values.size());
  if (Trace.isOn("sygus-ccore"))
  {
    Trace("sygus-ccore")
        << "SygusConnectiveCore: Construct candidate solutions..." << std::endl;
    Printer* p = Printer::getPrinter(options::outputLanguage());
    for (unsigned i = 0, size = candidates.size(); i < size; i++)
    {
      std::stringstream ss;
      p->toStreamSygus(ss, candidate_values[i]);
      Trace("sygus-ccore") << "  " << candidates[i] << " -> " << ss.str()
                           << std::endl;
    }
  }
  Assert(candidates.size() == 1 && candidates[0] == d_candidate);
  TNode cval = candidate_values[0];
  Node ets = d_eterm.substitute(d_candidate, cval);
  Node etsr = Rewriter::rewrite(ets);
  Trace("sygus-ccore-debug") << "Predicate is: " << etsr << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned r = 0; r < 2; r++)
  {
    Component& ccheck = r == 0 ? d_pre : d_post;
    if (!ccheck.isActive())
    {
      // not trying this direction
      continue;
    }
    if (cval.getOperator() == ccheck.d_scons)
    {
      // Do not use composite values, i.e. (AND a b) since we already process
      // a and b separately.
      continue;
    }
    Component& cfilter = r == 0 ? d_post : d_pre;
    Node fpred = cfilter.d_this;
    if (!fpred.isConst())
    {
      Node etsrn = r == 0 ? etsr : etsr.negate();
      Trace("sygus-ccore-debug")
          << "Check filter " << fpred << " ^ " << etsrn << "..." << std::endl;
      SmtEngine filterSmt(nm->toExprManager());
      filterSmt.setIsInternalSubsolver();
      filterSmt.setLogic(smt::currentSmtEngine()->getLogicInfo());
      filterSmt.assertFormula(fpred.toExpr());
      filterSmt.assertFormula(etsrn.toExpr());
      Result r = filterSmt.checkSat();
      Trace("sygus-ccore-debug") << "...got " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        // failed the filter
        continue;
      }
    }
    Trace("sygus-ccore-debug") << "Add to pool in direction " << r << std::endl;
    ccheck.d_cpool.push_back(etsr);
    ccheck.d_cpoolToSol[etsr] = cval;

    // ----- get the pool of assertions
    // exclude one assertion from every false core
    std::unordered_set<Node, NodeHashFunction> excAsserts;
    std::vector<Node> ctx;
    ccheck.d_falseCores.getExclusion(excAsserts, ctx);
    Trace("sygus-ccore-debug")
        << "Excluded " << excAsserts.size() << " assertions for "
        << ccheck.d_numFalseCores << " false cores." << std::endl;
    std::vector<Node> passerts;
    for (const Node& a : ccheck.d_cpool)
    {
      if (excAsserts.find(a) == excAsserts.end())
      {
        passerts.push_back(a);
      }
    }
    std::shuffle(passerts.begin(), passerts.end(), Random::getRandom());

    // ----- check for entailment, adding based on models of failed points
    std::vector<Node> asserts;
    asserts.push_back(etsr);
    Node an = etsr;
    std::vector<Node> mvs;
    std::unordered_set<Node, NodeHashFunction> visited;
    bool addSuccess = true;
    // Ensure that the current conjunction evaluates to false on all refinement
    // points. We get refinement points until we have exhausted.
    Node mvId;
    do
    {
      mvs.clear();
      Node mvId = ccheck.getRefinementPt(an, visited, d_vars, mvs);
      if (!mvId.isNull())
      {
        addSuccess = addToAsserts(passerts, mvs, mvId, asserts, an);
      }
    } while (!mvId.isNull() && addSuccess);

    do
    {
      addSuccess = false;
      // try a new core
      SmtEngine checkCoreSmt(nm->toExprManager());
      checkCoreSmt.setIsInternalSubsolver();
      checkCoreSmt.setLogic(smt::currentSmtEngine()->getLogicInfo());

      // do the check
      Node query = nm->mkNode(AND, an, ccheck.d_this);
      query = Rewriter::rewrite(query);

      checkCoreSmt.assertFormula(query.toExpr());
      Result r = checkCoreSmt.checkSat();
      Trace("sygus-ccore-debug") << "...got " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        // it entails the postcondition
        // check whether it is a false core  TODO

        Node sol = ccheck.getSygusSolution(asserts);
        Trace("sygus-ccore-sy") << "Sygus solution : " << sol << std::endl;
        if (ccheck.d_tried.find(sol) == ccheck.d_tried.end())
        {
          ccheck.d_tried.insert(sol);
        }
      }
      else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        // it does not entail the postcondition, add an assertion that blocks
        // the current point
        mvs.clear();
        getModel(checkCoreSmt, mvs);
        ccheck.d_refinementPt.addTerm(query, mvs);
        addSuccess = addToAsserts(passerts, mvs, query, asserts, an);
      }
    } while (addSuccess);
  }
  Trace("sygus-ccore") << "...failed to generate candidate" << std::endl;
  return false;
}

Node SygusConnectiveCore::Component::getSygusSolution(
    std::vector<Node>& conjs) const
{
  std::sort(conjs.begin(), conjs.end());
  Node sol;
  std::map<Node, Node>::const_iterator itu;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& u : conjs)
  {
    itu = d_cpoolToSol.find(u);
    Assert(itu != d_cpoolToSol.end());
    Node s = itu->second;
    Trace("sygus-ccore-debug-sy") << "  uc-s " << s << std::endl;
    if (sol.isNull())
    {
      sol = s;
    }
    else
    {
      sol = nm->mkNode(APPLY_CONSTRUCTOR, d_scons, s, sol);
    }
  }
  return sol;
}

Node SygusConnectiveCore::Component::getRefinementPt(
    Node n,
    std::unordered_set<Node, NodeHashFunction>& visited,
    const std::vector<Node>& vs,
    std::vector<Node>& ss)
{
  std::vector<Node> ctx;

  std::map<NodeTrie*, std::map<Node, NodeTrie>::iterator> vt;
  std::map<NodeTrie*, std::map<Node, NodeTrie>::iterator>::iterator itvt;
  std::vector<NodeTrie*> visit;
  NodeTrie* cur;
  visit.push_back(&d_refinementPt);
  do
  {
    cur = visit.back();
    if (ctx.size() == vs.size())
    {
      // at leaf
      Node id = cur->getData();
      if (visited.find(id) == visited.end())
      {
        visited.insert(id);
        // check if it is true
        Node sn = n.substitute(vs.begin(), vs.end(), ctx.begin(), ctx.end());
        sn = Rewriter::rewrite(sn);
        if (sn.isConst() && sn.getConst<bool>())
        {
          ss = ctx;
          return id;
        }
      }
      visit.pop_back();
      ctx.pop_back();
    }
    else
    {
      itvt = vt.find(cur);
      if (itvt == vt.begin())
      {
        std::map<Node, NodeTrie>::iterator itv = cur->d_data.begin();
        vt[cur] = itv;
        vt.find(cur);
      }
      if (itvt == vt.end())
      {
        visit.pop_back();
        vt.erase(cur);
        ctx.pop_back();
      }
      else
      {
        ctx.push_back(itvt->second->first);
        visit.push_back(&(itvt->second->second));
        ++vt[cur];
      }
    }

  } while (!visit.empty());
  return Node::null();
}

bool SygusConnectiveCore::addToAsserts(std::vector<Node>& passerts,
                                       const std::vector<Node>& mvs,
                                       Node mvId,
                                       std::vector<Node>& asserts,
                                       Node& an)
{
  // point should be valid
  Assert(!mvId.isNull());
  Node n;
  // select condition from passerts that evaluates to false on mvs
  for (unsigned i = 0, psize = passerts.size(); i < psize; i++)
  {
    Node cn = passerts[i];
    Node cne = evaluate(cn, mvId, mvs);
    if (cne.isConst() && !cne.getConst<bool>())
    {
      n = cn;
      // remove n from the pool
      passerts.erase(passerts.begin() + i, passerts.begin() + i + 1);
      break;
    }
  }
  if (!n.isNull())
  {
    asserts.push_back(n);
    an = NodeManager::currentNM()->mkNode(AND, n, an);
    return true;
  }
  passerts.clear();
  return false;
}

void SygusConnectiveCore::getModel(SmtEngine& smt, std::vector<Node>& vals)
{
  for (const Node& v : d_vars)
  {
    Node mv = Node::fromExpr(smt.getValue(v.toExpr()));
    Trace("sygus-ccore-model") << v << " -> " << mv << " ";
    vals.push_back(mv);
  }
}

Node SygusConnectiveCore::evaluate(Node n, Node id, const std::vector<Node>& mvs)
{
  std::unordered_map<Node, Node, NodeHashFunction>& ec = d_eval_cache[n];
  std::unordered_map<Node, Node, NodeHashFunction>::iterator it = ec.find(id);
  if (it != ec.end())
  {
    return it->second;
  }
  // TODO: use evaluator
  Node cn = n.substitute(d_vars.begin(), d_vars.end(), mvs.begin(), mvs.end());
  cn = Rewriter::rewrite(cn);
  ec[id] = cn;
  return cn;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
