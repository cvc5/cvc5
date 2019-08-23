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
  std::vector<Node> vars;
  ti.getVariables(vars);
  Trace("sygus-ccore") << "  variables: " << vars << std::endl;
  // make the evaluation function
  std::vector<Node> echildren;
  echildren.push_back(d_candidate);
  echildren.insert(echildren.end(), vars.begin(), vars.end());
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
    Trace("sygus-ccore") << "SygusConnectiveCore: Construct candidate solutions..." << std::endl;
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
    if (ccheck.d_cpool.size() <= 1)
    {
      continue;
    }
    bool hadFalseCore;
    do
    {
      hadFalseCore = false;
      Trace("sygus-ccore") << "Check conjunction of " << ccheck.d_cpool.size()
                                  << " pool values..." << std::endl;
      // try a new core
      SmtEngine checkCoreSmt(nm->toExprManager());
      checkCoreSmt.setIsInternalSubsolver();
      checkCoreSmt.setLogic(smt::currentSmtEngine()->getLogicInfo());
      // get the assertions
      // exclude one assertion from every false core
      std::unordered_set<Node, NodeHashFunction> excAsserts;
      std::vector<Node> ctx;
      ccheck.d_falseCores.getExclusion(excAsserts, ctx);
      Trace("sygus-ccore-debug")
          << "Excluded " << excAsserts.size() << " assertions for "
          << ccheck.d_numFalseCores << " false cores." << std::endl;
      std::vector<Node> asserts;
      for (const Node& a : ccheck.d_cpool)
      {
        if (excAsserts.find(a) == excAsserts.end())
        {
          asserts.push_back(a);
        }
      }
      asserts.push_back(ccheck.d_this);
      // randomize
      std::shuffle(asserts.begin(), asserts.end(), Random::getRandom());
      for (const Node& p : asserts)
      {
        checkCoreSmt.assertFormula(p.toExpr());
      }
      Result r = checkCoreSmt.checkSat();
      Trace("sygus-ccore-debug") << "...got " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        // get the unsat core
        UnsatCore uc = checkCoreSmt.getUnsatCore();
        bool hasCheckF = false;
        std::vector<Node> uasserts;
        for (UnsatCore::const_iterator i = uc.begin(); i != uc.end(); ++i)
        {
          Node uassert = Node::fromExpr(*i);
          Trace("sygus-ccore-debug") << "  uc " << uassert << std::endl;
          if (uassert == ccheck.d_this)
          {
            hasCheckF = true;
            continue;
          }
          uasserts.push_back(uassert);
        }
        std::sort(uasserts.begin(), uasserts.end());
        Node sol;
        for (const Node& u : uasserts)
        {
          Node s = ccheck.d_cpoolToSol[u];
          Trace("sygus-ccore-debug-sy") << "  uc-s " << s << std::endl;
          Assert(!s.isNull());
          if (sol.isNull())
          {
            sol = s;
          }
          else
          {
            sol = nm->mkNode(APPLY_CONSTRUCTOR, ccheck.d_scons, s, sol);
          }
        }
        Trace("sygus-ccore-sy") << "Sygus solution : " << sol << std::endl;
        if (ccheck.d_tried.find(sol) != ccheck.d_tried.end())
        {
          hasCheckF = true;
          break;
        }
        ccheck.d_tried.insert(sol);
        Trace("sygus-ccore-debug")
            << "Involved check formula: " << hasCheckF << std::endl;
        if (!hasCheckF)
        {
          // it is a false core
          Trace("sygus-ccore") << "...false candidate solution" << std::endl;
          ccheck.d_falseCores.add(sol, uasserts);
          ccheck.d_numFalseCores++;
          continue;
        }
        else
        {
          sol = nm->mkNode(APPLY_CONSTRUCTOR, ccheck.d_scons, s, sol);
        }
      }
      Trace("sygus-ccore-sy") << "Sygus solution : " << sol << std::endl;
      if (Trace.isOn("sygus-ccore"))
      {
        Trace("sygus-ccore") << "...constructed candidate solution ";
        Printer* p = Printer::getPrinter(options::outputLanguage());
        std::stringstream ss;
        p->toStreamSygus(ss, sol);
        Trace("sygus-ccore") << ss.str() << std::endl;
      }
      if( ccheck.d_tried.find(sol)!=ccheck.d_tried.end() )
      {
        Trace("sygus-ccore") << "...repeat candidate solution" << std::endl;
        continue;
      }
      ccheck.d_tried.insert(sol);
      Trace("sygus-ccore-debug")
          << "Involved check formula: " << hasCheckF << std::endl;
      if (!hasCheckF )
      {
        // it is a false core 
        Trace("sygus-ccore") << "...false candidate solution" << std::endl;
        ccheck.d_falseCores.add(sol,uasserts);
        ccheck.d_numFalseCores++;
        hadFalseCore = true;
      }
      else if (!sol.isNull())
      {
        solv.push_back(sol);
        return true;
      }
    }while( hadFalseCore );
  }
  Trace("sygus-ccore") << "...failed to generate candidate" << std::endl;
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
