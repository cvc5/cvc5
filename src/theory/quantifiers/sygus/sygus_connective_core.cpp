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

bool FalseCoreTrie::isFalse(const std::vector<Node>& is) const
{
  if (!d_data.isNull())
  {
    return true;
  }
  for (const std::pair<const Node, FalseCoreTrie>& p : d_children)
  {
    Node n = p.first;
    if (std::find(is.begin(), is.end(), n) != is.end())
    {
      if (p.second.isFalse(is))
      {
        return true;
      }
    }
  }
  return false;
}

SygusConnectiveCore::SygusConnectiveCore(QuantifiersEngine* qe,
                                         SynthConjecture* p)
    : Cegis(qe, p)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
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
  // negate the post condition
  d_post.d_this = TermUtil::simpleNegate(ti.getPostCondition());
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
  Trace("sygus-ccore-debug") << "...predicate is: " << etsr << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned d = 0; d < 2; d++)
  {
    Component& ccheck = d == 0 ? d_pre : d_post;
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
    Component& cfilter = d == 0 ? d_post : d_pre;
    Node fpred = cfilter.d_this;
    if (!fpred.isConst())
    {
      // TODO : check refinement points
      Node etsrn = d == 0 ? etsr : etsr.negate();
      Node fassert = nm->mkNode(AND, fpred, etsrn);
      Trace("sygus-ccore-debug")
          << "...check filter " << fassert << "..." << std::endl;
      std::vector<Node> mvs;
      Result r = checkSat(fassert, mvs);
      Trace("sygus-ccore-debug") << "...got " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        // failed the filter, remember the refinement point
        if (r.asSatisfiabilityResult().isSat() == Result::SAT)
        {
          cfilter.d_refinementPt.addTerm(fassert, mvs);
        }
        continue;
      }
    }
    Trace("sygus-ccore-debug")
        << "...add to pool in direction " << d << std::endl;
    ccheck.d_cpool.push_back(etsr);
    ccheck.d_cpoolToSol[etsr] = cval;

    // ----- get the pool of assertions and randomize it
    std::vector<Node> passerts = ccheck.d_cpool;
    std::shuffle(passerts.begin(), passerts.end(), Random::getRandom());

    // ----- check for entailment, adding based on models of failed points
    Trace("sygus-ccore") << "------ Get initial candidate..." << std::endl;
    std::vector<Node> asserts;
    Node an = d_true;
    std::vector<Node> mvs;
    std::unordered_set<Node, NodeHashFunction> visited;
    bool addSuccess = true;
    // Ensure that the current conjunction evaluates to false on all refinement
    // points. We get refinement points until we have exhausted.
    Node mvId;
    do
    {
      mvs.clear();
      Trace("sygus-ccore-debug") << "...get refinement pt..." << std::endl;
      Node mvId = ccheck.getRefinementPt(this, an, visited, mvs);
      if (!mvId.isNull())
      {
        Trace("sygus-ccore-debug") << "...got " << mvs << std::endl;
        addSuccess =
            ccheck.addToAsserts(this, passerts, mvs, mvId, asserts, an);
        Trace("sygus-ccore-debug")
            << "...add success is " << addSuccess << std::endl;
      }
      else
      {
        Trace("sygus-ccore-debug") << "...failed" << std::endl;
      }
    } while (!mvId.isNull() && addSuccess);
    if (!addSuccess)
    {
      Trace("sygus-ccore") << ">>> Failed to generate initial candidate"
                           << std::endl;
      continue;
    }
    Trace("sygus-ccore") << "----- Initial candidate is " << an << std::endl;

    do
    {
      addSuccess = false;
      // try a new core
      SmtEngine checkCoreSmt(nm->toExprManager());
      checkCoreSmt.setIsInternalSubsolver();
      checkCoreSmt.setLogic(smt::currentSmtEngine()->getLogicInfo());
      Trace("sygus-ccore") << "----- Check candidate " << an << std::endl;
      std::vector<Node> rasserts = asserts;
      rasserts.push_back(ccheck.d_this);
      std::shuffle(rasserts.begin(), rasserts.end(), Random::getRandom());
      Node query = nm->mkNode(AND, rasserts);
      for (const Node& a : rasserts)
      {
        checkCoreSmt.assertFormula(a.toExpr());
      }
      Result r = checkCoreSmt.checkSat();
      Trace("sygus-ccore") << "----- check-sat returned " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
      {
        // it entails the postcondition
        // check whether it is a false core
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
        if (hasCheckF)
        {
          Trace("sygus-ccore") << ">>> Solution : " << an << std::endl;

          Node sol = ccheck.getSygusSolution(asserts);
          Trace("sygus-ccore-sy") << "Sygus solution : " << sol << std::endl;
          if (ccheck.d_tried.find(sol) == ccheck.d_tried.end())
          {
            ccheck.d_tried.insert(sol);
          }
          solv.push_back(sol);
          return true;
        }
        else
        {
          Trace("sygus-ccore") << "--- false core : " << uasserts << std::endl;
          if (uasserts.size() == 1)
          {
            // singleton false core should be removed from pool
          }
          // false core, remove and continue
          ccheck.d_falseCores.add(query, uasserts);
          // TODO: try again
          /*
          // exclude the last assertion
          if( an.getKind()==AND )
          {
            Assert( an[0]==asserts.back() );
            an = an[1];
          }
          else
          {
            Assert( an==asserts.back() );
            an = d_true;
          }
          asserts.pop_back();
          addSuccess = true;
          */
        }
      }
      else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
      {
        // it does not entail the postcondition, add an assertion that blocks
        // the current point
        mvs.clear();
        getModel(checkCoreSmt, mvs);
        Trace("sygus-ccore") << "--- Add refinement point " << mvs << std::endl;
        ccheck.d_refinementPt.addTerm(query, mvs);
        Trace("sygus-ccore-debug") << "...get new assertion..." << std::endl;
        addSuccess =
            ccheck.addToAsserts(this, passerts, mvs, query, asserts, an);
        Trace("sygus-ccore-debug")
            << "...success is " << addSuccess << std::endl;
      }
    } while (addSuccess);
  }
  Trace("sygus-ccore") << "SygusConnectiveCore: failed to generate candidate"
                       << std::endl;
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
    SygusConnectiveCore* p,
    Node n,
    std::unordered_set<Node, NodeHashFunction>& visited,
    std::vector<Node>& ss)
{
  std::vector<Node> ctx;

  unsigned depth = p->d_vars.size();
  std::map<NodeTrie*, std::map<Node, NodeTrie>::iterator> vt;
  std::map<NodeTrie*, std::map<Node, NodeTrie>::iterator>::iterator itvt;
  std::map<Node, NodeTrie>::iterator itv;
  std::vector<NodeTrie*> visit;
  NodeTrie* cur;
  visit.push_back(&d_refinementPt);
  do
  {
    cur = visit.back();
    Trace("sygus-ccore-ref") << "process trie " << cur << std::endl;
    if (ctx.size() == depth)
    {
      Trace("sygus-ccore-ref") << "...at depth " << std::endl;
      // at leaf
      Node id = cur->getData();
      if (visited.find(id) == visited.end())
      {
        visited.insert(id);
        // check if it is true
        Node en = p->evaluate(n, id, ctx);
        if (en.isConst() && en.getConst<bool>())
        {
          ss = ctx;
          return id;
        }
      }
      visit.pop_back();
    }
    else
    {
      // get the current child iterator for this node
      itvt = vt.find(cur);
      if (itvt == vt.end())
      {
        Trace("sygus-ccore-ref") << "...initialize iterator " << std::endl;
        // initialize the iterator
        itv = cur->d_data.begin();
        vt[cur] = itv;
        ctx.push_back(Node::null());
        Trace("sygus-ccore-ref") << "...finished init" << std::endl;
      }
      else
      {
        Trace("sygus-ccore-ref") << "...continue iterator " << std::endl;
        itv = itvt->second;
      }
      Trace("sygus-ccore-ref") << "...now check status" << std::endl;
      AlwaysAssert(!ctx.empty());
      Trace("sygus-ccore-ref") << "...now check status2 " << cur << std::endl;
      // are we done iterating children?
      if (itv == cur->d_data.end())
      {
        Trace("sygus-ccore-ref") << "...finished iterating " << std::endl;
        // yes, pop back
        visit.pop_back();
        vt.erase(cur);
        ctx.pop_back();
      }
      else
      {
        Trace("sygus-ccore-ref") << "...recurse " << itv->first << std::endl;
        // recurse
        ctx[ctx.size() - 1] = itv->first;
        visit.push_back(&(itv->second));
        ++vt[cur];
      }
    }

  } while (!visit.empty());
  return Node::null();
}

bool SygusConnectiveCore::Component::addToAsserts(SygusConnectiveCore* p,
                                                  std::vector<Node>& passerts,
                                                  const std::vector<Node>& mvs,
                                                  Node mvId,
                                                  std::vector<Node>& asserts,
                                                  Node& an)
{
  // point should be valid
  Assert(!mvId.isNull());
  Node n;
  unsigned currIndex = 0;
  do
  {
    // select condition from passerts that evaluates to false on mvs
    for (unsigned i = currIndex, psize = passerts.size(); i < psize; i++)
    {
      Node cn = passerts[i];
      Node cne = p->evaluate(cn, mvId, mvs);
      if (cne.isConst() && !cne.getConst<bool>())
      {
        n = cn;
        // remove n from the pool
        passerts.erase(passerts.begin() + i, passerts.begin() + i + 1);
        currIndex = i;
        break;
      }
    }
    if (n.isNull())
    {
      // could not find any
      return false;
    }
    Trace("sygus-ccore-debug") << "...try adding " << n << "..." << std::endl;
    asserts.push_back(n);
    // is it already part of a false core?
    if (d_falseCores.isFalse(asserts))
    {
      Trace("sygus-ccore-debug")
          << "..." << n << " was rejected due to previous false core"
          << std::endl;
      asserts.pop_back();
      n = Node::null();
    }
  } while (n.isNull());
  Trace("sygus-ccore") << "--- Add " << n << " to falsify " << mvs << std::endl;
  // success
  if (an.isConst())
  {
    Assert(an.getConst<bool>());
    an = n;
  }
  else
  {
    an = NodeManager::currentNM()->mkNode(AND, n, an);
  }
  return true;
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

Result SygusConnectiveCore::checkSat(Node n, std::vector<Node>& mvs)
{
  Assert(mvs.empty());
  Assert(n.getType().isBoolean());
  Trace("sygus-ccore-debug") << "...check-sat " << n << "..." << std::endl;
  n = Rewriter::rewrite(n);
  if (n.isConst())
  {
    if (n.getConst<bool>())
    {
      // default model
      for (const Node& v : d_vars)
      {
        mvs.push_back(v.getType().mkGroundTerm());
      }
      return Result(Result::SAT);
    }
    else
    {
      return Result(Result::UNSAT);
    }
  }
  SmtEngine smt(NodeManager::currentNM()->toExprManager());
  smt.setIsInternalSubsolver();
  smt.setLogic(smt::currentSmtEngine()->getLogicInfo());
  smt.assertFormula(n.toExpr());
  Result r = smt.checkSat();
  Trace("sygus-ccore-debug") << "...got " << r << std::endl;
  if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    getModel(smt, mvs);
  }
  return r;
}

Node SygusConnectiveCore::evaluate(Node n,
                                   Node id,
                                   const std::vector<Node>& mvs)
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
