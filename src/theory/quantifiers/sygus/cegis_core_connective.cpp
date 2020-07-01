/*********************                                                        */
/*! \file cegis_core_connective.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of cegis core connective module.
 **/

#include "theory/quantifiers/sygus/cegis_core_connective.h"

#include "expr/datatype.h"
#include "options/base_options.h"
#include "printer/printer.h"
#include "proof/unsat_core.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/sygus/ce_guided_single_inv.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool VariadicTrie::add(Node n, const std::vector<Node>& i)
{
  VariadicTrie* curr = this;
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

bool VariadicTrie::hasSubset(const std::vector<Node>& is) const
{
  if (!d_data.isNull())
  {
    return true;
  }
  for (const std::pair<const Node, VariadicTrie>& p : d_children)
  {
    Node n = p.first;
    if (std::find(is.begin(), is.end(), n) != is.end())
    {
      if (p.second.hasSubset(is))
      {
        return true;
      }
    }
  }
  return false;
}

CegisCoreConnective::CegisCoreConnective(QuantifiersEngine* qe,
                                         SynthConjecture* p)
    : Cegis(qe, p)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

bool CegisCoreConnective::processInitialize(Node conj,
                                            Node n,
                                            const std::vector<Node>& candidates,
                                            std::vector<Node>& lemmas)
{
  Trace("sygus-ccore-init") << "CegisCoreConnective::initialize" << std::endl;
  Trace("sygus-ccore-init") << "  conjecture : " << conj << std::endl;
  Trace("sygus-ccore-init") << "  candidates : " << candidates << std::endl;
  if (candidates.size() != 1)
  {
    Trace("sygus-ccore-init")
        << "...only applies to single candidate conjectures." << std::endl;
    return false;
  }
  d_candidate = candidates[0];
  Assert(conj.getKind() == FORALL);
  Assert(conj[0].getNumChildren() == 1);
  Node body = conj[1];
  if (body.getKind() == NOT && body[0].getKind() == FORALL)
  {
    body = body[0][1];
  }
  else
  {
    body = TermUtil::simpleNegate(body);
  }
  Trace("sygus-ccore-init") << "  body : " << body << std::endl;

  TransitionInference ti;
  ti.process(body, conj[0][0]);

  if (!ti.isComplete())
  {
    Trace("sygus-ccore-init") << "...could not infer predicate." << std::endl;
    return false;
  }
  if (ti.isTrivial())
  {
    // not necessary to use this class if the conjecture is trivial (does
    // not contain the function-to-synthesize).
    Trace("sygus-ccore-init") << "...conjecture is trivial." << std::endl;
    return false;
  }
  Node trans = ti.getTransitionRelation();
  Trace("sygus-ccore-init") << "  transition relation: " << trans << std::endl;
  if (!trans.isConst() || trans.getConst<bool>())
  {
    Trace("sygus-ccore-init")
        << "...does not apply conjectures with transition relations."
        << std::endl;
    return false;
  }

  // the grammar must allow AND / OR when applicable
  TypeNode gt = d_candidate.getType();

  Node f = ti.getFunction();
  Assert(!f.isNull());
  Trace("sygus-ccore-init") << "  predicate: " << f << std::endl;
  ti.getVariables(d_vars);
  Trace("sygus-ccore-init") << "  variables: " << d_vars << std::endl;
  // make the evaluation function
  std::vector<Node> echildren;
  echildren.push_back(d_candidate);
  echildren.insert(echildren.end(), d_vars.begin(), d_vars.end());
  d_eterm = NodeManager::currentNM()->mkNode(DT_SYGUS_EVAL, echildren);
  Trace("sygus-ccore-init") << "  evaluation term: " << d_eterm << std::endl;

  Node prePost[2];
  prePost[0] = ti.getPreCondition();
  // negate the post condition
  prePost[1] = TermUtil::simpleNegate(ti.getPostCondition());
  Trace("sygus-ccore-init") << "  precondition: " << prePost[0] << std::endl;
  Trace("sygus-ccore-init") << "  postcondition: " << prePost[1] << std::endl;

  // side condition?
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(conj, qa);
  Node sc = qa.d_sygusSideCondition;
  if (!sc.isNull())
  {
    Trace("sygus-ccore-init") << "  side condition: " << sc << std::endl;
    if (sc.getKind() == EXISTS)
    {
      sc = sc[1];
    }
    Node scb = TermUtil::simpleNegate(sc);
    TransitionInference tisc;
    tisc.process(scb, conj[0][0]);
    Node scTrans = ti.getTransitionRelation();
    Trace("sygus-ccore-init")
        << "  transition relation of SC: " << scTrans << std::endl;
    if (tisc.isComplete() && scTrans.isConst() && !scTrans.getConst<bool>())
    {
      std::vector<Node> scVars;
      tisc.getVariables(scVars);
      Node scPre = tisc.getPreCondition();
      scPre = scPre.substitute(
          scVars.begin(), scVars.end(), d_vars.begin(), d_vars.end());
      Node scPost = TermUtil::simpleNegate(tisc.getPostCondition());
      scPost = scPost.substitute(
          scVars.begin(), scVars.end(), d_vars.begin(), d_vars.end());
      Trace("sygus-ccore-init")
          << "  precondition of SC: " << scPre << std::endl;
      Trace("sygus-ccore-init")
          << "  postcondition of SC: " << scPost << std::endl;
      // We are extracting the side condition to be used by this algorithm
      // from the side condition ascribed to the synthesis conjecture.
      // A sygus conjecture of the form, for predicate-to-synthesize I:
      //   exists I. forall x. P[I,x]
      // whose ascribed side condition is C[I], has the semantics:
      //   exists I. C[I] ^ forall x. P[I,x].
      // Notice that this side condition C may be an arbitrary formula over the
      // function to synthesize. However, the algorithm implemented by this
      // class is restricted to side conditions of the form:
      //   exists k. A[k] ^ I(k)
      // The above condition guards for this case, and runs this block of code,
      // where we use the TransitionInference utility to extract A[k] from
      // A[k] ^ I(k). In the end, we set d_sc to A[d_vars]; notice the variables
      // d_vars are those introduced by the TransitionInference utility
      // for normalization.
      d_sc = scPost;
    }
  }

  // We use the postcondition if it non-trivial and the grammar gt for our
  // candidate has the production rule gt -> AND( gt, gt ). Similarly for
  // precondition and OR.
  Assert(gt.isDatatype());
  const DType& gdt = gt.getDType();
  SygusTypeInfo& gti = d_tds->getTypeInfo(gt);
  for (unsigned r = 0; r < 2; r++)
  {
    Node node = prePost[r];
    if (node.isConst())
    {
      // this direction is trivial, ignore
      continue;
    }
    Component& c = r == 0 ? d_pre : d_post;
    Kind rk = r == 0 ? OR : AND;
    int i = gti.getKindConsNum(rk);
    if (i != -1 && gdt[i].getNumArgs() == 2
        && gdt[i].getArgType(0) == gt
        && gdt[i].getArgType(1) == gt)
    {
      Trace("sygus-ccore-init") << "  will do " << (r == 0 ? "pre" : "post")
                                << "condition." << std::endl;
      Node cons = gdt[i].getConstructor();
      c.initialize(node, cons);
      // Register the symmetry breaking lemma: do not do top-level solutions
      // with this constructor (e.g. we want to enumerate literals, not
      // conjunctions).
      Node tst = datatypes::utils::mkTester(d_candidate, i, gdt);
      Trace("sygus-ccore-init") << "Sym break lemma " << tst << std::endl;
      lemmas.push_back(tst.negate());
    }
  }
  if (!isActive())
  {
    return false;
  }
  // initialize the enumerator
  return Cegis::processInitialize(conj, n, candidates, lemmas);
}

bool CegisCoreConnective::processConstructCandidates(
    const std::vector<Node>& enums,
    const std::vector<Node>& enum_values,
    const std::vector<Node>& candidates,
    std::vector<Node>& candidate_values,
    bool satisfiedRl,
    std::vector<Node>& lems)
{
  Assert(isActive());
  bool ret = constructSolution(enums, enum_values, candidate_values);

  // exclude in the basic way if passive
  Assert(enums.size() == 1);
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, esize = enums.size(); i < esize; i++)
  {
    Node e = enums[i];
    if (!d_tds->isPassiveEnumerator(e))
    {
      continue;
    }
    Node v = enum_values[i];
    Node lem = d_tds->getExplain()->getExplanationForEquality(e, v).negate();
    Node g = d_tds->getActiveGuardForEnumerator(e);
    if (!g.isNull())
    {
      lem = nm->mkNode(OR, g.negate(), lem);
    }
    lems.push_back(lem);
  }
  return ret;
}

bool CegisCoreConnective::isActive() const
{
  return d_pre.isActive() || d_post.isActive();
}

bool CegisCoreConnective::constructSolution(
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
  Trace("sygus-ccore-summary")
      << "CegisCoreConnective: construct solution..." << std::endl;
  if (Trace.isOn("sygus-ccore"))
  {
    Trace("sygus-ccore")
        << "CegisCoreConnective: Construct candidate solutions..." << std::endl;
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
    Component& cfilter = d == 0 ? d_post : d_pre;
    // In terms of the algorithm described in the h file, this gets the formula
    // A (or B, depending on the direction d).
    Node fpred = cfilter.getFormula();
    if (!fpred.isNull() && !fpred.isConst())
    {
      // check refinement points
      Node etsrn = d == 0 ? etsr : etsr.negate();
      std::unordered_set<Node, NodeHashFunction> visited;
      std::vector<Node> pt;
      Node rid = cfilter.getRefinementPt(this, etsrn, visited, pt);
      if (!rid.isNull())
      {
        // failed a refinement point
        continue;
      }
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
          cfilter.addRefinementPt(fassert, mvs);
        }
        continue;
      }
    }
    Trace("sygus-ccore-debug")
        << "...add to pool in direction " << d << std::endl;
    // implements e.g. pool(B) += e_i.
    ccheck.addToPool(etsr, cval);

    // ----- get the pool of assertions and randomize it
    std::vector<Node> passerts;
    ccheck.getTermPool(passerts);
    std::shuffle(passerts.begin(), passerts.end(), Random::getRandom());

    // ----- check for entailment, adding based on models of failed points
    std::vector<Node> asserts;
    Node sol = constructSolutionFromPool(ccheck, asserts, passerts);
    if (!sol.isNull())
    {
      solv.push_back(sol);
      Trace("sygus-ccore-summary") << "...success" << std::endl;
      return true;
    }
    if (Trace.isOn("sygus-ccore-summary"))
    {
      std::stringstream ss;
      ccheck.debugPrintSummary(ss);
      Trace("sygus-ccore-summary")
          << "C[d=" << d << "] " << ss.str() << std::endl;
    }
  }
  Trace("sygus-ccore") << "CegisCoreConnective: failed to generate candidate"
                       << std::endl;
  Trace("sygus-ccore-summary") << "...failed" << std::endl;
  return false;
}

void CegisCoreConnective::Component::initialize(Node n, Node c)
{
  d_this = n;
  d_scons = c;
}

void CegisCoreConnective::Component::addToPool(Node n, Node s)
{
  d_cpool.push_back(n);
  d_cpoolToSol[n] = s;
}

Node CegisCoreConnective::Component::getSygusSolution(
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
void CegisCoreConnective::Component::debugPrintSummary(std::ostream& os) const
{
  os << "size(pool/pts/cores): " << d_cpool.size() << "/" << d_numRefPoints
     << "/" << d_numFalseCores;
}

void CegisCoreConnective::Component::addRefinementPt(
    Node id, const std::vector<Node>& pt)
{
  d_numRefPoints++;
  bool res = d_refinementPt.addTerm(id, pt);
  // this should always be a new point
  AlwaysAssert(res);
}
void CegisCoreConnective::Component::addFalseCore(Node id,
                                                  const std::vector<Node>& u)
{
  d_numFalseCores++;
  d_falseCores.add(id, u);
}

Node CegisCoreConnective::Component::getRefinementPt(
    CegisCoreConnective* p,
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
      Trace("sygus-ccore-ref") << "...data is " << id << std::endl;
      Assert(!id.isNull());
      AlwaysAssert(id.getType().isBoolean());
      if (visited.find(id) == visited.end())
      {
        visited.insert(id);
        Trace("sygus-ccore-ref") << "...eval " << std::endl;
        // check if it is true
        Node en = p->evaluate(n, id, ctx);
        if (en.isConst() && en.getConst<bool>())
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
      // get the current child iterator for this node
      itvt = vt.find(cur);
      if (itvt == vt.end())
      {
        Trace("sygus-ccore-ref") << "...initialize iterator " << std::endl;
        // initialize the iterator
        itv = cur->d_data.begin();
        vt[cur] = itv;
        Trace("sygus-ccore-ref") << "...finished init" << std::endl;
      }
      else
      {
        Trace("sygus-ccore-ref") << "...continue iterator " << std::endl;
        itv = itvt->second;
      }
      Trace("sygus-ccore-ref") << "...now check status" << std::endl;
      // are we done iterating children?
      if (itv == cur->d_data.end())
      {
        Trace("sygus-ccore-ref") << "...finished iterating " << std::endl;
        // yes, pop back
        if (!ctx.empty())
        {
          ctx.pop_back();
        }
        visit.pop_back();
        vt.erase(cur);
      }
      else
      {
        Trace("sygus-ccore-ref") << "...recurse " << itv->first << std::endl;
        // recurse
        ctx.push_back(itv->first);
        visit.push_back(&(itv->second));
        ++vt[cur];
      }
    }

  } while (!visit.empty());
  return Node::null();
}

void CegisCoreConnective::Component::getTermPool(
    std::vector<Node>& passerts) const
{
  passerts.insert(passerts.end(), d_cpool.begin(), d_cpool.end());
}

bool CegisCoreConnective::Component::addToAsserts(CegisCoreConnective* p,
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
    if (d_falseCores.hasSubset(asserts))
    {
      Trace("sygus-ccore-debug")
          << "..." << n << " was rejected due to previous false core"
          << std::endl;
      asserts.pop_back();
      n = Node::null();
    }
  } while (n.isNull());
  Trace("sygus-ccore") << "--- Insert " << n << " to falsify " << mvs
                       << std::endl;
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

void CegisCoreConnective::getModel(SmtEngine& smt,
                                   std::vector<Node>& vals) const
{
  for (const Node& v : d_vars)
  {
    Node mv = Node::fromExpr(smt.getValue(v.toExpr()));
    Trace("sygus-ccore-model") << v << " -> " << mv << " ";
    vals.push_back(mv);
  }
}

bool CegisCoreConnective::getUnsatCore(
    SmtEngine& smt,
    const std::unordered_set<Node, NodeHashFunction>& queryAsserts,
    std::vector<Node>& uasserts) const
{
  UnsatCore uc = smt.getUnsatCore();
  bool hasQuery = false;
  for (UnsatCore::const_iterator i = uc.begin(); i != uc.end(); ++i)
  {
    Node uassert = Node::fromExpr(*i);
    Trace("sygus-ccore-debug") << "  uc " << uassert << std::endl;
    if (queryAsserts.find(uassert) != queryAsserts.end())
    {
      hasQuery = true;
      continue;
    }
    uasserts.push_back(uassert);
  }
  return hasQuery;
}

Result CegisCoreConnective::checkSat(Node n, std::vector<Node>& mvs) const
{
  Trace("sygus-ccore-debug") << "...check-sat " << n << "..." << std::endl;
  Result r = checkWithSubsolver(n, d_vars, mvs);
  Trace("sygus-ccore-debug") << "...got " << r << std::endl;
  return r;
}

Node CegisCoreConnective::evaluate(Node n,
                                   Node id,
                                   const std::vector<Node>& mvs)
{
  Kind nk = n.getKind();
  if (nk == AND || nk == OR)
  {
    NodeManager* nm = NodeManager::currentNM();
    bool expRes = nk == OR;
    // split AND/OR
    for (const Node& nc : n)
    {
      Node enc = evaluate(nc, id, mvs);
      Assert(enc.isConst());
      if (enc.getConst<bool>() == expRes)
      {
        return nm->mkConst(expRes);
      }
    }
    return nm->mkConst(!expRes);
  }
  std::unordered_map<Node, Node, NodeHashFunction>& ec = d_eval_cache[n];
  if (!id.isNull())
  {
    std::unordered_map<Node, Node, NodeHashFunction>::iterator it = ec.find(id);
    if (it != ec.end())
    {
      return it->second;
    }
  }
  // use evaluator
  Node cn = d_eval.eval(n, d_vars, mvs);
  if (cn.isNull())
  {
    cn = n.substitute(d_vars.begin(), d_vars.end(), mvs.begin(), mvs.end());
    cn = Rewriter::rewrite(cn);
  }
  if (!id.isNull())
  {
    ec[id] = cn;
  }
  return cn;
}

Node CegisCoreConnective::constructSolutionFromPool(Component& ccheck,
                                                    std::vector<Node>& asserts,
                                                    std::vector<Node>& passerts)
{
  // In terms of Variant #2 from the header file, the set D is represented by
  // asserts. The available set of prediates pool(B) is represented by passerts.
  NodeManager* nm = NodeManager::currentNM();
  Trace("sygus-ccore") << "------ Get initial candidate..." << std::endl;
  Node an = asserts.empty()
                ? d_true
                : (asserts.size() == 1 ? asserts[0] : nm->mkNode(AND, asserts));
  std::vector<Node> mvs;
  std::unordered_set<Node, NodeHashFunction> visited;
  bool addSuccess = true;
  // Ensure that the current conjunction evaluates to false on all refinement
  // points. We get refinement points until we have exhausted.
  // In terms of Variant #2, this is inner while loop that adds points to D
  // while there exists a point in pts(B) such that D is true.
  Node mvId;
  do
  {
    mvs.clear();
    Trace("sygus-ccore-debug") << "...get refinement pt..." << std::endl;
    // In terms of Variant #2, this implements the line:
    //   "D[v] is true for some v in pts(B)",
    // where v is stored in mvs.
    mvId = ccheck.getRefinementPt(this, an, visited, mvs);
    if (!mvId.isNull())
    {
      Trace("sygus-ccore-debug") << "...got " << mvs << std::endl;
      // In terms of Variant #2, this checks the conditions:
      //   "d'[v] is false for some d' in pool(B)" and
      //   "no element of cores(B) is a subset of D ++ { d' }"
      // and adds d' to D (asserts) if possible.
      addSuccess = ccheck.addToAsserts(this, passerts, mvs, mvId, asserts, an);
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
    return Node::null();
  }
  Trace("sygus-ccore") << "----- Initial candidate is " << an << std::endl;

  // We now have constructed an initial candidate for D. In terms of Variant #2,
  // we now enter the block code within "if D is false for all v in pts(B)".
  // Further refinements to D are made as the following do-while loop proceeds.
  do
  {
    addSuccess = false;
    // try a new core
    std::unique_ptr<SmtEngine> checkSol(
        new SmtEngine(NodeManager::currentNM()->toExprManager()));
    initializeSubsolver(checkSol.get());
    Trace("sygus-ccore") << "----- Check candidate " << an << std::endl;
    std::vector<Node> rasserts = asserts;
    rasserts.push_back(d_sc);
    rasserts.push_back(ccheck.getFormula());
    std::shuffle(rasserts.begin(), rasserts.end(), Random::getRandom());
    Node query = rasserts.size() == 1 ? rasserts[0] : nm->mkNode(AND, rasserts);
    for (const Node& a : rasserts)
    {
      checkSol->assertFormula(a.toExpr());
    }
    Result r = checkSol->checkSat();
    Trace("sygus-ccore") << "----- check-sat returned " << r << std::endl;
    // In terms of Variant #2, this is the check "if (S ^ D) => B"
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      // it entails the postcondition, now get the unsat core
      // In terms of Variant #2, this is the line
      //   "Let U be a subset of D such that S ^ U ^ ~B is unsat."
      // and uasserts is set to U.
      std::vector<Node> uasserts;
      std::unordered_set<Node, NodeHashFunction> queryAsserts;
      queryAsserts.insert(ccheck.getFormula());
      queryAsserts.insert(d_sc);
      bool hasQuery = getUnsatCore(*checkSol, queryAsserts, uasserts);
      // now, check the side condition
      bool falseCore = false;
      if (!d_sc.isNull())
      {
        if (!hasQuery)
        {
          // Already know it trivially rewrites to false, don't need
          // to use unsat cores.
          falseCore = true;
        }
        else
        {
          // In terms of Variant #2, this is the check "if S ^ U is unsat"
          Trace("sygus-ccore") << "----- Check side condition" << std::endl;
          std::unique_ptr<SmtEngine> checkSc(
              new SmtEngine(NodeManager::currentNM()->toExprManager()));
          initializeSubsolver(checkSc.get());
          std::vector<Node> scasserts;
          scasserts.insert(scasserts.end(), uasserts.begin(), uasserts.end());
          scasserts.push_back(d_sc);
          std::shuffle(scasserts.begin(), scasserts.end(), Random::getRandom());
          for (const Node& sca : scasserts)
          {
            checkSc->assertFormula(sca.toExpr());
          }
          Result rsc = checkSc->checkSat();
          Trace("sygus-ccore")
              << "----- check-sat returned " << rsc << std::endl;
          if (rsc.asSatisfiabilityResult().isSat() == Result::UNSAT)
          {
            // In terms of Variant #2, this is the line
            //   "Let W be a subset of D such that S ^ W is unsat."
            // and uasserts is set to W.
            uasserts.clear();
            std::unordered_set<Node, NodeHashFunction> queryAsserts2;
            queryAsserts2.insert(d_sc);
            getUnsatCore(*checkSc, queryAsserts2, uasserts);
            falseCore = true;
          }
        }
      }

      if (!falseCore)
      {
        // In terms of Variant #2, this is the line:
        //   "return u_1 AND ... AND u_m where U = { u_1, ..., u_m }".
        Trace("sygus-ccore") << ">>> Solution : " << uasserts << std::endl;
        // We convert the builtin solution to a sygus datatype to
        // communicate with the sygus solver.
        Node sol = ccheck.getSygusSolution(uasserts);
        Trace("sygus-ccore-sy") << "Sygus solution : " << sol << std::endl;
        return sol;
      }
      else
      {
        Assert(!uasserts.empty());
        Node xu = uasserts[0];
        Trace("sygus-ccore")
            << "--- Add false core : " << uasserts << std::endl;
        // notice that a singleton false core could be removed from pool
        // in the case that (uasserts.size() == 1).
        std::sort(uasserts.begin(), uasserts.end());
        // In terms of Variant #2, this is "cores(B) += W".
        ccheck.addFalseCore(query, uasserts);
        // remove and continue
        // In terms of Variant #2, this is "remove some d'' in W from D".
        std::vector<Node>::iterator ita =
            std::find(asserts.begin(), asserts.end(), xu);
        Assert(ita != asserts.end());
        asserts.erase(ita);
        // Start over, since now we don't know which points are required to
        // falsify.
        return constructSolutionFromPool(ccheck, asserts, passerts);
      }
    }
    else if (r.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      // it does not entail the postcondition, add an assertion that blocks
      // the current point
      mvs.clear();
      getModel(*checkSol, mvs);
      // should evaluate to true
      Node ean = evaluate(an, Node::null(), mvs);
      Assert(ean.isConst() && ean.getConst<bool>());
      Trace("sygus-ccore") << "--- Add refinement point " << mvs << std::endl;
      // In terms of Variant #2, this is the line:
      //   "pts(B) += { v } where { x -> v } is a model for D ^ ~B".
      ccheck.addRefinementPt(query, mvs);
      Trace("sygus-ccore-debug") << "...get new assertion..." << std::endl;
      // In terms of Variant #2, this rechecks the condition of the inner while
      // loop and attempts to add a new assertion to D.
      addSuccess = ccheck.addToAsserts(this, passerts, mvs, query, asserts, an);
      Trace("sygus-ccore-debug") << "...success is " << addSuccess << std::endl;
    }
  } while (addSuccess);
  return Node::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
