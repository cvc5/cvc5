/*********************                                                        */
/*! \file ceg_bv_instantiator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of ceg_bv_instantiator
 **/

#include "theory/quantifiers/cegqi/ceg_bv_instantiator.h"

#include <stack>
#include "options/quantifiers_options.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"
#include "util/random.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

struct BvLinearAttributeId
{
};
using BvLinearAttribute = expr::Attribute<BvLinearAttributeId, bool>;

// this class can be used to query the model value through the CegInstaniator
// class
class CegInstantiatorBvInverterQuery : public BvInverterQuery
{
 public:
  CegInstantiatorBvInverterQuery(CegInstantiator* ci)
      : BvInverterQuery(), d_ci(ci)
  {
  }
  ~CegInstantiatorBvInverterQuery() {}
  /** return the model value of n */
  Node getModelValue(Node n) override { return d_ci->getModelValue(n); }
  /** get bound variable of type tn */
  Node getBoundVariable(TypeNode tn) override
  {
    return d_ci->getBoundVariable(tn);
  }

 protected:
  // pointer to class that is able to query model values
  CegInstantiator* d_ci;
};

BvInstantiator::BvInstantiator(QuantifiersEngine* qe, TypeNode tn)
    : Instantiator(qe, tn), d_inst_id_counter(0)
{
  // get the global inverter utility
  // this must be global since we need to:
  // * process Skolem functions properly across multiple variables within the
  // same quantifier
  // * cache Skolem variables uniformly across multiple quantified formulas
  d_inverter = qe->getBvInverter();
}

BvInstantiator::~BvInstantiator() {}
void BvInstantiator::reset(CegInstantiator* ci,
                           SolvedForm& sf,
                           Node pv,
                           CegInstEffort effort)
{
  d_inst_id_counter = 0;
  d_var_to_inst_id.clear();
  d_inst_id_to_term.clear();
  d_inst_id_to_alit.clear();
  d_var_to_curr_inst_id.clear();
  d_alit_to_model_slack.clear();
}

void BvInstantiator::processLiteral(CegInstantiator* ci,
                                    SolvedForm& sf,
                                    Node pv,
                                    Node lit,
                                    Node alit,
                                    CegInstEffort effort)
{
  Assert(d_inverter != NULL);
  // find path to pv
  std::vector<unsigned> path;
  Node sv = d_inverter->getSolveVariable(pv.getType());
  Node pvs = ci->getModelValue(pv);
  Trace("cegqi-bv") << "Get path to " << pv << " : " << lit << std::endl;
  Node slit =
      d_inverter->getPathToPv(lit, pv, sv, pvs, path, options::cbqiBvSolveNl());
  if (!slit.isNull())
  {
    CegInstantiatorBvInverterQuery m(ci);
    unsigned iid = d_inst_id_counter;
    Trace("cegqi-bv") << "Solve lit to bv inverter : " << slit << std::endl;
    Node inst = d_inverter->solveBvLit(sv, slit, path, &m);
    if (!inst.isNull())
    {
      inst = Rewriter::rewrite(inst);
      if (inst.isConst() || !ci->hasNestedQuantification())
      {
        Trace("cegqi-bv") << "...solved form is " << inst << std::endl;
        // store information for id and increment
        d_var_to_inst_id[pv].push_back(iid);
        d_inst_id_to_term[iid] = inst;
        d_inst_id_to_alit[iid] = alit;
        d_inst_id_counter++;
      }
    }
    else
    {
      Trace("cegqi-bv") << "...failed to solve." << std::endl;
    }
  }
  else
  {
    Trace("cegqi-bv") << "...no path." << std::endl;
  }
}

bool BvInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         CegInstEffort effort)
{
  return true;
}

Node BvInstantiator::hasProcessAssertion(CegInstantiator* ci,
                                         SolvedForm& sf,
                                         Node pv,
                                         Node lit,
                                         CegInstEffort effort)
{
  if (effort == CEG_INST_EFFORT_FULL)
  {
    // always use model values at full effort
    return Node::null();
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool pol = lit.getKind() != NOT;
  Kind k = atom.getKind();
  if (k != EQUAL && k != BITVECTOR_ULT && k != BITVECTOR_SLT)
  {
    // others are unhandled
    return Node::null();
  }
  else if (!atom[0].getType().isBitVector())
  {
    return Node::null();
  }
  else if (options::cbqiBvIneqMode() == CBQI_BV_INEQ_KEEP
           || (pol && k == EQUAL))
  {
    return lit;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node s = atom[0];
  Node t = atom[1];

  Node sm = ci->getModelValue(s);
  Node tm = ci->getModelValue(t);
  Assert(!sm.isNull() && sm.isConst());
  Assert(!tm.isNull() && tm.isConst());
  Trace("cegqi-bv") << "Model value: " << std::endl;
  Trace("cegqi-bv") << "   " << s << " " << k << " " << t << " is "
                    << std::endl;
  Trace("cegqi-bv") << "   " << sm << " <> " << tm << std::endl;

  Node ret;
  if (options::cbqiBvIneqMode() == CBQI_BV_INEQ_EQ_SLACK)
  {
    // if using slack, we convert constraints to a positive equality based on
    // the current model M, e.g.:
    //   (not) s ~ t  --->  s = t + ( s^M - t^M )
    if (sm != tm)
    {
      Node slack = Rewriter::rewrite(nm->mkNode(BITVECTOR_SUB, sm, tm));
      Assert(slack.isConst());
      // remember the slack value for the asserted literal
      d_alit_to_model_slack[lit] = slack;
      ret = nm->mkNode(EQUAL, s, nm->mkNode(BITVECTOR_PLUS, t, slack));
      Trace("cegqi-bv") << "Slack is " << slack << std::endl;
    }
    else
    {
      ret = s.eqNode(t);
    }
  }
  else
  {
    // turn disequality into an inequality
    // e.g. s != t becomes s < t or t < s
    if (k == EQUAL)
    {
      if (Random::getRandom().pickWithProb(0.5))
      {
        std::swap(s, t);
      }
      pol = true;
    }
    // otherwise, we optimistically solve for the boundary point of an
    // inequality, for example:
    //   for s < t, we solve s+1 = t
    //   for ~( s < t ), we solve s = t
    // notice that this equality does not necessarily hold in the model, and
    // hence the corresponding instantiation strategy is not guaranteed to be
    // monotonic.
    if (!pol)
    {
      ret = s.eqNode(t);
    }
    else
    {
      Node bv_one = bv::utils::mkOne(bv::utils::getSize(s));
      ret = nm->mkNode(BITVECTOR_PLUS, s, bv_one).eqNode(t);
    }
  }
  Trace("cegqi-bv") << "Process " << lit << " as " << ret << std::endl;
  return ret;
}

bool BvInstantiator::processAssertion(CegInstantiator* ci,
                                      SolvedForm& sf,
                                      Node pv,
                                      Node lit,
                                      Node alit,
                                      CegInstEffort effort)
{
  // if option enabled, use approach for word-level inversion for BV
  // instantiation
  if (options::cbqiBv())
  {
    // get the best rewritten form of lit for solving for pv
    //   this should remove instances of non-invertible operators, and
    //   "linearize" lit with respect to pv as much as possible
    Node rlit = rewriteAssertionForSolvePv(ci, pv, lit);
    if (Trace.isOn("cegqi-bv"))
    {
      Trace("cegqi-bv") << "BvInstantiator::processAssertion : solve " << pv
                        << " in " << lit << std::endl;
      if (lit != rlit)
      {
        Trace("cegqi-bv") << "...rewritten to " << rlit << std::endl;
      }
    }
    if (!rlit.isNull())
    {
      processLiteral(ci, sf, pv, rlit, alit, effort);
    }
  }
  return false;
}

bool BvInstantiator::useModelValue(CegInstantiator* ci,
                                   SolvedForm& sf,
                                   Node pv,
                                   CegInstEffort effort)
{
  return effort < CEG_INST_EFFORT_FULL || options::cbqiFullEffort();
}

bool BvInstantiator::processAssertions(CegInstantiator* ci,
                                       SolvedForm& sf,
                                       Node pv,
                                       CegInstEffort effort)
{
  std::unordered_map<Node, std::vector<unsigned>, NodeHashFunction>::iterator
      iti = d_var_to_inst_id.find(pv);
  if (iti == d_var_to_inst_id.end())
  {
    // no bounds
    return false;
  }
  Trace("cegqi-bv") << "BvInstantiator::processAssertions for " << pv
                    << std::endl;
  // if interleaving, do not do inversion half the time
  if (options::cbqiBvInterleaveValue() && Random::getRandom().pickWithProb(0.5))
  {
    Trace("cegqi-bv") << "...do not do instantiation for " << pv
                      << " (skip, based on heuristic)" << std::endl;
  }
  bool firstVar = sf.empty();
  // get inst id list
  if (Trace.isOn("cegqi-bv"))
  {
    Trace("cegqi-bv") << "  " << iti->second.size()
                      << " candidate instantiations for " << pv << " : "
                      << std::endl;
    if (firstVar)
    {
      Trace("cegqi-bv") << "  ...this is the first variable" << std::endl;
    }
  }
  // until we have a model-preserving selection function for BV, this must
  // be heuristic (we only pick one literal)
  // hence we randomize the list
  // this helps robustness, since picking the same literal every time may
  // lead to a stream of value instantiations, whereas with randomization
  // we may find an invertible literal that leads to a useful instantiation.
  std::random_shuffle(iti->second.begin(), iti->second.end());

  if (Trace.isOn("cegqi-bv"))
  {
    for (unsigned j = 0, size = iti->second.size(); j < size; j++)
    {
      unsigned inst_id = iti->second[j];
      Assert(d_inst_id_to_term.find(inst_id) != d_inst_id_to_term.end());
      Node inst_term = d_inst_id_to_term[inst_id];
      Assert(d_inst_id_to_alit.find(inst_id) != d_inst_id_to_alit.end());
      Node alit = d_inst_id_to_alit[inst_id];

      // get the slack value introduced for the asserted literal
      Node curr_slack_val;
      std::unordered_map<Node, Node, NodeHashFunction>::iterator itms =
          d_alit_to_model_slack.find(alit);
      if (itms != d_alit_to_model_slack.end())
      {
        curr_slack_val = itms->second;
      }

      // debug printing
      Trace("cegqi-bv") << "   [" << j << "] : ";
      Trace("cegqi-bv") << inst_term << std::endl;
      if (!curr_slack_val.isNull())
      {
        Trace("cegqi-bv") << "   ...with slack value : " << curr_slack_val
                          << std::endl;
      }
      Trace("cegqi-bv-debug") << "   ...from : " << alit << std::endl;
      Trace("cegqi-bv") << std::endl;
    }
  }

  // Now, try all instantiation ids we want to try
  // Typically we try only one, otherwise worst-case performance
  // for constructing instantiations is exponential on the number of
  // variables in this quantifier prefix.
  bool ret = false;
  bool tryMultipleInst = firstVar && options::cbqiMultiInst();
  bool revertOnSuccess = tryMultipleInst;
  for (unsigned j = 0, size = iti->second.size(); j < size; j++)
  {
    unsigned inst_id = iti->second[j];
    Assert(d_inst_id_to_term.find(inst_id) != d_inst_id_to_term.end());
    Node inst_term = d_inst_id_to_term[inst_id];
    Node alit = d_inst_id_to_alit[inst_id];
    // try instantiation pv -> inst_term
    TermProperties pv_prop_bv;
    Trace("cegqi-bv") << "*** try " << pv << " -> " << inst_term << std::endl;
    d_var_to_curr_inst_id[pv] = inst_id;
    ci->markSolved(alit);
    if (ci->constructInstantiationInc(
            pv, inst_term, pv_prop_bv, sf, revertOnSuccess))
    {
      ret = true;
    }
    ci->markSolved(alit, false);
    // we are done unless we try multiple instances
    if (!tryMultipleInst)
    {
      break;
    }
  }
  if (ret)
  {
    return true;
  }
  Trace("cegqi-bv") << "...failed to add instantiation for " << pv << std::endl;
  d_var_to_curr_inst_id.erase(pv);

  return false;
}

Node BvInstantiator::rewriteAssertionForSolvePv(CegInstantiator* ci,
                                                Node pv,
                                                Node lit)
{
  // result of rewriting the visited term
  std::stack<std::unordered_map<TNode, Node, TNodeHashFunction> > visited;
  visited.push(std::unordered_map<TNode, Node, TNodeHashFunction>());
  // whether the visited term contains pv
  std::unordered_map<TNode, bool, TNodeHashFunction> visited_contains_pv;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::unordered_map<TNode, Node, TNodeHashFunction> curr_subs;
  std::stack<std::stack<TNode> > visit;
  TNode cur;
  visit.push(std::stack<TNode>());
  visit.top().push(lit);
  do
  {
    cur = visit.top().top();
    visit.top().pop();
    it = visited.top().find(cur);

    if (it == visited.top().end())
    {
      std::unordered_map<TNode, Node, TNodeHashFunction>::iterator itc =
          curr_subs.find(cur);
      if (itc != curr_subs.end())
      {
        visited.top()[cur] = itc->second;
      }
      else
      {
        if (cur.getKind() == CHOICE)
        {
          // must replace variables of choice functions
          // with new variables to avoid variable
          // capture when considering substitutions
          // with multiple literals.
          Node bv = ci->getBoundVariable(cur[0][0].getType());
          // should not have captured variables
          Assert(curr_subs.find(cur[0][0]) == curr_subs.end());
          curr_subs[cur[0][0]] = bv;
          // we cannot cache the results of subterms
          // of this choice expression since we are
          // now in the context { cur[0][0] -> bv },
          // hence we push a context here
          visited.push(std::unordered_map<TNode, Node, TNodeHashFunction>());
          visit.push(std::stack<TNode>());
        }
        visited.top()[cur] = Node::null();
        visit.top().push(cur);
        for (unsigned i = 0; i < cur.getNumChildren(); i++)
        {
          visit.top().push(cur[i]);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      bool contains_pv = (cur == pv);
      for (unsigned i = 0; i < cur.getNumChildren(); i++)
      {
        it = visited.top().find(cur[i]);
        Assert(it != visited.top().end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur[i] != it->second;
        children.push_back(it->second);
        contains_pv = contains_pv || visited_contains_pv[cur[i]];
      }
      // careful that rewrites above do not affect whether this term contains pv
      visited_contains_pv[cur] = contains_pv;

      // rewrite the term
      ret = rewriteTermForSolvePv(pv, cur, children, visited_contains_pv);

      // return original if the above function does not produce a result
      if (ret.isNull())
      {
        if (childChanged)
        {
          ret = NodeManager::currentNM()->mkNode(cur.getKind(), children);
        }
        else
        {
          ret = cur;
        }
      }

      /* We need to update contains_pv also for rewritten nodes, since
       * the normalizePv* functions rely on the information if pv occurs in a
       * rewritten node or not. */
      if (ret != cur)
      {
        contains_pv = (ret == pv);
        for (unsigned i = 0, size = ret.getNumChildren(); i < size; ++i)
        {
          contains_pv = contains_pv || visited_contains_pv[ret[i]];
        }
        visited_contains_pv[ret] = contains_pv;
      }

      // if was choice, pop context
      if (cur.getKind() == CHOICE)
      {
        Assert(curr_subs.find(cur[0][0]) != curr_subs.end());
        curr_subs.erase(cur[0][0]);
        visited.pop();
        visit.pop();
        Assert(visited.size() == visit.size());
        Assert(!visit.empty());
      }

      visited.top()[cur] = ret;
    }
  } while (!visit.top().empty());
  Assert(visited.size() == 1);
  Assert(visited.top().find(lit) != visited.top().end());
  Assert(!visited.top().find(lit)->second.isNull());

  Node result = visited.top()[lit];

  if (Trace.isOn("cegqi-bv-nl"))
  {
    std::vector<TNode> trace_visit;
    std::unordered_set<TNode, TNodeHashFunction> trace_visited;

    trace_visit.push_back(result);
    do
    {
      cur = trace_visit.back();
      trace_visit.pop_back();

      if (trace_visited.find(cur) == trace_visited.end())
      {
        trace_visited.insert(cur);
        trace_visit.insert(trace_visit.end(), cur.begin(), cur.end());
      }
      else if (cur == pv)
      {
        Trace("cegqi-bv-nl")
            << "NONLINEAR LITERAL for " << pv << " : " << lit << std::endl;
      }
    } while (!trace_visit.empty());
  }

  return result;
}

/**
 * Determine coefficient of pv in term n, where n has the form pv, -pv, pv * t,
 * or -pv * t. Extracting the coefficient of multiplications only succeeds if
 * the multiplication are normalized with normalizePvMult.
 *
 * If sucessful it returns
 *   1    if n ==  pv,
 *  -1    if n == -pv,
 *   t    if n ==  pv * t,
 *  -t    if n == -pv * t.
 * If n is not a linear term, a null node is returned.
 */
static Node getPvCoeff(TNode pv, TNode n)
{
  bool neg = false;
  Node coeff;

  if (n.getKind() == BITVECTOR_NEG)
  {
    neg = true;
    n = n[0];
  }

  if (n == pv)
  {
    coeff = bv::utils::mkOne(bv::utils::getSize(pv));
  }
  /* All multiplications are normalized to pv * (t1 * t2). */
  else if (n.getKind() == BITVECTOR_MULT && n.getAttribute(BvLinearAttribute()))
  {
    Assert(n.getNumChildren() == 2);
    Assert(n[0] == pv);
    coeff = n[1];
  }
  else /* n is in no form to extract the coefficient for pv */
  {
    Trace("cegqi-bv-nl") << "Cannot extract coefficient for " << pv << " in "
                         << n << std::endl;
    return Node::null();
  }
  Assert(!coeff.isNull());

  if (neg) return NodeManager::currentNM()->mkNode(BITVECTOR_NEG, coeff);
  return coeff;
}

/**
 * Normalizes the children of a BITVECTOR_MULT w.r.t. pv. contains_pv marks
 * terms in which pv occurs.
 * For example,
 *
 *  a * -pv * b * c
 *
 * is rewritten to
 *
 *  pv * -(a * b * c)
 *
 * Returns the normalized node if the resulting term is linear w.r.t. pv and
 * a null node otherwise. If pv does not occur in children it returns a
 * multiplication over children.
 */
static Node normalizePvMult(
    TNode pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  bool neg, neg_coeff = false;
  bool found_pv = false;
  NodeManager* nm;
  NodeBuilder<> nb(BITVECTOR_MULT);
  BvLinearAttribute is_linear;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (!found_pv && nc == pv)
    {
      found_pv = true;
      neg_coeff = neg;
      continue;
    }
    else if (!found_pv && nc.getKind() == BITVECTOR_MULT
             && nc.getAttribute(is_linear))
    {
      Assert(nc.getNumChildren() == 2);
      Assert(nc[0] == pv);
      Assert(!contains_pv[nc[1]]);
      found_pv = true;
      neg_coeff = neg;
      nb << nc[1];
      continue;
    }
    return Node::null(); /* non-linear */
  }
  Assert(nb.getNumChildren() > 0);

  Node coeff = (nb.getNumChildren() == 1) ? nb[0] : nb.constructNode();
  if (neg_coeff)
  {
    coeff = nm->mkNode(BITVECTOR_NEG, coeff);
  }
  coeff = Rewriter::rewrite(coeff);
  unsigned size_coeff = bv::utils::getSize(coeff);
  Node zero = bv::utils::mkZero(size_coeff);
  if (coeff == zero)
  {
    return zero;
  }
  Node result;
  if (found_pv)
  {
    if (coeff == bv::utils::mkOne(size_coeff))
    {
      return pv;
    }
    result = nm->mkNode(BITVECTOR_MULT, pv, coeff);
    contains_pv[result] = true;
    result.setAttribute(is_linear, true);
  }
  else
  {
    result = coeff;
  }
  return result;
}

#ifdef CVC4_ASSERTIONS
static bool isLinearPlus(
    TNode n,
    TNode pv,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  Node coeff;
  Assert(n.getAttribute(BvLinearAttribute()));
  Assert(n.getNumChildren() == 2);
  if (n[0] != pv)
  {
    Assert(n[0].getKind() == BITVECTOR_MULT);
    Assert(n[0].getNumChildren() == 2);
    Assert(n[0][0] == pv);
    Assert(!contains_pv[n[0][1]]);
  }
  Assert(!contains_pv[n[1]]);
  coeff = getPvCoeff(pv, n[0]);
  Assert(!coeff.isNull());
  Assert(!contains_pv[coeff]);
  return true;
}
#endif

/**
 * Normalizes the children of a BITVECTOR_PLUS w.r.t. pv. contains_pv marks
 * terms in which pv occurs.
 * For example,
 *
 *  a * pv + b + c * -pv
 *
 * is rewritten to
 *
 *  pv * (a - c) + b
 *
 * Returns the normalized node if the resulting term is linear w.r.t. pv and
 * a null node otherwise. If pv does not occur in children it returns an
 * addition over children.
 */
static Node normalizePvPlus(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  NodeManager* nm;
  NodeBuilder<> nb_c(BITVECTOR_PLUS);
  NodeBuilder<> nb_l(BITVECTOR_PLUS);
  BvLinearAttribute is_linear;
  bool neg;

  nm = NodeManager::currentNM();
  for (TNode nc : children)
  {
    if (!contains_pv[nc])
    {
      nb_l << nc;
      continue;
    }

    neg = false;
    if (nc.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      nc = nc[0];
    }

    if (nc == pv
        || (nc.getKind() == BITVECTOR_MULT && nc.getAttribute(is_linear)))
    {
      Node coeff = getPvCoeff(pv, nc);
      Assert(!coeff.isNull());
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
      }
      nb_c << coeff;
      continue;
    }
    else if (nc.getKind() == BITVECTOR_PLUS && nc.getAttribute(is_linear))
    {
      Assert(isLinearPlus(nc, pv, contains_pv));
      Node coeff = getPvCoeff(pv, nc[0]);
      Assert(!coeff.isNull());
      Node leaf = nc[1];
      if (neg)
      {
        coeff = nm->mkNode(BITVECTOR_NEG, coeff);
        leaf = nm->mkNode(BITVECTOR_NEG, leaf);
      }
      nb_c << coeff;
      nb_l << leaf;
      continue;
    }
    /* can't collect coefficients of 'pv' in 'cur' -> non-linear */
    return Node::null();
  }
  Assert(nb_c.getNumChildren() > 0 || nb_l.getNumChildren() > 0);

  Node pv_mult_coeffs, result;
  if (nb_c.getNumChildren() > 0)
  {
    Node coeffs = (nb_c.getNumChildren() == 1) ? nb_c[0] : nb_c.constructNode();
    coeffs = Rewriter::rewrite(coeffs);
    result = pv_mult_coeffs = normalizePvMult(pv, {pv, coeffs}, contains_pv);
  }

  if (nb_l.getNumChildren() > 0)
  {
    Node leafs = (nb_l.getNumChildren() == 1) ? nb_l[0] : nb_l.constructNode();
    leafs = Rewriter::rewrite(leafs);
    Node zero = bv::utils::mkZero(bv::utils::getSize(pv));
    /* pv * 0 + t --> t */
    if (pv_mult_coeffs.isNull() || pv_mult_coeffs == zero)
    {
      result = leafs;
    }
    else
    {
      result = nm->mkNode(BITVECTOR_PLUS, pv_mult_coeffs, leafs);
      contains_pv[result] = true;
      result.setAttribute(is_linear, true);
    }
  }
  Assert(!result.isNull());
  return result;
}

/**
 * Linearize an equality w.r.t. pv such that pv only occurs once. contains_pv
 * marks terms in which pv occurs.
 * For example, equality
 *
 *   -pv * a + b = c + pv
 *
 * rewrites to
 *
 *   pv * (-a - 1) = c - b.
 */
static Node normalizePvEqual(
    Node pv,
    const std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  Assert(children.size() == 2);

  NodeManager* nm = NodeManager::currentNM();
  BvLinearAttribute is_linear;
  Node coeffs[2], leafs[2];
  bool neg;
  TNode child;

  for (unsigned i = 0; i < 2; ++i)
  {
    child = children[i];
    neg = false;
    if (child.getKind() == BITVECTOR_NEG)
    {
      neg = true;
      child = child[0];
    }
    if (child.getAttribute(is_linear) || child == pv)
    {
      if (child.getKind() == BITVECTOR_PLUS)
      {
        Assert(isLinearPlus(child, pv, contains_pv));
        coeffs[i] = getPvCoeff(pv, child[0]);
        leafs[i] = child[1];
      }
      else
      {
        Assert(child.getKind() == BITVECTOR_MULT || child == pv);
        coeffs[i] = getPvCoeff(pv, child);
      }
    }
    if (neg)
    {
      if (!coeffs[i].isNull())
      {
        coeffs[i] = nm->mkNode(BITVECTOR_NEG, coeffs[i]);
      }
      if (!leafs[i].isNull())
      {
        leafs[i] = nm->mkNode(BITVECTOR_NEG, leafs[i]);
      }
    }
  }

  if (coeffs[0].isNull() || coeffs[1].isNull())
  {
    return Node::null();
  }

  Node coeff = nm->mkNode(BITVECTOR_SUB, coeffs[0], coeffs[1]);
  coeff = Rewriter::rewrite(coeff);
  std::vector<Node> mult_children = {pv, coeff};
  Node lhs = normalizePvMult(pv, mult_children, contains_pv);

  Node rhs;
  if (!leafs[0].isNull() && !leafs[1].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_SUB, leafs[1], leafs[0]);
  }
  else if (!leafs[0].isNull())
  {
    rhs = nm->mkNode(BITVECTOR_NEG, leafs[0]);
  }
  else if (!leafs[1].isNull())
  {
    rhs = leafs[1];
  }
  else
  {
    rhs = bv::utils::mkZero(bv::utils::getSize(pv));
  }
  rhs = Rewriter::rewrite(rhs);

  if (lhs == rhs)
  {
    return bv::utils::mkTrue();
  }

  Node result = lhs.eqNode(rhs);
  contains_pv[result] = true;
  return result;
}

Node BvInstantiator::rewriteTermForSolvePv(
    Node pv,
    Node n,
    std::vector<Node>& children,
    std::unordered_map<TNode, bool, TNodeHashFunction>& contains_pv)
{
  NodeManager* nm = NodeManager::currentNM();

  // [1] rewrite cases of non-invertible operators

  if (n.getKind() == EQUAL)
  {
    TNode lhs = children[0];
    TNode rhs = children[1];

    /* rewrite: x * x = x -> x < 2 */
    if ((lhs == pv && rhs.getKind() == BITVECTOR_MULT && rhs[0] == pv
         && rhs[1] == pv)
        || (rhs == pv && lhs.getKind() == BITVECTOR_MULT && lhs[0] == pv
            && lhs[1] == pv))
    {
      return nm->mkNode(
          BITVECTOR_ULT,
          pv,
          bv::utils::mkConst(BitVector(bv::utils::getSize(pv), Integer(2))));
    }

    if (options::cbqiBvLinearize() && contains_pv[lhs] && contains_pv[rhs])
    {
      Node result = normalizePvEqual(pv, children, contains_pv);
      if (!result.isNull())
      {
        Trace("cegqi-bv-nl")
            << "Normalize " << n << " to " << result << std::endl;
      }
      else
      {
        Trace("cegqi-bv-nl")
            << "Nonlinear " << n.getKind() << " " << n << std::endl;
      }
      return result;
    }
  }
  else if (n.getKind() == BITVECTOR_MULT || n.getKind() == BITVECTOR_PLUS)
  {
    if (options::cbqiBvLinearize() && contains_pv[n])
    {
      Node result;
      if (n.getKind() == BITVECTOR_MULT)
      {
        result = normalizePvMult(pv, children, contains_pv);
      }
      else
      {
        result = normalizePvPlus(pv, children, contains_pv);
      }
      if (!result.isNull())
      {
        Trace("cegqi-bv-nl")
            << "Normalize " << n << " to " << result << std::endl;
        return result;
      }
      else
      {
        Trace("cegqi-bv-nl")
            << "Nonlinear " << n.getKind() << " " << n << std::endl;
      }
    }
  }

  // [2] try to rewrite non-linear literals -> linear literals

  return Node::null();
}

/** sort bv extract interval
 *
 * This sorts lists of bitvector extract terms where
 * ((_ extract i1 i2) t) < ((_ extract j1 j2) t)
 * if i1>j1 or i1=j1 and i2>j2.
 */
struct SortBvExtractInterval
{
  bool operator()(Node i, Node j)
  {
    Assert(i.getKind() == BITVECTOR_EXTRACT);
    Assert(j.getKind() == BITVECTOR_EXTRACT);
    BitVectorExtract ie = i.getOperator().getConst<BitVectorExtract>();
    BitVectorExtract je = j.getOperator().getConst<BitVectorExtract>();
    if (ie.high > je.high)
    {
      return true;
    }
    else if (ie.high == je.high)
    {
      Assert(ie.low != je.low);
      return ie.low > je.low;
    }
    return false;
  }
};

void BvInstantiatorPreprocess::registerCounterexampleLemma(
    std::vector<Node>& lems, std::vector<Node>& ce_vars)
{
  // new variables
  std::vector<Node> vars;
  // new lemmas
  std::vector<Node> new_lems;

  if (options::cbqiBvRmExtract())
  {
    NodeManager* nm = NodeManager::currentNM();
    Trace("cegqi-bv-pp") << "-----remove extracts..." << std::endl;
    // map from terms to bitvector extracts applied to that term
    std::map<Node, std::vector<Node> > extract_map;
    std::unordered_set<TNode, TNodeHashFunction> visited;
    for (unsigned i = 0, size = lems.size(); i < size; i++)
    {
      Trace("cegqi-bv-pp-debug2")
          << "Register ce lemma # " << i << " : " << lems[i] << std::endl;
      collectExtracts(lems[i], extract_map, visited);
    }
    for (std::pair<const Node, std::vector<Node> >& es : extract_map)
    {
      // sort based on the extract start position
      std::vector<Node>& curr_vec = es.second;

      SortBvExtractInterval sbei;
      std::sort(curr_vec.begin(), curr_vec.end(), sbei);

      unsigned width = es.first.getType().getBitVectorSize();

      // list of points b such that:
      //   b>0 and we must start a segment at (b-1)  or  b==0
      std::vector<unsigned> boundaries;
      boundaries.push_back(width);
      boundaries.push_back(0);

      Trace("cegqi-bv-pp") << "For term " << es.first << " : " << std::endl;
      for (unsigned i = 0, size = curr_vec.size(); i < size; i++)
      {
        Trace("cegqi-bv-pp") << "  " << i << " : " << curr_vec[i] << std::endl;
        BitVectorExtract e =
            curr_vec[i].getOperator().getConst<BitVectorExtract>();
        if (std::find(boundaries.begin(), boundaries.end(), e.high + 1)
            == boundaries.end())
        {
          boundaries.push_back(e.high + 1);
        }
        if (std::find(boundaries.begin(), boundaries.end(), e.low)
            == boundaries.end())
        {
          boundaries.push_back(e.low);
        }
      }
      std::sort(boundaries.rbegin(), boundaries.rend());

      // make the extract variables
      std::vector<Node> children;
      for (unsigned i = 1; i < boundaries.size(); i++)
      {
        Assert(boundaries[i - 1] > 0);
        Node ex = bv::utils::mkExtract(
            es.first, boundaries[i - 1] - 1, boundaries[i]);
        Node var =
            nm->mkSkolem("ek",
                         ex.getType(),
                         "variable to represent disjoint extract region");
        children.push_back(var);
        vars.push_back(var);
      }

      Node conc = nm->mkNode(kind::BITVECTOR_CONCAT, children);
      Assert(conc.getType() == es.first.getType());
      Node eq_lem = conc.eqNode(es.first);
      Trace("cegqi-bv-pp") << "Introduced : " << eq_lem << std::endl;
      new_lems.push_back(eq_lem);
      Trace("cegqi-bv-pp") << "...finished processing extracts for term "
                           << es.first << std::endl;
    }
    Trace("cegqi-bv-pp") << "-----done remove extracts" << std::endl;
  }

  if (!vars.empty())
  {
    // could try applying subs -> vars here
    // in practice, this led to worse performance

    Trace("cegqi-bv-pp") << "Adding " << new_lems.size() << " lemmas..."
                         << std::endl;
    lems.insert(lems.end(), new_lems.begin(), new_lems.end());
    Trace("cegqi-bv-pp") << "Adding " << vars.size() << " variables..."
                         << std::endl;
    ce_vars.insert(ce_vars.end(), vars.begin(), vars.end());
  }
}

void BvInstantiatorPreprocess::collectExtracts(
    Node lem,
    std::map<Node, std::vector<Node> >& extract_map,
    std::unordered_set<TNode, TNodeHashFunction>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(lem);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() != FORALL)
      {
        if (cur.getKind() == BITVECTOR_EXTRACT)
        {
          if (cur[0].getKind() == INST_CONSTANT)
          {
            extract_map[cur[0]].push_back(cur);
          }
        }

        for (const Node& nc : cur)
        {
          visit.push_back(nc);
        }
      }
    }
  } while (!visit.empty());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
