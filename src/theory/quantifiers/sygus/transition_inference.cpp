/*********************                                                        */
/*! \file transition_inference.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implmentation of utility for inferring whether a synthesis conjecture
 ** encodes a transition system.
 **
 **/
#include "theory/quantifiers/sygus/transition_inference.h"

#include "expr/node_algorithm.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

bool DetTrace::DetTraceTrie::add(Node loc, const std::vector<Node>& val)
{
  DetTraceTrie* curr = this;
  for (const Node& v : val)
  {
    curr = &(curr->d_children[v]);
  }
  if (curr->d_children.empty())
  {
    curr->d_children[loc].clear();
    return true;
  }
  return false;
}

Node DetTrace::DetTraceTrie::constructFormula(const std::vector<Node>& vars,
                                              unsigned index)
{
  NodeManager* nm = NodeManager::currentNM();
  if (index == vars.size())
  {
    return nm->mkConst(true);
  }
  std::vector<Node> disj;
  for (std::pair<const Node, DetTraceTrie>& p : d_children)
  {
    Node eq = vars[index].eqNode(p.first);
    if (index < vars.size() - 1)
    {
      Node conc = p.second.constructFormula(vars, index + 1);
      disj.push_back(nm->mkNode(AND, eq, conc));
    }
    else
    {
      disj.push_back(eq);
    }
  }
  Assert(!disj.empty());
  return disj.size() == 1 ? disj[0] : nm->mkNode(OR, disj);
}

bool DetTrace::increment(Node loc, std::vector<Node>& vals)
{
  if (d_trie.add(loc, vals))
  {
    for (unsigned i = 0, vsize = vals.size(); i < vsize; i++)
    {
      d_curr[i] = vals[i];
    }
    return true;
  }
  return false;
}

Node DetTrace::constructFormula(const std::vector<Node>& vars)
{
  return d_trie.constructFormula(vars);
}

void DetTrace::print(const char* c) const
{
  for (const Node& n : d_curr)
  {
    Trace(c) << n << " ";
  }
}

Node TransitionInference::getFunction() const { return d_func; }

void TransitionInference::getVariables(std::vector<Node>& vars) const
{
  vars.insert(vars.end(), d_vars.begin(), d_vars.end());
}

Node TransitionInference::getPreCondition() const { return d_pre.d_this; }
Node TransitionInference::getPostCondition() const { return d_post.d_this; }
Node TransitionInference::getTransitionRelation() const
{
  return d_trans.d_this;
}

void TransitionInference::getConstantSubstitution(
    const std::vector<Node>& vars,
    const std::vector<Node>& disjuncts,
    std::vector<Node>& const_var,
    std::vector<Node>& const_subs,
    bool reqPol)
{
  for (const Node& d : disjuncts)
  {
    Node sn;
    if (!const_var.empty())
    {
      sn = d.substitute(const_var.begin(),
                        const_var.end(),
                        const_subs.begin(),
                        const_subs.end());
      sn = Rewriter::rewrite(sn);
    }
    else
    {
      sn = d;
    }
    bool slit_pol = sn.getKind() != NOT;
    Node slit = sn.getKind() == NOT ? sn[0] : sn;
    if (slit.getKind() == EQUAL && slit_pol == reqPol)
    {
      // check if it is a variable equality
      TNode v;
      Node s;
      for (unsigned r = 0; r < 2; r++)
      {
        if (std::find(vars.begin(), vars.end(), slit[r]) != vars.end())
        {
          if (!expr::hasSubterm(slit[1 - r], slit[r]))
          {
            v = slit[r];
            s = slit[1 - r];
            break;
          }
        }
      }
      if (v.isNull())
      {
        // solve for var
        std::map<Node, Node> msum;
        if (ArithMSum::getMonomialSumLit(slit, msum))
        {
          for (std::pair<const Node, Node>& m : msum)
          {
            if (std::find(vars.begin(), vars.end(), m.first) != vars.end())
            {
              Node veq_c;
              Node val;
              int ires = ArithMSum::isolate(m.first, msum, veq_c, val, EQUAL);
              if (ires != 0 && veq_c.isNull()
                  && !expr::hasSubterm(val, m.first))
              {
                v = m.first;
                s = val;
              }
            }
          }
        }
      }
      if (!v.isNull())
      {
        TNode ts = s;
        for (unsigned k = 0, csize = const_subs.size(); k < csize; k++)
        {
          const_subs[k] = Rewriter::rewrite(const_subs[k].substitute(v, ts));
        }
        Trace("cegqi-inv-debug2")
            << "...substitution : " << v << " -> " << s << std::endl;
        const_var.push_back(v);
        const_subs.push_back(s);
      }
    }
  }
}

void TransitionInference::process(Node n, Node f)
{
  // set the function
  d_func = f;
  process(n);
}

void TransitionInference::process(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  d_complete = true;
  d_trivial = true;
  std::vector<Node> n_check;
  if (n.getKind() == AND)
  {
    for (const Node& nc : n)
    {
      n_check.push_back(nc);
    }
  }
  else
  {
    n_check.push_back(n);
  }
  for (const Node& nn : n_check)
  {
    std::map<bool, std::map<Node, bool> > visited;
    std::map<bool, Node> terms;
    std::vector<Node> disjuncts;
    Trace("cegqi-inv") << "TransitionInference : Process disjunct : " << nn
                       << std::endl;
    if (!processDisjunct(nn, terms, disjuncts, visited, true))
    {
      d_complete = false;
      continue;
    }
    if (terms.empty())
    {
      continue;
    }
    Node curr;
    // The component that this disjunct contributes to, where
    // 1 : pre-condition, -1 : post-condition, 0 : transition relation
    int comp_num;
    std::map<bool, Node>::iterator itt = terms.find(false);
    if (itt != terms.end())
    {
      curr = itt->second;
      if (terms.find(true) != terms.end())
      {
        comp_num = 0;
      }
      else
      {
        comp_num = -1;
      }
    }
    else
    {
      curr = terms[true];
      comp_num = 1;
    }
    Trace("cegqi-inv-debug2") << "  normalize based on " << curr << std::endl;
    std::vector<Node> vars;
    std::vector<Node> svars;
    getNormalizedSubstitution(curr, d_vars, vars, svars, disjuncts);
    for (unsigned j = 0, dsize = disjuncts.size(); j < dsize; j++)
    {
      Trace("cegqi-inv-debug2") << "  apply " << disjuncts[j] << std::endl;
      disjuncts[j] = Rewriter::rewrite(disjuncts[j].substitute(
          vars.begin(), vars.end(), svars.begin(), svars.end()));
      Trace("cegqi-inv-debug2") << "  ..." << disjuncts[j] << std::endl;
    }
    std::vector<Node> const_var;
    std::vector<Node> const_subs;
    if (comp_num == 0)
    {
      // transition
      Assert(terms.find(true) != terms.end());
      Node next = terms[true];
      next = Rewriter::rewrite(next.substitute(
          vars.begin(), vars.end(), svars.begin(), svars.end()));
      Trace("cegqi-inv-debug")
          << "transition next predicate : " << next << std::endl;
      // make the primed variables if we have not already
      if (d_prime_vars.empty())
      {
        for (unsigned j = 0, nchild = next.getNumChildren(); j < nchild; j++)
        {
          Node v = nm->mkSkolem(
              "ir", next[j].getType(), "template inference rev argument");
          d_prime_vars.push_back(v);
        }
      }
      // normalize the other direction
      Trace("cegqi-inv-debug2") << "  normalize based on " << next << std::endl;
      std::vector<Node> rvars;
      std::vector<Node> rsvars;
      getNormalizedSubstitution(next, d_prime_vars, rvars, rsvars, disjuncts);
      Assert(rvars.size() == rsvars.size());
      for (unsigned j = 0, dsize = disjuncts.size(); j < dsize; j++)
      {
        Trace("cegqi-inv-debug2") << "  apply " << disjuncts[j] << std::endl;
        disjuncts[j] = Rewriter::rewrite(disjuncts[j].substitute(
            rvars.begin(), rvars.end(), rsvars.begin(), rsvars.end()));
        Trace("cegqi-inv-debug2") << "  ..." << disjuncts[j] << std::endl;
      }
      getConstantSubstitution(
          d_prime_vars, disjuncts, const_var, const_subs, false);
    }
    else
    {
      getConstantSubstitution(d_vars, disjuncts, const_var, const_subs, false);
    }
    Node res;
    if (disjuncts.empty())
    {
      res = nm->mkConst(false);
    }
    else if (disjuncts.size() == 1)
    {
      res = disjuncts[0];
    }
    else
    {
      res = nm->mkNode(OR, disjuncts);
    }
    if (expr::hasBoundVar(res))
    {
      Trace("cegqi-inv-debug2") << "...failed, free variable." << std::endl;
      d_complete = false;
      continue;
    }
    Trace("cegqi-inv") << "*** inferred "
                       << (comp_num == 1 ? "pre"
                                         : (comp_num == -1 ? "post" : "trans"))
                       << "-condition : " << res << std::endl;
    Component& c =
        (comp_num == 1 ? d_pre : (comp_num == -1 ? d_post : d_trans));
    c.d_conjuncts.push_back(res);
    if (!const_var.empty())
    {
      bool has_const_eq = const_var.size() == d_vars.size();
      Trace("cegqi-inv") << "    with constant substitution, complete = "
                         << has_const_eq << " : " << std::endl;
      for (unsigned i = 0, csize = const_var.size(); i < csize; i++)
      {
        Trace("cegqi-inv") << "      " << const_var[i] << " -> "
                           << const_subs[i] << std::endl;
        if (has_const_eq)
        {
          c.d_const_eq[res][const_var[i]] = const_subs[i];
        }
      }
      Trace("cegqi-inv") << "...size = " << const_var.size()
                         << ", #vars = " << d_vars.size() << std::endl;
    }
  }

  // finalize the components
  for (int i = -1; i <= 1; i++)
  {
    Component& c = (i == 1 ? d_pre : (i == -1 ? d_post : d_trans));
    Node ret;
    if (c.d_conjuncts.empty())
    {
      ret = nm->mkConst(true);
    }
    else if (c.d_conjuncts.size() == 1)
    {
      ret = c.d_conjuncts[0];
    }
    else
    {
      ret = nm->mkNode(AND, c.d_conjuncts);
    }
    if (i == 0 || i == 1)
    {
      // pre-condition and transition are negated
      ret = TermUtil::simpleNegate(ret);
    }
    c.d_this = ret;
  }
}
void TransitionInference::getNormalizedSubstitution(
    Node curr,
    const std::vector<Node>& pvars,
    std::vector<Node>& vars,
    std::vector<Node>& subs,
    std::vector<Node>& disjuncts)
{
  for (unsigned j = 0, nchild = curr.getNumChildren(); j < nchild; j++)
  {
    if (curr[j].getKind() == BOUND_VARIABLE)
    {
      // if the argument is a bound variable, add to the renaming
      vars.push_back(curr[j]);
      subs.push_back(pvars[j]);
    }
    else
    {
      // otherwise, treat as a constraint on the variable
      // For example, this transforms e.g. a precondition clause
      // I( 0, 1 ) to x1 != 0 OR x2 != 1 OR I( x1, x2 ).
      Node eq = curr[j].eqNode(pvars[j]);
      disjuncts.push_back(eq.negate());
    }
  }
}

bool TransitionInference::processDisjunct(
    Node n,
    std::map<bool, Node>& terms,
    std::vector<Node>& disjuncts,
    std::map<bool, std::map<Node, bool> >& visited,
    bool topLevel)
{
  if (visited[topLevel].find(n) != visited[topLevel].end())
  {
    return true;
  }
  visited[topLevel][n] = true;
  bool childTopLevel = n.getKind() == OR && topLevel;
  // if another part mentions UF or a free variable, then fail
  bool lit_pol = n.getKind() != NOT;
  Node lit = n.getKind() == NOT ? n[0] : n;
  // is it an application of the function-to-synthesize? Yes if we haven't
  // encountered a function or if it matches the existing d_func.
  if (lit.getKind() == APPLY_UF
      && (d_func.isNull() || lit.getOperator() == d_func))
  {
    Node op = lit.getOperator();
    // initialize the variables
    if (d_trivial)
    {
      d_trivial = false;
      d_func = op;
      Trace("cegqi-inv-debug") << "Use " << op << " with args ";
      NodeManager* nm = NodeManager::currentNM();
      for (const Node& l : lit)
      {
        Node v = nm->mkSkolem("i", l.getType(), "template inference argument");
        d_vars.push_back(v);
        Trace("cegqi-inv-debug") << v << " ";
      }
      Trace("cegqi-inv-debug") << std::endl;
    }
    Assert(!d_func.isNull());
    if (topLevel)
    {
      if (terms.find(lit_pol) == terms.end())
      {
        terms[lit_pol] = lit;
        return true;
      }
      else
      {
        Trace("cegqi-inv-debug")
            << "...failed, repeated inv-app : " << lit << std::endl;
        return false;
      }
    }
    Trace("cegqi-inv-debug")
        << "...failed, non-entailed inv-app : " << lit << std::endl;
    return false;
  }
  else if (topLevel && !childTopLevel)
  {
    disjuncts.push_back(n);
  }
  for (const Node& nc : n)
  {
    if (!processDisjunct(nc, terms, disjuncts, visited, childTopLevel))
    {
      return false;
    }
  }
  return true;
}

TraceIncStatus TransitionInference::initializeTrace(DetTrace& dt,
                                                    Node loc,
                                                    bool fwd)
{
  Component& c = fwd ? d_pre : d_post;
  Assert(c.has(loc));
  std::map<Node, std::map<Node, Node> >::iterator it = c.d_const_eq.find(loc);
  if (it != c.d_const_eq.end())
  {
    std::vector<Node> next;
    for (const Node& v : d_vars)
    {
      Assert(it->second.find(v) != it->second.end());
      next.push_back(it->second[v]);
      dt.d_curr.push_back(it->second[v]);
    }
    Trace("cegqi-inv-debug2") << "dtrace : initial increment" << std::endl;
    bool ret = dt.increment(loc, next);
    AlwaysAssert(ret);
    return TRACE_INC_SUCCESS;
  }
  return TRACE_INC_INVALID;
}

TraceIncStatus TransitionInference::incrementTrace(DetTrace& dt,
                                                   Node loc,
                                                   bool fwd)
{
  Assert(d_trans.has(loc));
  // check if it satisfies the pre/post condition
  Node cc = fwd ? getPostCondition() : getPreCondition();
  Assert(!cc.isNull());
  Node ccr = Rewriter::rewrite(cc.substitute(
      d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end()));
  if (ccr.isConst())
  {
    if (ccr.getConst<bool>() == (fwd ? false : true))
    {
      Trace("cegqi-inv-debug2") << "dtrace : counterexample" << std::endl;
      return TRACE_INC_CEX;
    }
  }

  // terminates?
  Node c = getTransitionRelation();
  Assert(!c.isNull());

  Assert(d_vars.size() == dt.d_curr.size());
  Node cr = Rewriter::rewrite(c.substitute(
      d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end()));
  if (cr.isConst())
  {
    if (!cr.getConst<bool>())
    {
      Trace("cegqi-inv-debug2") << "dtrace : terminated" << std::endl;
      return TRACE_INC_TERMINATE;
    }
    return TRACE_INC_INVALID;
  }
  if (!fwd)
  {
    // only implemented in forward direction
    Assert(false);
    return TRACE_INC_INVALID;
  }
  Component& cm = d_trans;
  std::map<Node, std::map<Node, Node> >::iterator it = cm.d_const_eq.find(loc);
  if (it == cm.d_const_eq.end())
  {
    return TRACE_INC_INVALID;
  }
  std::vector<Node> next;
  for (const Node& pv : d_prime_vars)
  {
    Assert(it->second.find(pv) != it->second.end());
    Node pvs = it->second[pv];
    Assert(d_vars.size() == dt.d_curr.size());
    Node pvsr = Rewriter::rewrite(pvs.substitute(
        d_vars.begin(), d_vars.end(), dt.d_curr.begin(), dt.d_curr.end()));
    next.push_back(pvsr);
  }
  if (dt.increment(loc, next))
  {
    Trace("cegqi-inv-debug2") << "dtrace : success increment" << std::endl;
    return TRACE_INC_SUCCESS;
  }
  // looped
  Trace("cegqi-inv-debug2") << "dtrace : looped" << std::endl;
  return TRACE_INC_TERMINATE;
}

TraceIncStatus TransitionInference::initializeTrace(DetTrace& dt, bool fwd)
{
  Trace("cegqi-inv-debug2") << "Initialize trace" << std::endl;
  Component& c = fwd ? d_pre : d_post;
  if (c.d_conjuncts.size() == 1)
  {
    return initializeTrace(dt, c.d_conjuncts[0], fwd);
  }
  return TRACE_INC_INVALID;
}

TraceIncStatus TransitionInference::incrementTrace(DetTrace& dt, bool fwd)
{
  if (d_trans.d_conjuncts.size() == 1)
  {
    return incrementTrace(dt, d_trans.d_conjuncts[0], fwd);
  }
  return TRACE_INC_INVALID;
}

Node TransitionInference::constructFormulaTrace(DetTrace& dt) const
{
  return dt.constructFormula(d_vars);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
