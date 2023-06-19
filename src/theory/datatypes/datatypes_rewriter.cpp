/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of rewriter for the theory of (co)inductive datatypes.
 */

#include "theory/datatypes/datatypes_rewriter.h"

#include "expr/ascription_type.h"
#include "expr/codatatype_bound_variable.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/elim_shadow_converter.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "tuple_utils.h"
#include "util/rational.h"

using namespace cvc5::internal;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace datatypes {

DatatypesRewriter::DatatypesRewriter(Evaluator* sygusEval, const Options& opts)
    : d_sygusEval(sygusEval), d_opts(opts)
{
}

RewriteResponse DatatypesRewriter::postRewrite(TNode in)
{
  Trace("datatypes-rewrite-debug") << "post-rewriting " << in << std::endl;
  Kind kind = in.getKind();
  NodeManager* nm = NodeManager::currentNM();
  if (kind == kind::APPLY_CONSTRUCTOR)
  {
    return rewriteConstructor(in);
  }
  else if (kind == kind::APPLY_SELECTOR)
  {
    return rewriteSelector(in);
  }
  else if (kind == kind::APPLY_TESTER)
  {
    return rewriteTester(in);
  }
  else if (kind == APPLY_UPDATER)
  {
    return rewriteUpdater(in);
  }
  else if (kind == kind::DT_SIZE)
  {
    if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
    {
      std::vector<Node> children;
      for (unsigned i = 0, size = in [0].getNumChildren(); i < size; i++)
      {
        if (in[0][i].getType().isDatatype())
        {
          children.push_back(nm->mkNode(kind::DT_SIZE, in[0][i]));
        }
      }
      TNode constructor = in[0].getOperator();
      size_t constructorIndex = utils::indexOf(constructor);
      const DType& dt = utils::datatypeOf(constructor);
      const DTypeConstructor& c = dt[constructorIndex];
      unsigned weight = c.getWeight();
      children.push_back(nm->mkConstInt(Rational(weight)));
      Node res =
          children.size() == 1 ? children[0] : nm->mkNode(kind::ADD, children);
      Trace("datatypes-rewrite")
          << "DatatypesRewriter::postRewrite: rewrite size " << in << " to "
          << res << std::endl;
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (kind == kind::DT_HEIGHT_BOUND)
  {
    if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
    {
      std::vector<Node> children;
      Node res;
      Rational r = in[1].getConst<Rational>();
      Rational rmo = Rational(r - Rational(1));
      for (unsigned i = 0, size = in [0].getNumChildren(); i < size; i++)
      {
        if (in[0][i].getType().isDatatype())
        {
          if (r.isZero())
          {
            res = nm->mkConst(false);
            break;
          }
          children.push_back(
              nm->mkNode(kind::DT_HEIGHT_BOUND, in[0][i], nm->mkConstInt(rmo)));
        }
      }
      if (res.isNull())
      {
        res = children.size() == 0
                  ? nm->mkConst(true)
                  : (children.size() == 1 ? children[0]
                                          : nm->mkNode(kind::AND, children));
      }
      Trace("datatypes-rewrite")
          << "DatatypesRewriter::postRewrite: rewrite height " << in << " to "
          << res << std::endl;
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (kind == kind::DT_SIZE_BOUND)
  {
    if (in[0].isConst())
    {
      Node res = nm->mkNode(kind::LEQ, nm->mkNode(kind::DT_SIZE, in[0]), in[1]);
      return RewriteResponse(REWRITE_AGAIN_FULL, res);
    }
  }
  else if (kind == DT_SYGUS_EVAL)
  {
    // sygus evaluation function
    Node ev = in[0];
    if (ev.getKind() == APPLY_CONSTRUCTOR)
    {
      Trace("dt-sygus-util") << "Rewrite " << in << " by unfolding...\n";
      Trace("dt-sygus-util") << "Type is " << in.getType() << std::endl;
      std::vector<Node> args;
      for (unsigned j = 1, nchild = in.getNumChildren(); j < nchild; j++)
      {
        args.push_back(in[j]);
      }
      Node ret = sygusToBuiltinEval(ev, args);
      Trace("dt-sygus-util") << "...got " << ret << "\n";
      Trace("dt-sygus-util") << "Type is " << ret.getType() << std::endl;
      Assert(in.getType() == ret.getType());
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }
  else if (kind == MATCH)
  {
    Trace("dt-rewrite-match") << "Rewrite match: " << in << std::endl;
    Node ret = expandMatch(in);
    Trace("dt-rewrite-match")
        << "Rewrite match: " << in << " ... " << ret << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }
  else if (kind == MATCH_BIND_CASE)
  {
    // eliminate shadowing
    Node retElimShadow = ElimShadowNodeConverter::eliminateShadow(in);
    if (retElimShadow != in)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, retElimShadow);
    }
  }
  else if (kind == TUPLE_PROJECT)
  {
    // returns a tuple that represents
    // (tuple ((_ tuple_select i_1) t) ... ((_ tuple_select i_n) t))
    // where each i_j is less than the length of t

    Trace("dt-rewrite-project") << "Rewrite project: " << in << std::endl;

    ProjectOp op = in.getOperator().getConst<ProjectOp>();
    std::vector<uint32_t> indices = op.getIndices();
    Node tuple = in[0];
    Node ret = TupleUtils::getTupleProjection(indices, tuple);

    Trace("dt-rewrite-project")
        << "Rewrite project: " << in << " ... " << ret << std::endl;
    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }

  if (kind == kind::EQUAL)
  {
    if (in[0] == in[1])
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    std::vector<Node> rew;
    if (utils::checkClash(in[0], in[1], rew))
    {
      Trace("datatypes-rewrite")
          << "Rewrite clashing equality " << in << " to false" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      //}else if( rew.size()==1 && rew[0]!=in ){
      //  Trace("datatypes-rewrite") << "Rewrite equality " << in << " to " <<
      //  rew[0] << std::endl;
      //  return RewriteResponse(REWRITE_AGAIN_FULL, rew[0] );
    }
    else if (in[1] < in[0])
    {
      Node ins = nm->mkNode(in.getKind(), in[1], in[0]);
      Trace("datatypes-rewrite")
          << "Swap equality " << in << " to " << ins << std::endl;
      return RewriteResponse(REWRITE_DONE, ins);
    }
    Trace("datatypes-rewrite-debug")
        << "Did not rewrite equality " << in << " " << in[0].getKind() << " "
        << in[1].getKind() << std::endl;
  }

  return RewriteResponse(REWRITE_DONE, in);
}
Node DatatypesRewriter::expandMatch(Node in)
{
  NodeManager* nm = NodeManager::currentNM();
  // ensure we've type checked
  TypeNode tin = in.getType();
  Node h = in[0];
  std::vector<Node> cases;
  std::vector<Node> rets;
  TypeNode t = h.getType();
  const DType& dt = t.getDType();
  for (size_t k = 1, nchild = in.getNumChildren(); k < nchild; k++)
  {
    Node c = in[k];
    Node cons;
    Kind ck = c.getKind();
    if (ck == MATCH_CASE)
    {
      Assert(c[0].getKind() == APPLY_CONSTRUCTOR);
      cons = c[0].getOperator();
    }
    else if (ck == MATCH_BIND_CASE)
    {
      if (c[1].getKind() == APPLY_CONSTRUCTOR)
      {
        cons = c[1].getOperator();
      }
    }
    else
    {
      AlwaysAssert(false) << "Bad case for match term";
    }
    size_t cindex = 0;
    // cons is null in the default case
    if (!cons.isNull())
    {
      cindex = utils::indexOf(cons);
    }
    Node body;
    if (ck == MATCH_CASE)
    {
      body = c[1];
    }
    else if (ck == MATCH_BIND_CASE)
    {
      std::vector<Node> vars;
      std::vector<Node> subs;
      if (cons.isNull())
      {
        Assert(c[1].getKind() == BOUND_VARIABLE);
        vars.push_back(c[1]);
        subs.push_back(h);
      }
      else
      {
        for (size_t i = 0, vsize = c[0].getNumChildren(); i < vsize; i++)
        {
          vars.push_back(c[0][i]);
          Node sc = nm->mkNode(APPLY_SELECTOR, dt[cindex][i].getSelector(), h);
          subs.push_back(sc);
        }
      }
      body =
          c[2].substitute(vars.begin(), vars.end(), subs.begin(), subs.end());
    }
    if (!cons.isNull())
    {
      cases.push_back(utils::mkTester(h, cindex, dt));
    }
    else
    {
      // variables have no constraints
      cases.push_back(nm->mkConst(true));
    }
    rets.push_back(body);
  }
  Assert(!cases.empty());
  // now make the ITE
  std::reverse(cases.begin(), cases.end());
  std::reverse(rets.begin(), rets.end());
  Node ret = rets[0];
  // notice that due to our type checker, either there is a variable pattern
  // or all constructors are present in the match.
  for (size_t i = 1, ncases = cases.size(); i < ncases; i++)
  {
    ret = nm->mkNode(ITE, cases[i], rets[i], ret);
  }
  return ret;
}

RewriteResponse DatatypesRewriter::preRewrite(TNode in)
{
  Trace("datatypes-rewrite-debug") << "pre-rewriting " << in << std::endl;
  // must prewrite to apply type ascriptions since rewriting does not preserve
  // types
  if (in.getKind() == kind::APPLY_CONSTRUCTOR)
  {
    TypeNode tn = in.getType();

    // check for parametric datatype constructors
    // to ensure a normal form, all parameteric datatype constructors must have
    // a type ascription
    if (tn.isParametricDatatype())
    {
      if (in.getOperator().getKind() != kind::APPLY_TYPE_ASCRIPTION)
      {
        Trace("datatypes-rewrite-debug")
            << "Ascribing type to parametric datatype constructor " << in
            << std::endl;
        Node op = in.getOperator();
        // get the constructor object
        const DTypeConstructor& dtc = utils::datatypeOf(op)[utils::indexOf(op)];
        // create ascribed constructor type
        Node op_new = dtc.getInstantiatedConstructor(tn);
        // make new node
        std::vector<Node> children;
        children.push_back(op_new);
        children.insert(children.end(), in.begin(), in.end());
        Node inr =
            NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, children);
        Trace("datatypes-rewrite-debug") << "Created " << inr << std::endl;
        return RewriteResponse(REWRITE_DONE, inr);
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteConstructor(TNode in)
{
  if (in.isConst())
  {
    Trace("datatypes-rewrite-debug") << "Normalizing constant " << in
                                     << std::endl;
    Node inn = normalizeConstant(in);
    // constant may be a subterm of another constant, so cannot assume that this
    // will succeed for codatatypes
    // Assert( !inn.isNull() );
    if (!inn.isNull() && inn != in)
    {
      Trace("datatypes-rewrite") << "Normalized constant " << in << " -> "
                                 << inn << std::endl;
      return RewriteResponse(REWRITE_DONE, inn);
    }
    return RewriteResponse(REWRITE_DONE, in);
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteSelector(TNode in)
{
  Assert (in.getKind()==kind::APPLY_SELECTOR);
  if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
  {
    // Have to be careful not to rewrite well-typed expressions
    // where the selector doesn't match the constructor,
    // e.g. "pred(zero)".
    TypeNode tn = in.getType();
    TypeNode argType = in[0].getType();
    Node selector = in.getOperator();
    TNode constructor = in[0].getOperator();
    size_t constructorIndex = utils::indexOf(constructor);
    const DType& dt = utils::datatypeOf(selector);
    const DTypeConstructor& c = dt[constructorIndex];
    Trace("datatypes-rewrite-debug") << "Rewriting collapsable selector : "
                                     << in;
    Trace("datatypes-rewrite-debug") << ", cindex = " << constructorIndex
                                     << ", selector is " << selector
                                     << std::endl;
    // The argument that the selector extracts, or -1 if the selector is
    // is wrongly applied.
    // The argument index of internal selectors is obtained by
    // getSelectorIndexInternal.
    int selectorIndex = c.getSelectorIndexInternal(selector);
    Trace("datatypes-rewrite-debug") << "Internal selector index is "
                                     << selectorIndex << std::endl;
    if (selectorIndex >= 0)
    {
      Assert(selectorIndex < (int)c.getNumArgs());
      if (dt.isCodatatype() && in[0][selectorIndex].isConst())
      {
        // must replace all debruijn indices with self
        Node sub = replaceDebruijn(in[0][selectorIndex], in[0], argType, 0);
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial codatatype selector "
                                   << in << " to " << sub << std::endl;
        if (sub != in)
        {
          return RewriteResponse(REWRITE_AGAIN_FULL, sub);
        }
      }
      else
      {
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << std::endl;
        return RewriteResponse(REWRITE_DONE, in[0][selectorIndex]);
      }
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteTester(TNode in)
{
  if (in[0].getKind() == kind::APPLY_CONSTRUCTOR)
  {
    bool result =
        utils::indexOf(in.getOperator()) == utils::indexOf(in[0].getOperator());
    Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                               << "Rewrite trivial tester " << in << " "
                               << result << std::endl;
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(result));
  }
  const DType& dt = in[0].getType().getDType();
  if (dt.getNumConstructors() == 1 && !dt.isSygus())
  {
    // only one constructor, so it must be
    Trace("datatypes-rewrite")
        << "DatatypesRewriter::postRewrite: "
        << "only one ctor for " << dt.getName() << " and that is "
        << dt[0].getName() << std::endl;
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(true));
  }
  // could try dt.getNumConstructors()==2 && indexOf(in.getOperator())==1 ?
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse DatatypesRewriter::rewriteUpdater(TNode in)
{
  Assert (in.getKind()==APPLY_UPDATER);
  if (in[0].getKind() == APPLY_CONSTRUCTOR)
  {
    Node op = in.getOperator();
    size_t cindex = utils::indexOf(in[0].getOperator());
    size_t cuindex = utils::cindexOf(op);
    if (cindex==cuindex)
    {
      NodeManager * nm = NodeManager::currentNM();
      size_t updateIndex = utils::indexOf(op);
      std::vector<Node> children(in[0].begin(), in[0].end());
      children[updateIndex] = in[1];
      children.insert(children.begin(),in[0].getOperator());
      return RewriteResponse(REWRITE_DONE, nm->mkNode(APPLY_CONSTRUCTOR, children));
    }
    return RewriteResponse(REWRITE_DONE, in[0]);
  }
  return RewriteResponse(REWRITE_DONE, in);
}

Node DatatypesRewriter::normalizeCodatatypeConstant(Node n)
{
  Trace("dt-nconst") << "Normalize " << n << std::endl;
  std::map<Node, Node> rf;
  std::vector<Node> sk;
  std::vector<Node> rf_pending;
  std::vector<Node> terms;
  std::map<Node, bool> cdts;
  Node s = collectRef(n, sk, rf, rf_pending, terms, cdts);
  if (!s.isNull())
  {
    Trace("dt-nconst") << "...symbolic normalized is : " << s << std::endl;
    for (std::map<Node, Node>::iterator it = rf.begin(); it != rf.end(); ++it)
    {
      Trace("dt-nconst") << "  " << it->first << " = " << it->second
                         << std::endl;
    }
    // now run DFA minimization on term structure
    Trace("dt-nconst") << "  " << terms.size()
                       << " total subterms :" << std::endl;
    int eqc_count = 0;
    std::map<Node, int> eqc_op_map;
    std::map<Node, int> eqc;
    std::map<int, std::vector<Node> > eqc_nodes;
    // partition based on top symbol
    for (unsigned j = 0, size = terms.size(); j < size; j++)
    {
      Node t = terms[j];
      Trace("dt-nconst") << "    " << t << ", cdt=" << cdts[t] << std::endl;
      int e;
      if (cdts[t])
      {
        Assert(t.getKind() == kind::APPLY_CONSTRUCTOR);
        Node op = t.getOperator();
        std::map<Node, int>::iterator it = eqc_op_map.find(op);
        if (it == eqc_op_map.end())
        {
          e = eqc_count;
          eqc_op_map[op] = eqc_count;
          eqc_count++;
        }
        else
        {
          e = it->second;
        }
      }
      else
      {
        e = eqc_count;
        eqc_count++;
      }
      eqc[t] = e;
      eqc_nodes[e].push_back(t);
    }
    // partition until fixed point
    int eqc_curr = 0;
    bool success = true;
    while (success)
    {
      success = false;
      int eqc_end = eqc_count;
      while (eqc_curr < eqc_end)
      {
        if (eqc_nodes[eqc_curr].size() > 1)
        {
          // look at all nodes in this equivalence class
          unsigned nchildren = eqc_nodes[eqc_curr][0].getNumChildren();
          std::map<int, std::vector<Node> > prt;
          for (unsigned j = 0; j < nchildren; j++)
          {
            prt.clear();
            // partition based on children : for the first child that causes a
            // split, break
            for (unsigned k = 0, size = eqc_nodes[eqc_curr].size(); k < size;
                 k++)
            {
              Node t = eqc_nodes[eqc_curr][k];
              Assert(t.getNumChildren() == nchildren);
              Node tc = t[j];
              // refer to loops
              std::map<Node, Node>::iterator itr = rf.find(tc);
              if (itr != rf.end())
              {
                tc = itr->second;
              }
              Assert(eqc.find(tc) != eqc.end());
              prt[eqc[tc]].push_back(t);
            }
            if (prt.size() > 1)
            {
              success = true;
              break;
            }
          }
          // move into new eqc(s)
          for (const std::pair<const int, std::vector<Node> >& p : prt)
          {
            int e = eqc_count;
            for (unsigned j = 0, size = p.second.size(); j < size; j++)
            {
              Node t = p.second[j];
              eqc[t] = e;
              eqc_nodes[e].push_back(t);
            }
            eqc_count++;
          }
        }
        eqc_nodes.erase(eqc_curr);
        eqc_curr++;
      }
    }
    // add in already occurring loop variables
    for (std::map<Node, Node>::iterator it = rf.begin(); it != rf.end(); ++it)
    {
      Trace("dt-nconst-debug") << "Mapping equivalence class of " << it->first
                               << " -> " << it->second << std::endl;
      Assert(eqc.find(it->second) != eqc.end());
      eqc[it->first] = eqc[it->second];
    }
    // we now have a partition of equivalent terms
    Trace("dt-nconst") << "Computed equivalence classes ids : " << std::endl;
    for (std::map<Node, int>::iterator it = eqc.begin(); it != eqc.end(); ++it)
    {
      Trace("dt-nconst") << "  " << it->first << " -> " << it->second
                         << std::endl;
    }
    // traverse top-down based on equivalence class
    std::map<int, int> eqc_stack;
    return normalizeCodatatypeConstantEqc(s, eqc_stack, eqc, 0);
  }
  Trace("dt-nconst") << "...invalid." << std::endl;
  return Node::null();
}

// normalize constant : apply to top-level codatatype constants
Node DatatypesRewriter::normalizeConstant(Node n)
{
  TypeNode tn = n.getType();
  if (tn.isDatatype())
  {
    if (tn.isCodatatype())
    {
      return normalizeCodatatypeConstant(n);
    }
    else
    {
      std::vector<Node> children;
      bool childrenChanged = false;
      for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
      {
        Node nc = normalizeConstant(n[i]);
        children.push_back(nc);
        childrenChanged = childrenChanged || nc != n[i];
      }
      if (childrenChanged)
      {
        return NodeManager::currentNM()->mkNode(n.getKind(), children);
      }
    }
  }
  return n;
}

Node DatatypesRewriter::collectRef(Node n,
                                   std::vector<Node>& sk,
                                   std::map<Node, Node>& rf,
                                   std::vector<Node>& rf_pending,
                                   std::vector<Node>& terms,
                                   std::map<Node, bool>& cdts)
{
  Assert(n.isConst());
  TypeNode tn = n.getType();
  Node ret = n;
  bool isCdt = false;
  if (tn.isDatatype())
  {
    if (!tn.isCodatatype())
    {
      // nested datatype within codatatype : can be normalized independently
      // since all loops should be self-contained
      ret = normalizeConstant(n);
    }
    else
    {
      isCdt = true;
      if (n.getKind() == kind::APPLY_CONSTRUCTOR)
      {
        sk.push_back(n);
        rf_pending.push_back(Node::null());
        std::vector<Node> children;
        children.push_back(n.getOperator());
        bool childChanged = false;
        for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
        {
          Node nc = collectRef(n[i], sk, rf, rf_pending, terms, cdts);
          if (nc.isNull())
          {
            return Node::null();
          }
          childChanged = nc != n[i] || childChanged;
          children.push_back(nc);
        }
        sk.pop_back();
        if (childChanged)
        {
          ret = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR,
                                                 children);
          if (!rf_pending.back().isNull())
          {
            rf[rf_pending.back()] = ret;
          }
        }
        else
        {
          Assert(rf_pending.back().isNull());
        }
        rf_pending.pop_back();
      }
      else
      {
        // a loop
        const Integer& i = n.getConst<CodatatypeBoundVariable>().getIndex();
        uint32_t index = i.toUnsignedInt();
        if (index >= sk.size())
        {
          return Node::null();
        }
        Assert(sk.size() == rf_pending.size());
        Node r = rf_pending[rf_pending.size() - 1 - index];
        if (r.isNull())
        {
          r = NodeManager::currentNM()->mkBoundVar(
              sk[rf_pending.size() - 1 - index].getType());
          rf_pending[rf_pending.size() - 1 - index] = r;
        }
        return r;
      }
    }
  }
  Trace("dt-nconst-debug") << "Return term : " << ret << " from " << n
                           << std::endl;
  if (std::find(terms.begin(), terms.end(), ret) == terms.end())
  {
    terms.push_back(ret);
    Assert(ret.getType() == tn);
    cdts[ret] = isCdt;
  }
  return ret;
}
// eqc_stack stores depth
Node DatatypesRewriter::normalizeCodatatypeConstantEqc(
    Node n, std::map<int, int>& eqc_stack, std::map<Node, int>& eqc, int depth)
{
  Trace("dt-nconst-debug") << "normalizeCodatatypeConstantEqc: " << n
                           << " depth=" << depth << std::endl;
  if (eqc.find(n) != eqc.end())
  {
    int e = eqc[n];
    std::map<int, int>::iterator it = eqc_stack.find(e);
    if (it != eqc_stack.end())
    {
      int debruijn = depth - it->second - 1;
      return NodeManager::currentNM()->mkConst(
          CodatatypeBoundVariable(n.getType(), debruijn));
    }
    std::vector<Node> children;
    bool childChanged = false;
    eqc_stack[e] = depth;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      Node nc = normalizeCodatatypeConstantEqc(n[i], eqc_stack, eqc, depth + 1);
      children.push_back(nc);
      childChanged = childChanged || nc != n[i];
    }
    eqc_stack.erase(e);
    if (childChanged)
    {
      Assert(n.getKind() == kind::APPLY_CONSTRUCTOR);
      children.insert(children.begin(), n.getOperator());
      return NodeManager::currentNM()->mkNode(n.getKind(), children);
    }
  }
  return n;
}

Node DatatypesRewriter::replaceDebruijn(Node n,
                                        Node orig,
                                        TypeNode orig_tn,
                                        unsigned depth)
{
  if (n.getKind() == kind::CODATATYPE_BOUND_VARIABLE && n.getType() == orig_tn)
  {
    unsigned index =
        n.getConst<CodatatypeBoundVariable>().getIndex().toUnsignedInt();
    if (index == depth)
    {
      return orig;
    }
  }
  else if (n.getNumChildren() > 0)
  {
    std::vector<Node> children;
    bool childChanged = false;
    for (unsigned i = 0, size = n.getNumChildren(); i < size; i++)
    {
      Node nc = replaceDebruijn(n[i], orig, orig_tn, depth + 1);
      children.push_back(nc);
      childChanged = childChanged || nc != n[i];
    }
    if (childChanged)
    {
      if (n.hasOperator())
      {
        children.insert(children.begin(), n.getOperator());
      }
      return NodeManager::currentNM()->mkNode(n.getKind(), children);
    }
  }
  return n;
}

Node DatatypesRewriter::expandApplySelector(Node n, bool sharedSel)
{
  Assert(n.getKind() == APPLY_SELECTOR);
  Node selector = n.getOperator();
  if (!sharedSel || !selector.hasAttribute(DTypeConsIndexAttr()))
  {
    return n;
  }
  // APPLY_SELECTOR always applies to an external selector, cindexOf is
  // legal here
  size_t cindex = utils::cindexOf(selector);
  const DType& dt = utils::datatypeOf(selector);
  const DTypeConstructor& c = dt[cindex];
  TypeNode ndt = n[0].getType();
  size_t selectorIndex = utils::indexOf(selector);
  Trace("dt-expand") << "...selector index = " << selectorIndex << std::endl;
  Assert(selectorIndex < c.getNumArgs());
  return utils::applySelector(c, selectorIndex, true, n[0]);
}

TrustNode DatatypesRewriter::expandDefinition(Node n)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode tn = n.getType();
  Node ret;
  switch (n.getKind())
  {
    case kind::APPLY_SELECTOR:
    {
      ret = expandApplySelector(n, d_opts.datatypes.dtSharedSelectors);
    }
    break;
    case APPLY_UPDATER:
    {
      Assert(tn.isDatatype());
      const DType& dt = tn.getDType();
      Node op = n.getOperator();
      size_t updateIndex = utils::indexOf(op);
      size_t cindex = utils::cindexOf(op);
      const DTypeConstructor& dc = dt[cindex];
      NodeBuilder b(APPLY_CONSTRUCTOR);
      if (tn.isParametricDatatype())
      {
        b << dc.getInstantiatedConstructor(n[0].getType());
      }
      else
      {
        b << dc.getConstructor();
      }
      Trace("dt-expand") << "Expand updater " << n << std::endl;
      Trace("dt-expand") << "expr is " << n << std::endl;
      Trace("dt-expand") << "updateIndex is " << updateIndex << std::endl;
      Trace("dt-expand") << "t is " << tn << std::endl;
      bool shareSel = d_opts.datatypes.dtSharedSelectors;
      for (size_t i = 0, size = dc.getNumArgs(); i < size; ++i)
      {
        if (i == updateIndex)
        {
          b << n[1];
        }
        else
        {
          b << utils::applySelector(dc, i, shareSel, n[0]);
        }
      }
      ret = b;
      if (dt.getNumConstructors() > 1)
      {
        // must be the right constructor to update
        Node tester = nm->mkNode(APPLY_TESTER, dc.getTester(), n[0]);
        ret = nm->mkNode(ITE, tester, ret, n[0]);
      }
      Trace("dt-expand") << "return " << ret << std::endl;
    }
    break;
    default: break;
  }
  if (!ret.isNull() && n != ret)
  {
    return TrustNode::mkTrustRewrite(n, ret, nullptr);
  }
  return TrustNode::null();
}

Node DatatypesRewriter::sygusToBuiltinEval(Node n,
                                           const std::vector<Node>& args)
{
  Assert(d_sygusEval != nullptr);
  Assert (n.getType().isDatatype());
  Assert (n.getType().getDType().isSygus());
  Assert (n.getType().getDType().getSygusVarList().getNumChildren()==args.size());
  NodeManager* nm = NodeManager::currentNM();
  // constant arguments?
  bool constArgs = true;
  for (const Node& a : args)
  {
    if (!a.isConst())
    {
      constArgs = false;
      break;
    }
  }
  std::vector<Node> eargs;
  bool svarsInit = false;
  std::vector<Node> svars;
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  unsigned index;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      TypeNode tn = cur.getType();
      if (!tn.isDatatype() || !tn.getDType().isSygus())
      {
        visited[cur] = cur;
      }
      else if (cur.isConst())
      {
        // convert to builtin term
        Node bt = utils::sygusToBuiltin(cur);
        // run the evaluator if possible
        if (!svarsInit)
        {
          svarsInit = true;
          TypeNode type = cur.getType();
          Node varList = type.getDType().getSygusVarList();
          for (const Node& v : varList)
          {
            svars.push_back(v);
          }
        }
        Assert(args.size() == svars.size());
        // try evaluation if we have constant arguments
        Node ret =
            constArgs ? d_sygusEval->eval(bt, svars, args) : Node::null();
        if (ret.isNull())
        {
          // if evaluation was not available, use a substitution
          ret = bt.substitute(
              svars.begin(), svars.end(), args.begin(), args.end());
        }
        visited[cur] = ret;
      }
      else
      {
        if (cur.getKind() == APPLY_CONSTRUCTOR)
        {
          visited[cur] = Node::null();
          visit.push_back(cur);
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
        else
        {
          // it is the evaluation of this term on the arguments
          if (eargs.empty())
          {
            eargs.push_back(cur);
            eargs.insert(eargs.end(), args.begin(), args.end());
          }
          else
          {
            eargs[0] = cur;
          }
          visited[cur] = nm->mkNode(DT_SYGUS_EVAL, eargs);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      Assert(cur.getKind() == APPLY_CONSTRUCTOR);
      const DType& dt = cur.getType().getDType();
      // non sygus-datatype terms are also themselves
      if (dt.isSygus())
      {
        std::vector<Node> children;
        for (const Node& cn : cur)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          children.push_back(it->second);
        }
        index = utils::indexOf(cur.getOperator());
        // apply to children, which constructs the builtin term
        ret = utils::mkSygusTerm(dt, index, children);
        // now apply it to arguments in args
        ret = utils::applySygusArgs(dt, dt[index].getSygusOp(), ret, args);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

}  // namespace datatypes
}  // namespace theory
}  // namespace cvc5::internal
