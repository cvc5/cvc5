/*********************                                                        */
/*! \file datatypes_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of rewriter for the theory of (co)inductive datatypes.
 **
 ** Implementation of rewriter for the theory of (co)inductive datatypes.
 **/

#include "theory/datatypes/datatypes_rewriter.h"

#include "expr/dtype.h"
#include "expr/node_algorithm.h"
#include "expr/sygus_datatype.h"
#include "options/datatypes_options.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/datatypes/theory_datatypes_utils.h"

using namespace CVC4;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace datatypes {

RewriteResponse DatatypesRewriter::postRewrite(TNode in)
{
  Trace("datatypes-rewrite-debug") << "post-rewriting " << in << std::endl;
  Kind kind = in.getKind();
  NodeManager* nm = NodeManager::currentNM();
  if (kind == kind::APPLY_CONSTRUCTOR)
  {
    return rewriteConstructor(in);
  }
  else if (kind == kind::APPLY_SELECTOR_TOTAL || kind == kind::APPLY_SELECTOR)
  {
    return rewriteSelector(in);
  }
  else if (kind == kind::APPLY_TESTER)
  {
    return rewriteTester(in);
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
      children.push_back(nm->mkConst(Rational(weight)));
      Node res =
          children.size() == 1 ? children[0] : nm->mkNode(kind::PLUS, children);
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
              nm->mkNode(kind::DT_HEIGHT_BOUND, in[0][i], nm->mkConst(rmo)));
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
      Node ret = utils::sygusToBuiltinEval(ev, args);
      Trace("dt-sygus-util") << "...got " << ret << "\n";
      Trace("dt-sygus-util") << "Type is " << ret.getType() << std::endl;
      Assert(in.getType().isComparableTo(ret.getType()));
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }
  else if (kind == MATCH)
  {
    Trace("dt-rewrite-match") << "Rewrite match: " << in << std::endl;
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
        AlwaysAssert(false);
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
            Node sc = nm->mkNode(
                APPLY_SELECTOR_TOTAL, dt[cindex].getSelectorInternal(t, i), h);
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
    AlwaysAssert(cases[0].isConst() || cases.size() == dt.getNumConstructors());
    for (unsigned i = 1, ncases = cases.size(); i < ncases; i++)
    {
      ret = nm->mkNode(ITE, cases[i], rets[i], ret);
    }
    Trace("dt-rewrite-match")
        << "Rewrite match: " << in << " ... " << ret << std::endl;
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
        Node tc = NodeManager::currentNM()->mkConst(
            AscriptionType(dtc.getSpecializedConstructorType(tn).toType()));
        Node op_new = NodeManager::currentNM()->mkNode(
            kind::APPLY_TYPE_ASCRIPTION, tc, op);
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
  Kind k = in.getKind();
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
    int selectorIndex = -1;
    if (k == kind::APPLY_SELECTOR_TOTAL)
    {
      // The argument index of internal selectors is obtained by
      // getSelectorIndexInternal.
      selectorIndex = c.getSelectorIndexInternal(selector);
    }
    else
    {
      // The argument index of external selectors (applications of
      // APPLY_SELECTOR) is given by an attribute and obtained via indexOf below
      // The argument is only valid if it is the proper constructor.
      selectorIndex = utils::indexOf(selector);
      if (selectorIndex < 0
          || selectorIndex >= static_cast<int>(c.getNumArgs()))
      {
        selectorIndex = -1;
      }
      else if (c[selectorIndex].getSelector() != selector)
      {
        selectorIndex = -1;
      }
    }
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
    else if (k == kind::APPLY_SELECTOR_TOTAL)
    {
      Node gt;
      bool useTe = true;
      // if( !tn.isSort() ){
      //  useTe = false;
      //}
      if (tn.isDatatype())
      {
        const DType& dta = tn.getDType();
        useTe = !dta.isCodatatype();
      }
      if (useTe)
      {
        TypeEnumerator te(tn);
        gt = *te;
      }
      else
      {
        gt = tn.mkGroundTerm();
      }
      if (!gt.isNull())
      {
        // Assert( gtt.isDatatype() || gtt.isParametricDatatype() );
        if (tn.isDatatype() && !tn.isInstantiatedDatatype())
        {
          gt = NodeManager::currentNM()->mkNode(
              kind::APPLY_TYPE_ASCRIPTION,
              NodeManager::currentNM()->mkConst(AscriptionType(tn.toType())),
              gt);
        }
        Trace("datatypes-rewrite") << "DatatypesRewriter::postRewrite: "
                                   << "Rewrite trivial selector " << in
                                   << " to distinguished ground term " << gt
                                   << std::endl;
        return RewriteResponse(REWRITE_DONE, gt);
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
        const Integer& i = n.getConst<UninterpretedConstant>().getIndex();
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
          UninterpretedConstant(n.getType(), debruijn));
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
  if (n.getKind() == kind::UNINTERPRETED_CONSTANT && n.getType() == orig_tn)
  {
    unsigned index =
        n.getConst<UninterpretedConstant>().getIndex().toUnsignedInt();
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

} /* CVC4::theory::datatypes namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
