/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/booleans/theory_bool_rewriter.h"

#include <algorithm>
#include <unordered_set>

#include "expr/algorithm/flatten.h"
#include "expr/node_value.h"
#include "proof/conv_proof_generator.h"
#include "util/cardinality.h"

namespace cvc5::internal {
namespace theory {
namespace booleans {

TheoryBoolRewriter::TheoryBoolRewriter(NodeManager* nm) : TheoryRewriter(nm)
{
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
  registerProofRewriteRule(ProofRewriteRule::MACRO_BOOL_NNF_NORM,
                           TheoryRewriteCtx::POST_DSL);
}

Node TheoryBoolRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::MACRO_BOOL_NNF_NORM:
    {
      Node nn = computeNnfNorm(nodeManager(), n);
      if (nn != n)
      {
        return nn;
      }
    }
    break;
    default: break;
  }
  return Node::null();
}

bool TheoryBoolRewriter::addNnfNormChild(std::vector<Node>& children,
                                         Node c,
                                         Kind k,
                                         std::map<Node, bool>& lit_pol,
                                         bool& childrenChanged)
{
  if (k == Kind::OR || k == Kind::AND)
  {
    Node lit = c.getKind() == Kind::NOT ? c[0] : c;
    bool pol = c.getKind() != Kind::NOT;
    std::map<Node, bool>::iterator it = lit_pol.find(lit);
    if (it == lit_pol.end())
    {
      lit_pol[lit] = pol;
      children.push_back(c);
    }
    else
    {
      childrenChanged = true;
      if (it->second != pol)
      {
        return false;
      }
    }
  }
  else
  {
    children.push_back(c);
  }
  return true;
}

Node TheoryBoolRewriter::computeNnfNorm(NodeManager* nm,
                                        const Node& n,
                                        TConvProofGenerator* pg)
{
  Trace("compute-nnf") << "Compute NNF norm " << n << std::endl;
  // at pre-order traversal, we store preKind and preChildren, which
  // determine the Kind and the children for the node to reconstruct.
  std::unordered_map<TNode, Kind> preKind;
  std::unordered_map<TNode, std::vector<Node>> preChildren;
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
      Kind k = cur.getKind();
      bool negAllCh = false;
      bool negCh1 = false;
      // the new formula we should traverse
      TNode ncur = cur;
      // the result of rewriting cur after pre-rewrite
      Node preCur;
      if (k == Kind::IMPLIES)
      {
        k = Kind::OR;
        negCh1 = true;
      }
      else if (k == Kind::XOR)
      {
        k = Kind::EQUAL;
        negCh1 = true;
      }
      else if (k == Kind::NOT)
      {
        if (cur[0].getKind() == Kind::NOT)
        {
          // double negation cancels
          preCur = cur[0][0];
          visited[cur] = preCur;
        }
        else if (cur[0].getKind() == Kind::OR
                 || cur[0].getKind() == Kind::IMPLIES)
        {
          k = Kind::AND;
          negAllCh = true;
          negCh1 = cur[0].getKind() == Kind::IMPLIES;
        }
        else if (cur[0].getKind() == Kind::AND)
        {
          k = Kind::OR;
          negAllCh = true;
        }
        else if (cur[0].getKind() == Kind::XOR
                 || (cur[0].getKind() == Kind::EQUAL
                     && cur[0][0].getType().isBoolean()))
        {
          k = Kind::EQUAL;
          negCh1 = cur[0].getKind() == Kind::EQUAL;
        }
        else if (cur[0].getKind() == Kind::ITE)
        {
          k = cur[0].getKind();
          negAllCh = true;
          negCh1 = true;
        }
        else
        {
          visited[cur] = cur;
          continue;
        }
        ncur = cur[0];
      }
      else if ((k != Kind::EQUAL || !cur[0].getType().isBoolean())
               && k != Kind::ITE && k != Kind::AND && k != Kind::OR)
      {
        // a literal
        visited[cur] = cur;
        continue;
      }
      if (preCur.isNull())
      {
        preKind[cur] = k;
        visited[cur] = Node::null();
        visit.push_back(cur);
        std::vector<Node>& pc = preChildren[cur];
        for (size_t i = 0, nchild = ncur.getNumChildren(); i < nchild; ++i)
        {
          Node c =
              (i == 0 && negCh1) != negAllCh ? ncur[i].negate() : Node(ncur[i]);
          pc.push_back(c);
          visit.push_back(c);
        }
        if (pg != nullptr)
        {
          preCur = nm->mkNode(k, pc);
        }
      }
      // if proof producing, possibly add a pre-rewrite step
      if (pg != nullptr)
      {
        if (preCur != cur)
        {
          pg->addRewriteStep(
              cur, preCur, nullptr, true, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
        }
      }
    }
    else if (it->second.isNull())
    {
      Kind ok = cur.getKind();
      Assert(preKind.find(cur) != preKind.end());
      Kind k = preKind[cur];
      Assert(cur.getMetaKind() != kind::metakind::PARAMETERIZED);
      bool childChanged = false;
      std::vector<Node> children;
      std::vector<Node>& pc = preChildren[cur];
      std::map<Node, bool> lit_pol;
      bool success = true;
      for (const Node& cn : pc)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        Node c = it->second;
        if (c.getKind() == k && (k == Kind::OR || k == Kind::AND))
        {
          // flatten
          childChanged = true;
          for (const Node& cc : c)
          {
            if (!addNnfNormChild(children, cc, k, lit_pol, childChanged))
            {
              success = false;
              break;
            }
          }
        }
        else
        {
          success = addNnfNormChild(children, c, k, lit_pol, childChanged);
        }
        if (!success)
        {
          // tautology
          break;
        }
        childChanged = childChanged || c != cn;
      }
      Node ret = cur;
      if (!success)
      {
        Assert(k == Kind::OR || k == Kind::AND);
        ret = nm->mkConst(k == Kind::OR);
      }
      else if (childChanged || k != ok)
      {
        ret = (children.size() == 1 && k != Kind::NOT)
                  ? children[0]
                  : nm->mkNode(k, children);
      }
      // if proof producing, possibly add a post-rewrite step
      if (pg != nullptr)
      {
        std::vector<Node> pcc;
        for (const Node& cn : pc)
        {
          it = visited.find(cn);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          pcc.push_back(it->second);
        }
        Node pcpc = nm->mkNode(k, pcc);
        if (pcpc != ret)
        {
          pg->addRewriteStep(
              pcpc, ret, nullptr, false, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
        }
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

RewriteResponse TheoryBoolRewriter::postRewrite(TNode node) {
  return preRewrite(node);
}

/**
 * flattenNode looks for children of same kind, and if found merges
 * them into the parent.
 *
 * It simultaneously handles a couple of other optimizations:
 * - trivialNode - if found during exploration, return that node itself
 *    (like in case of OR, if "true" is found, makes sense to replace
 *     whole formula with "true")
 * - skipNode - as name suggests, skip them
 *    (like in case of OR, you may want to skip any "false" nodes found)
 *
 * Use a null node if you want to ignore any of the optimizations.
 */
RewriteResponse TheoryBoolRewriter::flattenNode(TNode n,
                                                TNode trivialNode,
                                                TNode skipNode)
{
  typedef std::unordered_set<TNode> node_set;

  node_set visited;
  visited.insert(skipNode);

  std::vector<TNode> toProcess;
  toProcess.push_back(n);

  Kind k = n.getKind();
  typedef std::vector<TNode> ChildList;
  ChildList childList;   //TNode should be fine, since 'n' is still there

  for (unsigned i = 0; i < toProcess.size(); ++ i) {
    TNode current = toProcess[i];
    for(unsigned j = 0, j_end = current.getNumChildren(); j < j_end; ++ j) {
      TNode child = current[j];
      if(visited.find(child) != visited.end()) {
        continue;
      } else if(child == trivialNode) {
        return RewriteResponse(REWRITE_DONE, trivialNode);
      } else {
        visited.insert(child);
        if(child.getKind() == k)
          toProcess.push_back(child);
        else
          childList.push_back(child);
      }
    }
  }
  if (childList.size() == 0) return RewriteResponse(REWRITE_DONE, skipNode);
  if (childList.size() == 1) return RewriteResponse(REWRITE_AGAIN, childList[0]);

  /* Trickery to stay under number of children possible in a node */
  NodeManager* nm = nodeManager();
  if (childList.size() < expr::NodeValue::MAX_CHILDREN)
  {
    Node retNode = nm->mkNode(k, childList);
    return RewriteResponse(REWRITE_DONE, retNode);
  }
  else
  {
    Assert(childList.size()
           < static_cast<size_t>(expr::NodeValue::MAX_CHILDREN)
                 * static_cast<size_t>(expr::NodeValue::MAX_CHILDREN));
    NodeBuilder nb(nodeManager(), k);
    ChildList::iterator cur = childList.begin(), next, en = childList.end();
    while (cur != en)
    {
      next = min(cur + expr::NodeValue::MAX_CHILDREN, en);
      nb << (nm->mkNode(k, ChildList(cur, next)));
      cur = next;
    }
    return RewriteResponse(REWRITE_DONE, nb.constructNode());
  }
}

// Equality parity returns
// * 0 if no relation between a and b is found
// * 1 if a == b
// * 2 if a == not(b)
// * 3 or b == not(a)
inline int equalityParity(TNode a, TNode b){
  if(a == b){
    return 1;
  }
  else if (a.getKind() == Kind::NOT && a[0] == b)
  {
    return 2;
  }
  else if (b.getKind() == Kind::NOT && b[0] == a)
  {
    return 3;
  }
  else
  {
    return 0;
  }
}

Node TheoryBoolRewriter::makeNegation(TNode n)
{
  bool even = false;
  while (n.getKind() == Kind::NOT)
  {
    n = n[0];
    even = !even;
  }
  if(even){
    return n;
  } else {
    if(n.isConst()){
      return nodeManager()->mkConst(!n.getConst<bool>());
    }else{
      return n.notNode();
    }
  }
}

RewriteResponse TheoryBoolRewriter::preRewrite(TNode n) {
  NodeManager* nm = nodeManager();

  switch(n.getKind()) {
    case Kind::NOT:
    {
      if (n[0] == d_true) return RewriteResponse(REWRITE_DONE, d_false);
      if (n[0] == d_false) return RewriteResponse(REWRITE_DONE, d_true);
      if (n[0].getKind() == Kind::NOT)
        return RewriteResponse(REWRITE_AGAIN, n[0][0]);
      break;
    }
    case Kind::OR:
    {
      bool done = true;
      TNode::iterator i = n.begin(), iend = n.end();
      for (; i != iend; ++i)
      {
        if (*i == d_true) return RewriteResponse(REWRITE_DONE, d_true);
        if (*i == d_false) done = false;
        if ((*i).getKind() == Kind::OR) done = false;
      }
      if (!done)
      {
        return flattenNode(
            n, /* trivialNode = */ d_true, /* skipNode = */ d_false);
      }
      // x v ... v x --> x
      unsigned ind, size;
      for (ind = 0, size = n.getNumChildren(); ind < size - 1; ++ind)
      {
        if (n[ind] != n[ind + 1])
        {
          break;
        }
      }
      if (ind == size - 1)
      {
        return RewriteResponse(REWRITE_AGAIN, n[0]);
      }
      break;
    }
    case Kind::AND:
    {
      bool done = true;
      TNode::iterator i = n.begin(), iend = n.end();
      for (; i != iend; ++i)
      {
        if (*i == d_false) return RewriteResponse(REWRITE_DONE, d_false);
        if (*i == d_true) done = false;
        if ((*i).getKind() == Kind::AND) done = false;
      }
      if (!done)
      {
        RewriteResponse ret = flattenNode(
            n, /* trivialNode = */ d_false, /* skipNode = */ d_true);
        Trace("bool-flad_trueen") << n << ": " << ret.d_node << std::endl;
        return ret;
      }
      // x ^ ... ^ x --> x
      unsigned ind, size;
      for (ind = 0, size = n.getNumChildren(); ind < size - 1; ++ind)
      {
        if (n[ind] != n[ind + 1])
        {
          break;
        }
      }
      if (ind == size - 1)
      {
        return RewriteResponse(REWRITE_AGAIN, n[0]);
      }
      break;
    }
    case Kind::IMPLIES:
    {
      if (n[0] == d_false || n[1] == d_true)
        return RewriteResponse(REWRITE_DONE, d_true);
      if (n[0] == d_true && n[1] == d_false)
        return RewriteResponse(REWRITE_DONE, d_false);
      if (n[0] == d_true) return RewriteResponse(REWRITE_AGAIN, n[1]);
      if (n[1] == d_false)
        return RewriteResponse(REWRITE_AGAIN, makeNegation(n[0]));
      break;
    }
    case Kind::EQUAL:
    {
      // rewrite simple cases of IFF
      if (n[0] == d_true)
      {
        // IFF true x
        return RewriteResponse(REWRITE_AGAIN, n[1]);
      }
      else if (n[1] == d_true)
      {
        // IFF x true
        return RewriteResponse(REWRITE_AGAIN, n[0]);
      }
      else if (n[0] == d_false)
      {
        // IFF false x
        return RewriteResponse(REWRITE_AGAIN, makeNegation(n[1]));
      }
      else if (n[1] == d_false)
      {
        // IFF x false
        return RewriteResponse(REWRITE_AGAIN, makeNegation(n[0]));
      }
      else if (n[0] == n[1])
      {
        // IFF x x
        return RewriteResponse(REWRITE_DONE, d_true);
      }
      else if (n[0].getKind() == Kind::NOT && n[0][0] == n[1])
      {
        // IFF (NOT x) x
        return RewriteResponse(REWRITE_DONE, d_false);
      }
      else if (n[1].getKind() == Kind::NOT && n[1][0] == n[0])
      {
        // IFF x (NOT x)
        return RewriteResponse(REWRITE_DONE, d_false);
      }
      else if (n[0].getKind() == Kind::EQUAL && n[1].getKind() == Kind::EQUAL)
      {
        // a : (= i x)
        // i : (= j k)
        // x : (= y z)

        // assume wlog k, z are constants and j is the same symbol as y
        // (= (= j k) (= j z))
        // if k = z
        //  then (= (= j k) (= j k)) => true
        // else
        //  (= (= j k) (= j z)) <=> b
        //  b : (and (not (= j k)) (not (= j z)))
        //  (= j k) (= j z) | a b
        //  f       f       | t t
        //  f       t       | f f
        //  t       f       | f f
        //  t       t       | * f
        // * j cannot equal both k and z in a theory model
        TNode t, c;
        if (n[0][0].isConst())
        {
          c = n[0][0];
          t = n[0][1];
        }
        else if (n[0][1].isConst())
        {
          c = n[0][1];
          t = n[0][0];
        }
        bool matchesForm = false;
        bool constantsEqual = false;
        if (!c.isNull())
        {
          if (n[1][0] == t && n[1][1].isConst())
          {
            matchesForm = true;
            constantsEqual = (n[1][1] == c);
          }
          else if (n[1][1] == t && n[1][0].isConst())
          {
            matchesForm = true;
            constantsEqual = (n[1][0] == c);
          }
        }
        if (matchesForm)
        {
          if (constantsEqual)
          {
            return RewriteResponse(REWRITE_DONE, d_true);
          }
          else
          {
            if (t.getType().isCardinalityLessThan(2))
            {
              return RewriteResponse(REWRITE_DONE, d_false);
            }
            else
            {
              Node neitherEquality =
                  (makeNegation(n[0])).andNode(makeNegation(n[1]));
              return RewriteResponse(REWRITE_AGAIN, neitherEquality);
            }
          }
        }
      }
      // sort
      if (n[0].getId() > n[1].getId())
      {
        return RewriteResponse(REWRITE_AGAIN,
                               nm->mkNode(Kind::EQUAL, n[1], n[0]));
      }
      return RewriteResponse(REWRITE_DONE, n);
    }
    case Kind::XOR:
    {
      // rewrite simple cases of XOR
      if (n[0] == d_true)
      {
        // XOR true x
        return RewriteResponse(REWRITE_AGAIN, makeNegation(n[1]));
      }
      else if (n[1] == d_true)
      {
        // XOR x true
        return RewriteResponse(REWRITE_AGAIN, makeNegation(n[0]));
      }
      else if (n[0] == d_false)
      {
        // XOR false x
        return RewriteResponse(REWRITE_AGAIN, n[1]);
      }
      else if (n[1] == d_false)
      {
        // XOR x false
        return RewriteResponse(REWRITE_AGAIN, n[0]);
      }
      else if (n[0] == n[1])
      {
        // XOR x x
        return RewriteResponse(REWRITE_DONE, d_false);
      }
      else if (n[0].getKind() == Kind::NOT && n[0][0] == n[1])
      {
        // XOR (NOT x) x
        return RewriteResponse(REWRITE_DONE, d_true);
      }
      else if (n[1].getKind() == Kind::NOT && n[1][0] == n[0])
      {
        // XOR x (NOT x)
        return RewriteResponse(REWRITE_DONE, d_true);
      }
      break;
    }
    case Kind::ITE:
    {
      // non-Boolean-valued ITEs should have been removed in place of
      // a variable
      // rewrite simple cases of ITE
      if (n[0].isConst())
      {
        if (n[0] == d_true)
        {
          // ITE true x y
          Trace("bool-ite")
              << "TheoryBoolRewriter::preRewrite_ITE: n[0] ==d_true " << n
              << ": " << n[1] << std::endl;
          return RewriteResponse(REWRITE_AGAIN, n[1]);
        }
        else
        {
          Assert(n[0] == d_false);
          // ITE false x y
          Trace("bool-ite")
              << "TheoryBoolRewriter::preRewrite_ITE: n[0] ==d_false " << n
              << ": " << n[1] << std::endl;
          return RewriteResponse(REWRITE_AGAIN, n[2]);
        }
      }
      else if (n[1].isConst())
      {
        if (n[1] == d_true && n[2] == d_false)
        {
          Trace("bool-ite") << "TheoryBoolRewriter::preRewrite_ITE: n[1] "
                               "==d_true && n[2] == d_false "
                            << n << ": " << n[0] << std::endl;
          return RewriteResponse(REWRITE_AGAIN, n[0]);
        }
        else if (n[1] == d_false && n[2] == d_true)
        {
          Trace("bool-ite") << "TheoryBoolRewriter::preRewrite_ITE: n[1] "
                               "== d_false && n[2] == d_true "
                            << n << ": " << n[0].notNode() << std::endl;
          return RewriteResponse(REWRITE_AGAIN, makeNegation(n[0]));
        }
      }

      if (n[0].getKind() == Kind::NOT)
      {
        // ite(not(c), x, y) ---> ite(c, y, x)
        return RewriteResponse(REWRITE_AGAIN,
                               nm->mkNode(Kind::ITE, n[0][0], n[2], n[1]));
      }

      int parityTmp;
      if ((parityTmp = equalityParity(n[1], n[2])) != 0)
      {
        Node resp = (parityTmp == 1) ? (Node)n[1] : n[0].eqNode(n[1]);
        Trace("bool-ite")
            << "TheoryBoolRewriter::preRewrite_ITE:  equalityParity n[1], n[2] "
            << parityTmp << " " << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
        // Curiously, this rewrite affects several benchmarks dramatically,
        // including copy_array and some simple_startup - disable for now } else
        // if (n[0].getKind() == Kind::NOT) {
        //   return RewriteResponse(REWRITE_AGAIN, n[0][0].iteNode(n[2], n[1]));
      }
      else if (!n[1].isConst() && (parityTmp = equalityParity(n[0], n[1])) != 0)
      {
        // (parityTmp == 1) if n[0] == n[1]
        // otherwise, n[0] == not(n[1]) or not(n[0]) == n[1]

        // if n[1] is constant this can loop, this is possible in prewrite
        Node resp = n[0].iteNode((parityTmp == 1) ? d_true : d_false, n[2]);
        Trace("bool-ite")
            << "TheoryBoolRewriter::preRewrite_ITE: equalityParity n[0], n[1] "
            << parityTmp << " " << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
      }
      else if (!n[2].isConst() && (parityTmp = equalityParity(n[0], n[2])) != 0)
      {
        // (parityTmp == 1) if n[0] == n[2]
        // otherwise, n[0] == not(n[2]) or not(n[0]) == n[2]
        Node resp = n[0].iteNode(n[1], (parityTmp == 1) ? d_false : d_true);
        Trace("bool-ite")
            << "TheoryBoolRewriter::preRewrite_ITE: equalityParity n[0], n[2] "
            << parityTmp << " " << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
      }
      else if (n[1].getKind() == Kind::ITE
               && (parityTmp = equalityParity(n[0], n[1][0])) != 0)
      {
        // (parityTmp == 1) then n : (ite c (ite c x y) z)
        // (parityTmp > 1)  then n : (ite c (ite (not c) x y) z) or
        // n: (ite (not c) (ite c x y) z)
        Node resp = n[0].iteNode((parityTmp == 1) ? n[1][1] : n[1][2], n[2]);
        Trace("bool-ite")
            << "TheoryBoolRewriter::preRewrite: equalityParity n[0], n[1][0] "
            << parityTmp << " " << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
      }
      else if (n[2].getKind() == Kind::ITE
               && (parityTmp = equalityParity(n[0], n[2][0])) != 0)
      {
        // (parityTmp == 1) then n : (ite c x (ite c y z))
        // (parityTmp > 1)  then n : (ite c x (ite (not c) y z)) or
        // n: (ite (not c) x (ite c y z))
        Node resp = n[0].iteNode(n[1], (parityTmp == 1) ? n[2][2] : n[2][1]);
        Trace("bool-ite")
            << "TheoryBoolRewriter::preRewrite: equalityParity n[0], n[2][0] "
            << parityTmp << " " << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
      }

    // Rewrites for ITEs with a constant branch. These rewrites are applied
    // after the parity rewrites above because they may simplify ITEs such as
    // `(ite c c true)` to `(ite c true true)`. As a result, we avoid
    // introducing an unnecessary conjunction/disjunction here.
      if (n[1].isConst() && (n[1] == d_true || n[1] == d_false))
      {
        // ITE C true y --> C v y
        // ITE C false y --> ~C ^ y
        Node resp =
            n[1] == d_true ? n[0].orNode(n[2]) : (n[0].negate()).andNode(n[2]);
        Trace("bool-ite") << "TheoryBoolRewriter::preRewrite_ITE: n[1] const "
                          << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
      }
      else if (n[2].isConst() && (n[2] == d_true || n[2] == d_false))
      {
        // ITE C x true --> ~C v x
        // ITE C x false --> C ^ x
        Node resp =
            n[2] == d_true ? (n[0].negate()).orNode(n[1]) : n[0].andNode(n[1]);
        Trace("bool-ite") << "TheoryBoolRewriter::preRewrite_ITE: n[2] const "
                          << n << ": " << resp << std::endl;
        return RewriteResponse(REWRITE_AGAIN, resp);
    }

    break;
    }
  default:
    return RewriteResponse(REWRITE_DONE, n);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal
