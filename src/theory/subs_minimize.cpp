/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of substitution minimization.
 */

#include "theory/subs_minimize.h"

#include "expr/node_algorithm.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/strings/word.h"
#include "util/rational.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

SubstitutionMinimize::SubstitutionMinimize(Env& env) : EnvObj(env) {}

bool SubstitutionMinimize::find(Node t,
                                Node target,
                                const std::vector<Node>& vars,
                                const std::vector<Node>& subs,
                                std::vector<Node>& reqVars)
{
  return findInternal(t, target, vars, subs, reqVars);
}

void getConjuncts(Node n, std::vector<Node>& conj)
{
  if (n.getKind() == AND)
  {
    for (const Node& nc : n)
    {
      conj.push_back(nc);
    }
  }
  else
  {
    conj.push_back(n);
  }
}

bool SubstitutionMinimize::findWithImplied(Node t,
                                           const std::vector<Node>& vars,
                                           const std::vector<Node>& subs,
                                           std::vector<Node>& reqVars,
                                           std::vector<Node>& impliedVars)
{
  NodeManager* nm = NodeManager::currentNM();
  Node truen = nm->mkConst(true);
  if (!findInternal(t, truen, vars, subs, reqVars))
  {
    return false;
  }
  if (reqVars.empty())
  {
    return true;
  }

  // map from conjuncts of t to whether they may be used to show an implied var
  std::vector<Node> tconj;
  getConjuncts(t, tconj);
  // map from conjuncts to their free symbols
  std::map<Node, std::unordered_set<Node> > tcFv;

  std::unordered_set<Node> reqSet;
  std::vector<Node> reqSubs;
  std::map<Node, unsigned> reqVarToIndex;
  for (const Node& v : reqVars)
  {
    reqVarToIndex[v] = reqSubs.size();
    const std::vector<Node>::const_iterator& it =
        std::find(vars.begin(), vars.end(), v);
    Assert(it != vars.end());
    ptrdiff_t pos = std::distance(vars.begin(), it);
    reqSubs.push_back(subs[pos]);
  }
  std::vector<Node> finalReqVars;
  for (const Node& v : vars)
  {
    if (reqVarToIndex.find(v) == reqVarToIndex.end())
    {
      // not a required variable, nothing to do
      continue;
    }
    unsigned vindex = reqVarToIndex[v];
    Node prev = reqSubs[vindex];
    // make identity substitution
    reqSubs[vindex] = v;
    bool madeImplied = false;
    // it is a required variable, can we make an implied variable?
    for (const Node& tc : tconj)
    {
      // ensure we've computed its free symbols
      std::map<Node, std::unordered_set<Node> >::iterator itf = tcFv.find(tc);
      if (itf == tcFv.end())
      {
        expr::getSymbols(tc, tcFv[tc]);
        itf = tcFv.find(tc);
      }
      // only have a chance if contains v
      if (itf->second.find(v) == itf->second.end())
      {
        continue;
      }
      // try the current substitution
      Node tcs = tc.substitute(
          reqVars.begin(), reqVars.end(), reqSubs.begin(), reqSubs.end());
      Node tcsr = rewrite(tcs);
      std::vector<Node> tcsrConj;
      getConjuncts(tcsr, tcsrConj);
      for (const Node& tcc : tcsrConj)
      {
        if (tcc.getKind() == EQUAL)
        {
          for (unsigned r = 0; r < 2; r++)
          {
            if (tcc[r] == v)
            {
              Node res = tcc[1 - r];
              if (res.isConst())
              {
                Assert(res == prev);
                madeImplied = true;
                break;
              }
            }
          }
        }
        if (madeImplied)
        {
          break;
        }
      }
      if (madeImplied)
      {
        break;
      }
    }
    if (!madeImplied)
    {
      // revert the substitution
      reqSubs[vindex] = prev;
      finalReqVars.push_back(v);
    }
    else
    {
      impliedVars.push_back(v);
    }
  }
  reqVars.clear();
  reqVars.insert(reqVars.end(), finalReqVars.begin(), finalReqVars.end());

  return true;
}

bool SubstitutionMinimize::findInternal(Node n,
                                        Node target,
                                        const std::vector<Node>& vars,
                                        const std::vector<Node>& subs,
                                        std::vector<Node>& reqVars)
{
  Trace("subs-min") << "Substitution minimize : " << std::endl;
  Trace("subs-min") << "  substitution : " << vars << " -> " << subs
                    << std::endl;
  Trace("subs-min") << "  node : " << n << std::endl;
  Trace("subs-min") << "  target : " << target << std::endl;

  Trace("subs-min") << "--- Compute values for subterms..." << std::endl;
  // the value of each subterm in n under the substitution
  std::unordered_map<TNode, Node> value;
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = value.find(cur);

    if (it == value.end())
    {
      if (cur.isVar())
      {
        const std::vector<Node>::const_iterator& iit =
            std::find(vars.begin(), vars.end(), cur);
        if (iit == vars.end())
        {
          value[cur] = cur;
        }
        else
        {
          ptrdiff_t pos = std::distance(vars.begin(), iit);
          value[cur] = subs[pos];
        }
      }
      else
      {
        value[cur] = Node::null();
        visit.push_back(cur);
        if (cur.getKind() == APPLY_UF)
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      if (cur.getNumChildren() > 0)
      {
        std::vector<Node> children;
        NodeBuilder nb(cur.getKind());
        if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          if (cur.getKind() == APPLY_UF)
          {
            children.push_back(cur.getOperator());
          }
          else
          {
            nb << cur.getOperator();
          }
        }
        children.insert(children.end(), cur.begin(), cur.end());
        for (const Node& cn : children)
        {
          it = value.find(cn);
          Assert(it != value.end());
          Assert(!it->second.isNull());
          nb << it->second;
        }
        ret = nb.constructNode();
        ret = rewrite(ret);
      }
      value[cur] = ret;
    }
  } while (!visit.empty());
  Assert(value.find(n) != value.end());
  Assert(!value.find(n)->second.isNull());

  Trace("subs-min") << "... got " << value[n] << std::endl;
  if (value[n] != target)
  {
    Trace("subs-min") << "... not equal to target " << target << std::endl;
    // depends on all variables
    for (const std::pair<const TNode, Node>& v : value)
    {
      if (v.first.isVar())
      {
        reqVars.push_back(v.first);
      }
    }
    return false;
  }

  Trace("subs-min") << "--- Compute relevant variables..." << std::endl;
  std::unordered_set<Node> rlvFv;
  // only variables that occur in assertions are relevant

  visit.push_back(n);
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator itv;
  do
  {
    cur = visit.back();
    visit.pop_back();
    itv = visited.find(cur);
    if (itv == visited.end())
    {
      visited.insert(cur);
      it = value.find(cur);
      if (it->second == cur)
      {
        // if its value is the same as current, there is nothing to do
      }
      else if (cur.isVar())
      {
        // must include
        rlvFv.insert(cur);
      }
      else if (cur.getKind() == ITE)
      {
        // only recurse on relevant branch
        Node bval = value[cur[0]];
        if (!bval.isNull() && bval.isConst())
        {
          unsigned cindex = bval.getConst<bool>() ? 1 : 2;
          visit.push_back(cur[0]);
          visit.push_back(cur[cindex]);
          continue;
        }
        // otherwise, we handle it normally below
      }
      if (cur.getNumChildren() > 0)
      {
        Kind ck = cur.getKind();
        bool alreadyJustified = false;

        // if the operator is an apply uf, check its value
        if (cur.getKind() == APPLY_UF)
        {
          Node op = cur.getOperator();
          it = value.find(op);
          Assert(it != value.end());
          TNode vop = it->second;
          if (vop.getKind() == LAMBDA)
          {
            visit.push_back(op);
            // do iterative partial evaluation on the body of the lambda
            Node curr = vop[1];
            for (unsigned i = 0, size = cur.getNumChildren(); i < size; i++)
            {
              it = value.find(cur[i]);
              Assert(it != value.end());
              Node scurr = curr.substitute(vop[0][i], it->second);
              // if the valuation of the i^th argument changes the
              // interpretation of the body of the lambda, then the i^th
              // argument is relevant to the substitution. Hence, we add
              // i to visit, and update curr below.
              if (scurr != curr)
              {
                curr = rewrite(scurr);
                visit.push_back(cur[i]);
              }
            }
            alreadyJustified = true;
          }
        }
        if (!alreadyJustified)
        {
          // a subset of the arguments of cur that fully justify the evaluation
          std::vector<unsigned> justifyArgs;
          if (cur.getNumChildren() > 1)
          {
            for (unsigned i = 0, size = cur.getNumChildren(); i < size; i++)
            {
              Node cn = cur[i];
              it = value.find(cn);
              Assert(it != value.end());
              Assert(!it->second.isNull());
              if (isSingularArg(it->second, ck, i))
              {
                // have we seen this argument already? if so, we are done
                if (visited.find(cn) != visited.end())
                {
                  alreadyJustified = true;
                  break;
                }
                justifyArgs.push_back(i);
              }
            }
          }
          // we need to recurse on at most one child
          if (!alreadyJustified && !justifyArgs.empty())
          {
            unsigned sindex = justifyArgs[0];
            // could choose a best index, for now, we just take the first
            visit.push_back(cur[sindex]);
            alreadyJustified = true;
          }
        }
        if (!alreadyJustified)
        {
          // must recurse on all arguments, including operator
          if (cur.getKind() == APPLY_UF)
          {
            visit.push_back(cur.getOperator());
          }
          for (const Node& cn : cur)
          {
            visit.push_back(cn);
          }
        }
      }
    }
  } while (!visit.empty());

  for (const Node& v : rlvFv)
  {
    Assert(std::find(vars.begin(), vars.end(), v) != vars.end());
    reqVars.push_back(v);
  }

  Trace("subs-min") << "... requires " << reqVars.size() << "/" << vars.size()
                    << " : " << reqVars << std::endl;

  return true;
}

bool SubstitutionMinimize::isSingularArg(Node n, Kind k, unsigned arg)
{
  // Notice that this function is hardcoded. We could compute this function
  // in a theory-independent way using partial evaluation. However, we
  // prefer performance to generality here.

  // TODO: a variant of this code is implemented in quantifiers::TermUtil.
  // These implementations should be merged (see #1216).
  if (!n.isConst())
  {
    return false;
  }
  if (k == AND)
  {
    return !n.getConst<bool>();
  }
  else if (k == OR)
  {
    return n.getConst<bool>();
  }
  else if (k == IMPLIES)
  {
    return arg == (n.getConst<bool>() ? 1 : 0);
  }
  if (k == MULT
      || (arg == 0
          && (k == DIVISION_TOTAL || k == INTS_DIVISION_TOTAL
              || k == INTS_MODULUS_TOTAL))
      || (arg == 2 && k == STRING_SUBSTR))
  {
    // zero
    if (n.getConst<Rational>().sgn() == 0)
    {
      return true;
    }
  }
  if (k == BITVECTOR_AND || k == BITVECTOR_MULT || k == BITVECTOR_UDIV
      || k == BITVECTOR_UREM
      || (arg == 0
          && (k == BITVECTOR_SHL || k == BITVECTOR_LSHR
              || k == BITVECTOR_ASHR)))
  {
    if (bv::utils::isZero(n))
    {
      return true;
    }
  }
  if (k == BITVECTOR_OR)
  {
    // bit-vector ones
    if (bv::utils::isOnes(n))
    {
      return true;
    }
  }

  if ((arg == 1 && k == STRING_CONTAINS) || (arg == 0 && k == STRING_SUBSTR))
  {
    // empty string
    if (strings::Word::getLength(n) == 0)
    {
      return true;
    }
  }
  if ((arg != 0 && k == STRING_SUBSTR) || (arg == 2 && k == STRING_INDEXOF))
  {
    // negative integer
    if (n.getConst<Rational>().sgn() < 0)
    {
      return true;
    }
  }
  return false;
}

}  // namespace theory
}  // namespace cvc5::internal
