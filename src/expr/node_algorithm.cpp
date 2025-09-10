/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Common algorithms on nodes.
 *
 * This file implements common algorithms applied to nodes, such as checking if
 * a node contains a free or a bound variable.
 */

#include "expr/node_algorithm.h"

#include "expr/attribute.h"
#include "expr/cardinality_constraint.h"
#include "expr/dtype.h"

namespace cvc5::internal {
namespace expr {

bool hasSubterm(TNode n, TNode t, bool strict)
{
  if (!strict && n == t)
  {
    return true;
  }

  std::unordered_set<TNode> visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(n);

  // incrementally iterate and add to toProcess
  for (unsigned i = 0; i < toProcess.size(); ++i)
  {
    TNode current = toProcess[i];
    for (unsigned j = 0, j_end = current.getNumChildren(); j <= j_end; ++j)
    {
      TNode child;
      // try children then operator
      if (j < j_end)
      {
        child = current[j];
      }
      else if (current.hasOperator())
      {
        child = current.getOperator();
      }
      else
      {
        break;
      }
      if (child == t)
      {
        return true;
      }
      if (visited.find(child) != visited.end())
      {
        continue;
      }
      else
      {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
}

bool hasSubtermMulti(TNode n, TNode t)
{
  std::unordered_map<TNode, bool> visited;
  std::unordered_map<TNode, bool> contains;
  std::unordered_map<TNode, bool>::iterator it;
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
      if (cur == t)
      {
        visited[cur] = true;
        contains[cur] = true;
      }
      else
      {
        visited[cur] = false;
        visit.push_back(cur);
        for (const Node& cc : cur)
        {
          visit.push_back(cc);
        }
      }
    }
    else if (!it->second)
    {
      bool doesContain = false;
      for (const Node& cn : cur)
      {
        it = contains.find(cn);
        Assert(it != contains.end());
        if (it->second)
        {
          if (doesContain)
          {
            // two children have t, return true
            return true;
          }
          doesContain = true;
        }
      }
      contains[cur] = doesContain;
      visited[cur] = true;
    }
  } while (!visit.empty());
  return false;
}

bool hasSubtermKind(Kind k, Node n)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == k)
      {
        return true;
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

bool hasSubtermKinds(const std::unordered_set<Kind, kind::KindHashFunction>& ks,
                     TNode n)
{
  if (ks.empty())
  {
    return false;
  }
  std::unordered_set<TNode> visited;
  return hasSubtermKinds(ks, n, visited) != Kind::UNDEFINED_KIND;
}

Kind hasSubtermKinds(const std::unordered_set<Kind, kind::KindHashFunction>& ks,
                     TNode n,
                     std::unordered_set<TNode>& visited)
{
  Assert(!ks.empty());
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  Kind k;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      k = cur.getKind();
      if (ks.find(k) != ks.end())
      {
        return k;
      }
      visited.insert(cur);
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return Kind::UNDEFINED_KIND;
}

void getSubtermsKind(Kind k, TNode n, std::unordered_set<Node>& ts, bool nested)
{
  std::unordered_set<Kind, kind::KindHashFunction> ks{k};
  std::map<Kind, std::unordered_set<Node>> tsm;
  getSubtermsKinds(ks, n, tsm, nested);
  std::unordered_set<Node>& tsc = tsm[k];
  ts.insert(tsc.begin(), tsc.end());
}

void getSubtermsKinds(
    const std::unordered_set<Kind, kind::KindHashFunction>& ks,
    TNode n,
    std::map<Kind, std::unordered_set<Node>>& ts, bool nested)
{
  Assert(!ks.empty());
  for (Kind k : ks)
  {
    if (ts.find(k) == ts.end())
    {
      ts[k].clear();
    }
  }
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  Kind k;
  std::map<Kind, std::unordered_set<Node>>::iterator itt;
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      k = cur.getKind();
      itt = ts.find(k);
      if (itt != ts.end())
      {
        itt->second.insert(cur);
        if (!nested)
        {
          continue;
        }
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

bool hasSubterm(TNode n, const std::vector<Node>& t, bool strict)
{
  if (t.empty())
  {
    return false;
  }
  if (!strict && std::find(t.begin(), t.end(), n) != t.end())
  {
    return true;
  }

  std::unordered_set<TNode> visited;
  std::vector<TNode> toProcess;

  toProcess.push_back(n);

  // incrementally iterate and add to toProcess
  for (unsigned i = 0; i < toProcess.size(); ++i)
  {
    TNode current = toProcess[i];
    for (unsigned j = 0, j_end = current.getNumChildren(); j <= j_end; ++j)
    {
      TNode child;
      // try children then operator
      if (j < j_end)
      {
        child = current[j];
      }
      else if (current.hasOperator())
      {
        child = current.getOperator();
      }
      else
      {
        break;
      }
      if (std::find(t.begin(), t.end(), child) != t.end())
      {
        return true;
      }
      if (visited.find(child) != visited.end())
      {
        continue;
      }
      else
      {
        visited.insert(child);
        toProcess.push_back(child);
      }
    }
  }

  return false;
}

struct HasBoundVarTag
{
};
struct HasBoundVarComputedTag
{
};
/** Attribute true for expressions with bound variables in them */
typedef expr::Attribute<HasBoundVarTag, bool> HasBoundVarAttr;
typedef expr::Attribute<HasBoundVarComputedTag, bool> HasBoundVarComputedAttr;

bool hasBoundVar(TNode n)
{
  if (!n.getAttribute(HasBoundVarComputedAttr()))
  {
    bool hasBv = false;
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      hasBv = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end() && !hasBv; ++i)
      {
        if (hasBoundVar(*i))
        {
          hasBv = true;
          break;
        }
      }
    }
    if (!hasBv && n.hasOperator())
    {
      hasBv = hasBoundVar(n.getOperator());
    }
    n.setAttribute(HasBoundVarAttr(), hasBv);
    n.setAttribute(HasBoundVarComputedAttr(), true);
    Trace("bva") << n << " has bva : " << n.getAttribute(HasBoundVarAttr())
                 << std::endl;
    return hasBv;
  }
  return n.getAttribute(HasBoundVarAttr());
}

/**
 * Check variables internal, which is used as a helper to implement many of the
 * methods in this file.
 *
 * This computes the free variables in n, that is, the subterms of n of kind
 * BOUND_VARIABLE that are not bound in n or occur in scope, adds these to fvs
 * if computeFv is true.
 *
 * @param n The node under investigation
 * @param fvs The set which free variables are added to
 * @param scope The scope we are considering.
 * @param wasShadow Flag set to true if variable shadowing was encountered.
 * Only computed if checkShadow is true.
 * @param computeFv If this flag is false, then we only return true/false and
 * do not add to fvs.
 * @param checkShadow If this flag is true, we immediately return true if a
 * variable is shadowing. If this flag is false, we give an assertion failure
 * when this occurs.
 * @return true iff this node contains a free variable.
 */
bool checkVariablesInternal(TNode n,
                            std::unordered_set<Node>& fvs,
                            std::unordered_set<TNode>& scope,
                            bool& wasShadow,
                            bool computeFv = true,
                            bool checkShadow = false)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // can skip if it doesn't have a bound variable
    if (!hasBoundVar(cur))
    {
      continue;
    }
    std::unordered_set<TNode>::iterator itv = visited.find(cur);
    if (itv == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == Kind::BOUND_VARIABLE)
      {
        if (scope.find(cur) == scope.end())
        {
          if (computeFv)
          {
            fvs.insert(cur);
          }
          else
          {
            return true;
          }
        }
      }
      else if (cur.isClosure())
      {
        // add to scope
        std::vector<TNode> boundvars;
        for (const TNode& cn : cur[0])
        {
          if (scope.find(cn) != scope.end())
          {
            if (checkShadow)
            {
              wasShadow = true;
              return true;
            }
          }
          else
          {
            // add to scope if it is not shadowing
            boundvars.push_back(cn);
            scope.insert(cn);
          }
        }
        // must make recursive call to use separate cache
        if (checkVariablesInternal(
                cur[1], fvs, scope, wasShadow, computeFv, checkShadow)
            && !computeFv)
        {
          return true;
        }
        // cleanup
        for (const TNode& cn : boundvars)
        {
          scope.erase(cn);
        }
      }
      else
      {
        if (cur.hasOperator())
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  } while (!visit.empty());

  return !fvs.empty();
}

/** Same as above, without checking for shadowing */
bool getVariablesInternal(TNode n,
                          std::unordered_set<Node>& fvs,
                          std::unordered_set<TNode>& scope,
                          bool computeFv = true)
{
  bool wasShadow = false;
  return checkVariablesInternal(n, fvs, scope, wasShadow, computeFv, false);
}

bool hasFreeVar(TNode n)
{
  // optimization for variables and constants
  if (n.getNumChildren() == 0)
  {
    return n.getKind() == Kind::BOUND_VARIABLE;
  }
  std::unordered_set<Node> fvs;
  std::unordered_set<TNode> scope;
  return getVariablesInternal(n, fvs, scope, false);
}

bool hasFreeOrShadowedVar(TNode n, bool& wasShadow)
{
  // optimization for variables and constants
  if (n.getNumChildren() == 0)
  {
    return n.getKind() == Kind::BOUND_VARIABLE;
  }
  std::unordered_set<Node> fvs;
  std::unordered_set<TNode> scope;
  return checkVariablesInternal(n, fvs, scope, wasShadow, false, true);
}

struct HasClosureTag
{
};
struct HasClosureComputedTag
{
};
/** Attribute true for expressions with closures in them */
typedef expr::Attribute<HasClosureTag, bool> HasClosureAttr;
typedef expr::Attribute<HasClosureComputedTag, bool> HasClosureComputedAttr;

bool hasClosure(Node n)
{
  if (!n.getAttribute(HasClosureComputedAttr()))
  {
    bool hasC = false;
    if (n.isClosure())
    {
      hasC = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end() && !hasC; ++i)
      {
        hasC = hasClosure(*i);
      }
    }
    if (!hasC && n.hasOperator())
    {
      hasC = hasClosure(n.getOperator());
    }
    n.setAttribute(HasClosureAttr(), hasC);
    n.setAttribute(HasClosureComputedAttr(), true);
    return hasC;
  }
  return n.getAttribute(HasClosureAttr());
}

bool getFreeVariables(TNode n, std::unordered_set<Node>& fvs)
{
  std::unordered_set<TNode> scope;
  return getVariablesInternal(n, fvs, scope);
}

bool getFreeVariablesScope(TNode n,
                           std::unordered_set<Node>& fvs,
                           std::unordered_set<TNode>& scope)
{
  return getVariablesInternal(n, fvs, scope);
}
bool hasFreeVariablesScope(TNode n, std::unordered_set<TNode>& scope)
{
  std::unordered_set<Node> fvs;
  return getVariablesInternal(n, fvs, scope, false);
}

bool getVariables(TNode n, std::unordered_set<Node>& vs)
{
  std::unordered_set<TNode> visited;
  return getVariables(n, vs, visited);
}

bool getVariables(TNode n,
                  std::unordered_set<Node>& vs,
                  std::unordered_set<TNode>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    std::unordered_set<TNode>::iterator itv = visited.find(cur);
    if (itv == visited.end())
    {
      if (cur.isVar())
      {
        vs.insert(cur);
      }
      else
      {
        if (cur.hasOperator())
        {
          visit.push_back(cur.getOperator());
        }
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
      visited.insert(cur);
    }
  } while (!visit.empty());

  return !vs.empty();
}

void getSymbols(TNode n, std::unordered_set<Node>& syms)
{
  std::unordered_set<TNode> visited;
  getSymbols(n, syms, visited);
}

void getSymbols(TNode n,
                std::unordered_set<Node>& syms,
                std::unordered_set<TNode>& visited)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.isVar() && cur.getKind() != Kind::BOUND_VARIABLE)
      {
        syms.insert(cur);
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void getKindSubterms(TNode n,
                     Kind k,
                     bool topLevel,
                     std::unordered_set<Node>& ts)
{
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (cur.getKind() == k)
      {
        ts.insert(cur);
        if (topLevel)
        {
          // only considering top-level applications
          continue;
        }
      }
      if (cur.hasOperator())
      {
        visit.push_back(cur.getOperator());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void getOperatorsMap(TNode n, std::map<TypeNode, std::unordered_set<Node>>& ops)
{
  std::unordered_set<TNode> visited;
  getOperatorsMap(n, ops, visited);
}

void getOperatorsMap(TNode n,
                     std::map<TypeNode, std::unordered_set<Node>>& ops,
                     std::unordered_set<TNode>& visited)
{
  // nodes that we still need to visit
  std::vector<TNode> visit;
  // current node
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    // if cur is in the cache, do nothing
    if (visited.find(cur) == visited.end())
    {
      // fetch the correct type
      TypeNode tn = cur.getType();
      // add the current operator to the result
      if (cur.hasOperator())
      {
       Node o;
       if (cur.getMetaKind() == kind::metakind::PARAMETERIZED) {
         o = cur.getOperator();
       } else {
         o = cur.getNodeManager()->operatorOf(cur.getKind());
       }
        ops[tn].insert(o);
      }
      // add children to visit in the future
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void getTypes(TNode n, std::unordered_set<TypeNode>& types)
{
  std::unordered_set<TNode> visited;
  getTypes(n, types, visited);
}

void getTypes(TNode n,
              std::unordered_set<TypeNode>& types,
              std::unordered_set<TNode>& visited)
{
  std::unordered_set<TNode>::iterator it;
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
      visited.insert(cur);
      types.insert(cur.getType());
      // special cases where the type is not part of the AST
      if (cur.getKind() == Kind::CARDINALITY_CONSTRAINT)
      {
        types.insert(
            cur.getOperator().getConst<CardinalityConstraint>().getType());
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
}

void getComponentTypes(TypeNode t, std::unordered_set<TypeNode>& types)
{
  std::vector<TypeNode> toProcess;
  toProcess.push_back(t);
  do
  {
    TypeNode curr = toProcess.back();
    toProcess.pop_back();
    // if not already visited
    if (types.find(curr) == types.end())
    {
      types.insert(curr);
      // get component types from the children
      for (unsigned i = 0, nchild = curr.getNumChildren(); i < nchild; i++)
      {
        toProcess.push_back(curr[i]);
      }
    }
  } while (!toProcess.empty());
}

bool match(Node x, Node y, std::unordered_map<Node, Node>& subs)
{
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction> visited;
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction>::iterator
      it;
  std::unordered_map<Node, Node>::iterator subsIt;

  std::vector<std::pair<TNode, TNode>> stack;
  stack.emplace_back(x, y);
  std::pair<TNode, TNode> curr;

  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      // holds trivially
      continue;
    }
    it = visited.find(curr);
    if (it != visited.end())
    {
      // already processed
      continue;
    }
    visited.insert(curr);
    if (curr.first.getNumChildren() == 0)
    {
      if (!curr.first.getType().isComparableTo(curr.second.getType()))
      {
        // the two subterms have different types
        return false;
      }
      // if the two subterms are not equal and the first one is a bound
      // variable...
      if (curr.first.getKind() == Kind::BOUND_VARIABLE)
      {
        // and we have not seen this variable before...
        subsIt = subs.find(curr.first);
        if (subsIt == subs.cend())
        {
          // add the two subterms to `sub`
          subs.emplace(curr.first, curr.second);
        }
        else
        {
          // if we saw this variable before, make sure that (now and before) it
          // maps to the same subterm
          if (curr.second != subsIt->second)
          {
            return false;
          }
        }
      }
      else
      {
        // the two subterms are not equal
        return false;
      }
    }
    else
    {
      // if the two subterms are not equal, make sure that their operators are
      // equal
      // we compare operators instead of kinds because different terms may have
      // the same kind (both `(id x)` and `(square x)` have kind APPLY_UF)
      // since many builtin operators like `ADD` allow arbitrary number of
      // arguments, we also need to check if the two subterms have the same
      // number of children
      if (curr.first.getNumChildren() != curr.second.getNumChildren()
          || curr.first.getOperator() != curr.second.getOperator())
      {
        return false;
      }
      // recurse on children
      for (size_t i = 0, n = curr.first.getNumChildren(); i < n; ++i)
      {
        stack.emplace_back(curr.first[i], curr.second[i]);
      }
    }
  }
  return true;
}

void getConversionConditions(Node n1,
                             Node n2,
                             std::vector<Node>& eqs,
                             bool isHo)
{
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction> visited;
  std::unordered_set<std::pair<TNode, TNode>, TNodePairHashFunction>::iterator
      it;
  std::vector<std::pair<TNode, TNode>> stack;
  stack.emplace_back(n1, n2);
  std::pair<TNode, TNode> curr;
  while (!stack.empty())
  {
    curr = stack.back();
    stack.pop_back();
    if (curr.first == curr.second)
    {
      // holds trivially
      continue;
    }
    Assert(curr.first.getType() == curr.second.getType());
    it = visited.find(curr);
    if (it != visited.end())
    {
      // already processed
      continue;
    }
    visited.insert(curr);
    bool rec = false;
    if (curr.first.getNumChildren() > 0
        && curr.first.getNumChildren() == curr.second.getNumChildren())
    {
      size_t prevSize = stack.size();
      if (curr.first.getOperator() == curr.second.getOperator())
      {
        if (curr.first.isClosure())
        {
          // only recurse if equal variable lists
          rec = (curr.first[0] == curr.second[0]);
        }
        else
        {
          rec = true;
        }
      }
      else if (isHo && curr.first.getKind() == Kind::APPLY_UF
               && curr.second.getKind() == Kind::APPLY_UF)
      {
        rec = true;
        // if isHo, we recurse on distinct operators with the same type
        // note that it is redundant to check type here, as we check the
        // types of arguments below and undo if necessary
        stack.emplace_back(curr.first.getOperator(), curr.second.getOperator());
      }
      if (rec)
      {
        // recurse on children
        for (size_t i = 0, n = curr.first.getNumChildren(); i < n; ++i)
        {
          // if there is a type mismatch, we can't unify
          if (curr.first[i].getType() != curr.second[i].getType())
          {
            stack.resize(prevSize);
            rec = false;
            break;
          }
          stack.emplace_back(curr.first[i], curr.second[i]);
        }
      }
    }
    if (!rec)
    {
      eqs.push_back(curr.first.eqNode(curr.second));
    }
  }
}

bool isBooleanConnective(TNode cur)
{
  Kind k = cur.getKind();
  return k == Kind::NOT || k == Kind::IMPLIES || k == Kind::AND || k == Kind::OR
         || (k == Kind::ITE && cur.getType().isBoolean()) || k == Kind::XOR
         || (k == Kind::EQUAL && cur[0].getType().isBoolean());
}

bool isTheoryAtom(TNode n)
{
  Kind k = n.getKind();
  Assert(k != Kind::NOT);
  return k != Kind::AND && k != Kind::OR && k != Kind::IMPLIES && k != Kind::ITE
         && k != Kind::XOR && (k != Kind::EQUAL || !n[0].getType().isBoolean());
}

struct HasAbstractSubtermTag
{
};
struct HasAbstractSubtermComputedTag
{
};
/** Attribute true for expressions that have subterms with abstract type */
using AbstractSubtermVarAttr = expr::Attribute<HasAbstractSubtermTag, bool>;
using HasAbstractSubtermComputedAttr =
    expr::Attribute<HasAbstractSubtermComputedTag, bool>;

bool hasAbstractSubterm(TNode n)
{
  if (!n.getAttribute(HasAbstractSubtermComputedAttr()))
  {
    bool hasAbs = false;
    if (n.getType().isAbstract())
    {
      hasAbs = true;
    }
    else
    {
      for (auto i = n.begin(); i != n.end(); ++i)
      {
        if (hasAbstractSubterm(*i))
        {
          hasAbs = true;
          break;
        }
      }
    }
    if (!hasAbs && n.hasOperator())
    {
      hasAbs = hasAbstractSubterm(n.getOperator());
    }
    n.setAttribute(AbstractSubtermVarAttr(), hasAbs);
    n.setAttribute(HasAbstractSubtermComputedAttr(), true);
    return hasAbs;
  }
  return n.getAttribute(AbstractSubtermVarAttr());
}

}  // namespace expr
}  // namespace cvc5::internal
