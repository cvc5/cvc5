/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Evaluator for separation logic assertions against a concrete heap model.
 */

#include "theory/sep/sep_model_checker.h"

#include <algorithm>

#include "base/check.h"
#include "expr/node_algorithm.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

/**
 * The number of candidate fragments we are willing to consider while deciding
 * separating conjunctions, across a single evaluation.
 *
 * Searching for a partition is exponential in the number of heap cells, so it
 * has to be bounded. Bounding the search itself rather than the size of the
 * heap keeps the cost of check-model predictable while still deciding the
 * shapes that occur in practice: a conjunct whose cell count is fixed by its
 * syntax (see getExactSize) only ever generates fragments of that one size, so
 * a star of points-to atoms costs O(n^2) fragments in the size of the heap
 * rather than O(2^n).
 *
 * Exhausting the budget yields UNKNOWN, never FALSE, so the caller falls back
 * to the subsolver instead of reporting a spurious model failure.
 *
 * What this particular number buys, measured: a star of points-to atoms costs
 * n(n+1)/2 fragments, so it decides heaps of around 140 cells; a conjunct with
 * no fixed cell count costs 2^n, so it decides those up to 13 cells and hands
 * 14 and beyond to the subsolver.
 */
static constexpr size_t s_partitionBudget = 10000;

/**
 * The operators whose truth depends on which heap they are evaluated in.
 * SepModelChecker::hasSpatialSubterm is the only way in to this.
 */
static const std::unordered_set<Kind, kind::KindHashFunction> s_spatialKinds = {
    Kind::SEP_EMP,
    Kind::SEP_PTO,
    Kind::SEP_STAR,
    Kind::SEP_WAND,
    Kind::SEP_LABEL};

/**
 * Advance `sel`, a strictly increasing selection of `sel.size()` indices drawn
 * from {0, ..., n-1}, to the next such selection in lexicographic order.
 * Returns false if it was already the last one.
 */
static bool nextSelection(std::vector<size_t>& sel, size_t n)
{
  size_t k = sel.size();
  for (size_t i = k; i > 0; --i)
  {
    // the largest value index i-1 can take, leaving room for those after it
    if (sel[i - 1] != i - 1 + n - k)
    {
      sel[i - 1]++;
      for (size_t j = i; j < k; j++)
      {
        sel[j] = sel[j - 1] + 1;
      }
      return true;
    }
  }
  return false;
}

SepModelChecker::SepModelChecker(const TheoryModel* m)
    : d_model(m), d_budget(s_partitionBudget)
{
}

bool SepModelChecker::hasSpatialSubterm(TNode n)
{
  return expr::hasSubtermKinds(s_spatialKinds, n);
}

Node SepModelChecker::evaluate(const TheoryModel* m, TNode heap, TNode a)
{
  SepModelChecker smc(m);
  if (!smc.extractHeap(heap))
  {
    return Node::null();
  }
  Tri r = smc.eval(a, smc.d_heap);
  if (r == Tri::UNKNOWN)
  {
    return Node::null();
  }
  return a.getNodeManager()->mkConst(r == Tri::TRUE);
}

bool SepModelChecker::addCell(TNode pto)
{
  Node l = d_model->getValue(pto[0]);
  Node d = d_model->getValue(pto[1]);
  if (!l.isConst() || !d.isConst())
  {
    // The heap model is meant to be fully concrete, and TheorySep asserts as
    // much when it builds it, but that assertion is compiled out of a
    // production build. A cell whose data is a placeholder rather than a value
    // would compare unequal to everything here, so refuse the heap rather than
    // decide anything against it.
    return false;
  }
  d_heap.emplace_back(l, d);
  return true;
}

bool SepModelChecker::extractHeap(TNode heap)
{
  Kind hk = heap.getKind();
  if (hk == Kind::SEP_EMP)
  {
    // empty heap
    return true;
  }
  if (hk == Kind::SEP_PTO)
  {
    return addCell(heap);
  }
  if (hk == Kind::SEP_STAR)
  {
    for (const Node& child : heap)
    {
      if (child.getKind() != Kind::SEP_PTO || !addCell(child))
      {
        return false;
      }
    }
    return true;
  }
  return false;
}

bool SepModelChecker::collectLocations(TNode setVal, std::vector<Node>& locs)
{
  switch (setVal.getKind())
  {
    case Kind::SET_EMPTY: return true;
    case Kind::SET_SINGLETON:
    {
      Node l = d_model->getValue(setVal[0]);
      if (!l.isConst())
      {
        return false;
      }
      locs.push_back(l);
      return true;
    }
    case Kind::SET_UNION:
      return collectLocations(setVal[0], locs)
             && collectLocations(setVal[1], locs);
    default: return false;
  }
}

SepModelChecker::Tri SepModelChecker::eval(TNode phi, const Heap& h)
{
  Kind k = phi.getKind();
  switch (k)
  {
    case Kind::SEP_EMP:
    {
      // emp holds iff the (sub-)heap is empty
      return fromBool(h.empty());
    }
    case Kind::SEP_PTO:
    {
      // (pto l d) holds iff the sub-heap is exactly the single cell l -> d
      Node l = d_model->getValue(phi[0]);
      Node d = d_model->getValue(phi[1]);
      if (!l.isConst() || !d.isConst())
      {
        // could not resolve the location or data to a concrete value
        return Tri::UNKNOWN;
      }
      if (h.size() != 1)
      {
        return Tri::FALSE;
      }
      return fromBool(h[0].first == l && h[0].second == d);
    }
    case Kind::SEP_STAR:
    {
      std::vector<Node> children(phi.begin(), phi.end());
      return evalStar(children, 0, h);
    }
    case Kind::SEP_WAND:
    {
      // The magic wand quantifies over all heaps that could be joined with the
      // current one; this cannot be checked against a single concrete model.
      return Tri::UNKNOWN;
    }
    case Kind::SEP_LABEL:
    {
      // (@sep_label phi L): phi holds over the sub-heap whose domain is the
      // model value of the label set L. These labeled atoms are the internal
      // facts checked by TheoryEngine::checkTheoryAssertionsWithModel.
      if (!d_model->isSepHeapLabel(phi[1]))
      {
        // L is not a fragment of this heap. It labels one of the heaps a magic
        // wand quantifies over, which the model says nothing about, so
        // restricting the model heap to it would answer a question about a
        // different heap. Note the label's value can perfectly well overlap
        // this heap's locations, so this cannot be decided from the value.
        return Tri::UNKNOWN;
      }
      Node lblVal = d_model->getValue(phi[1]);
      std::vector<Node> locs;
      if (!collectLocations(lblVal, locs))
      {
        return Tri::UNKNOWN;
      }
      // restrict the current sub-heap to the labeled domain
      Heap sub;
      for (const Cell& c : h)
      {
        if (std::find(locs.begin(), locs.end(), c.first) != locs.end())
        {
          sub.push_back(c);
        }
      }
      return eval(phi[0], sub);
    }
    case Kind::NOT:
    {
      Tri r = eval(phi[0], h);
      if (r == Tri::UNKNOWN)
      {
        return Tri::UNKNOWN;
      }
      return r == Tri::TRUE ? Tri::FALSE : Tri::TRUE;
    }
    case Kind::AND:
    {
      bool anyUnknown = false;
      for (const Node& c : phi)
      {
        Tri r = eval(c, h);
        if (r == Tri::FALSE)
        {
          return Tri::FALSE;
        }
        anyUnknown = anyUnknown || (r == Tri::UNKNOWN);
      }
      return anyUnknown ? Tri::UNKNOWN : Tri::TRUE;
    }
    case Kind::OR:
    {
      bool anyUnknown = false;
      for (const Node& c : phi)
      {
        Tri r = eval(c, h);
        if (r == Tri::TRUE)
        {
          return Tri::TRUE;
        }
        anyUnknown = anyUnknown || (r == Tri::UNKNOWN);
      }
      return anyUnknown ? Tri::UNKNOWN : Tri::FALSE;
    }
    case Kind::IMPLIES:
    {
      // a => b  is  (not a) or b
      Tri a = eval(phi[0], h);
      Tri b = eval(phi[1], h);
      if (a == Tri::FALSE || b == Tri::TRUE)
      {
        return Tri::TRUE;
      }
      if (a == Tri::UNKNOWN || b == Tri::UNKNOWN)
      {
        return Tri::UNKNOWN;
      }
      // a is TRUE and b is FALSE
      return Tri::FALSE;
    }
    case Kind::XOR:
    case Kind::EQUAL:
    {
      // Boolean (dis)equality between spatial formulas, e.g. (= sep1 sep2).
      // For non-Boolean equalities we fall through to the model evaluation
      // below, since those are heap-independent.
      if (phi[0].getType().isBoolean())
      {
        Tri a = eval(phi[0], h);
        Tri b = eval(phi[1], h);
        if (a == Tri::UNKNOWN || b == Tri::UNKNOWN)
        {
          return Tri::UNKNOWN;
        }
        bool eq = (a == b);
        return fromBool(k == Kind::EQUAL ? eq : !eq);
      }
      break;
    }
    case Kind::ITE:
    {
      if (phi[0].getType().isBoolean() && phi.getType().isBoolean())
      {
        Tri c = eval(phi[0], h);
        if (c == Tri::TRUE)
        {
          return eval(phi[1], h);
        }
        if (c == Tri::FALSE)
        {
          return eval(phi[2], h);
        }
        return Tri::UNKNOWN;
      }
      break;
    }
    default: break;
  }
  // We do not know how to decompose phi. If it still has a spatial operator
  // beneath it, we cannot hand it to the model: the model evaluates spatial
  // atoms against the whole heap, whereas here they have to hold of the
  // sub-heap h.
  if (hasSpatialSubterm(phi))
  {
    return Tri::UNKNOWN;
  }
  // Otherwise phi is heap-independent, so evaluate it in the model.
  Node v = d_model->getValue(phi);
  if (v.isConst() && v.getType().isBoolean())
  {
    return fromBool(v.getConst<bool>());
  }
  return Tri::UNKNOWN;
}

bool SepModelChecker::getExactSize(TNode phi, size_t& size)
{
  switch (phi.getKind())
  {
    case Kind::SEP_EMP:
      // emp holds only on the empty heap
      size = 0;
      return true;
    case Kind::SEP_PTO:
      // pto holds only on a heap of exactly one cell
      size = 1;
      return true;
    case Kind::SEP_STAR:
    {
      // a star of formulas with fixed cell counts has their sum
      size_t total = 0;
      for (const Node& c : phi)
      {
        size_t cs;
        if (!getExactSize(c, cs))
        {
          return false;
        }
        total += cs;
      }
      size = total;
      return true;
    }
    default: return false;
  }
}

SepModelChecker::Tri SepModelChecker::evalStar(
    const std::vector<Node>& children, size_t ci, const Heap& h)
{
  size_t n = children.size();
  Assert(ci < n);
  if (ci + 1 == n)
  {
    // last child must account for exactly the remaining cells
    return eval(children[ci], h);
  }
  size_t numCells = h.size();
  // If this child's syntax fixes how many cells it covers, only fragments of
  // that size are candidates; otherwise every subset is.
  size_t exact;
  bool hasExact = getExactSize(children[ci], exact);
  if (hasExact && exact > numCells)
  {
    // this child alone needs more cells than are left
    return Tri::FALSE;
  }
  size_t loSize = hasExact ? exact : 0;
  size_t hiSize = hasExact ? exact : numCells;
  bool anyUnknown = false;
  // Try each candidate fragment for children[ci], recursing on the complement
  // for the remaining children.
  for (size_t k = loSize; k <= hiSize; k++)
  {
    std::vector<size_t> sel(k);
    for (size_t i = 0; i < k; i++)
    {
      sel[i] = i;
    }
    do
    {
      if (d_budget == 0)
      {
        // Out of budget. We have not ruled out the fragments we did not get
        // to, so the star cannot be reported as false.
        return Tri::UNKNOWN;
      }
      d_budget--;
      Heap sub;
      Heap rest;
      size_t si = 0;
      for (size_t i = 0; i < numCells; ++i)
      {
        if (si < k && sel[si] == i)
        {
          sub.push_back(h[i]);
          si++;
        }
        else
        {
          rest.push_back(h[i]);
        }
      }
      Tri t1 = eval(children[ci], sub);
      if (t1 == Tri::FALSE)
      {
        continue;
      }
      Tri t2 = evalStar(children, ci + 1, rest);
      if (t2 == Tri::FALSE)
      {
        continue;
      }
      if (t1 == Tri::TRUE && t2 == Tri::TRUE)
      {
        return Tri::TRUE;
      }
      // one of the branches is UNKNOWN (and neither is FALSE): this partition
      // might satisfy the star, so we cannot conclude FALSE overall.
      anyUnknown = true;
    } while (nextSelection(sel, numCells));
  }
  return anyUnknown ? Tri::UNKNOWN : Tri::FALSE;
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal
