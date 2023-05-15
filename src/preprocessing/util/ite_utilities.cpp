/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Aina Niemetz, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simplifications for ITE expressions.
 *
 * This module implements preprocessing phases designed to simplify ITE
 * expressions.  Based on:
 * Kim, Somenzi, Jin.  Efficient Term-ITE Conversion for SMT.  FMCAD 2009.
 * Burch, Jerry.  Techniques for Verifying Superscalar Microprocessors.  DAC
 *'96
 */
#include "preprocessing/util/ite_utilities.h"

#include <utility>

#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/passes/rewrite.h"
#include "theory/theory.h"
#include "util/rational.h"

using namespace std;
namespace cvc5::internal {
namespace preprocessing {
namespace util {

namespace ite {

inline static bool isTermITE(TNode e)
{
  return (e.getKind() == kind::ITE && !e.getType().isBoolean());
}

inline static bool triviallyContainsNoTermITEs(TNode e)
{
  return e.isConst() || e.isVar();
}

static bool isTheoryAtom(TNode a)
{
  using namespace kind;
  switch (a.getKind())
  {
    case EQUAL:
    case DISTINCT: return !(a[0].getType().isBoolean());

    /* from uf */
    case APPLY_UF: return a.getType().isBoolean();
    case CARDINALITY_CONSTRAINT:
    case DIVISIBLE:
    case LT:
    case LEQ:
    case GT:
    case GEQ:
    case IS_INTEGER:
    case BITVECTOR_COMP:
    case BITVECTOR_ULT:
    case BITVECTOR_ULE:
    case BITVECTOR_UGT:
    case BITVECTOR_UGE:
    case BITVECTOR_SLT:
    case BITVECTOR_SLE:
    case BITVECTOR_SGT:
    case BITVECTOR_SGE: return true;
    default: return false;
  }
}

struct CTIVStackElement
{
  TNode curr;
  unsigned pos;
  CTIVStackElement() : curr(), pos(0) {}
  CTIVStackElement(TNode c) : curr(c), pos(0) {}
}; /* CTIVStackElement */

}  // namespace ite

ITEUtilities::ITEUtilities(Env& env)
    : EnvObj(env),
      d_containsVisitor(new ContainsTermITEVisitor()),
      d_compressor(NULL),
      d_simplifier(NULL),
      d_careSimp(NULL)
{
  Assert(d_containsVisitor != NULL);
}

ITEUtilities::~ITEUtilities()
{
  if (d_simplifier != NULL)
  {
    delete d_simplifier;
  }
  if (d_compressor != NULL)
  {
    delete d_compressor;
  }
  if (d_careSimp != NULL)
  {
    delete d_careSimp;
  }
}

Node ITEUtilities::simpITE(TNode assertion)
{
  if (d_simplifier == NULL)
  {
    d_simplifier = new ITESimplifier(d_env, d_containsVisitor.get());
  }
  return d_simplifier->simpITE(assertion);
}

bool ITEUtilities::simpIteDidALotOfWorkHeuristic() const
{
  if (d_simplifier == NULL)
  {
    return false;
  }
  else
  {
    return d_simplifier->doneALotOfWorkHeuristic();
  }
}

/* returns false if an assertion is discovered to be equal to false. */
bool ITEUtilities::compress(AssertionPipeline* assertionsToPreprocess)
{
  if (d_compressor == NULL)
  {
    d_compressor = new ITECompressor(d_env, d_containsVisitor.get());
  }
  return d_compressor->compress(assertionsToPreprocess);
}

Node ITEUtilities::simplifyWithCare(TNode e)
{
  if (d_careSimp == NULL)
  {
    d_careSimp = new ITECareSimplifier();
  }
  return d_careSimp->simplifyWithCare(e);
}

void ITEUtilities::clear()
{
  if (d_simplifier != NULL)
  {
    d_simplifier->clearSimpITECaches();
  }
  if (d_compressor != NULL)
  {
    d_compressor->garbageCollect();
  }
  if (d_careSimp != NULL)
  {
    d_careSimp->clear();
  }
  d_containsVisitor->garbageCollect();
}

/** ContainsTermITEVisitor. */
ContainsTermITEVisitor::ContainsTermITEVisitor() : d_cache() {}
ContainsTermITEVisitor::~ContainsTermITEVisitor() {}
bool ContainsTermITEVisitor::containsTermITE(TNode e)
{
  /* throughout execution skip through NOT nodes. */
  e = (e.getKind() == kind::NOT) ? e[0] : e;
  if (ite::triviallyContainsNoTermITEs(e))
  {
    return false;
  }

  NodeBoolMap::const_iterator end = d_cache.end();
  NodeBoolMap::const_iterator tmp_it = d_cache.find(e);
  if (tmp_it != end)
  {
    return (*tmp_it).second;
  }

  bool foundTermIte = false;
  std::vector<ite::CTIVStackElement> stack;
  stack.push_back(ite::CTIVStackElement(e));
  while (!foundTermIte && !stack.empty())
  {
    ite::CTIVStackElement& top = stack.back();
    TNode curr = top.curr;
    if (top.pos >= curr.getNumChildren())
    {
      // all of the children have been visited
      // no term ites were found
      d_cache[curr] = false;
      stack.pop_back();
    }
    else
    {
      // this is someone's child
      TNode child = curr[top.pos];
      child = (child.getKind() == kind::NOT) ? child[0] : child;
      ++top.pos;
      if (ite::triviallyContainsNoTermITEs(child))
      {
        // skip
      }
      else
      {
        tmp_it = d_cache.find(child);
        if (tmp_it != end)
        {
          foundTermIte = (*tmp_it).second;
        }
        else
        {
          stack.push_back(ite::CTIVStackElement(child));
          foundTermIte = ite::isTermITE(child);
        }
      }
    }
  }
  if (foundTermIte)
  {
    while (!stack.empty())
    {
      TNode curr = stack.back().curr;
      stack.pop_back();
      d_cache[curr] = true;
    }
  }
  return foundTermIte;
}
void ContainsTermITEVisitor::garbageCollect() { d_cache.clear(); }

/** IncomingArcCounter. */
IncomingArcCounter::IncomingArcCounter(bool skipVars, bool skipConstants)
    : d_reachCount(), d_skipVariables(skipVars), d_skipConstants(skipConstants)
{
}
IncomingArcCounter::~IncomingArcCounter() {}

void IncomingArcCounter::computeReachability(
    const std::vector<Node>& assertions)
{
  std::vector<TNode> tovisit(assertions.begin(), assertions.end());

  while (!tovisit.empty())
  {
    TNode back = tovisit.back();
    tovisit.pop_back();

    bool skip = false;
    switch (back.getMetaKind())
    {
      case kind::metakind::CONSTANT: skip = d_skipConstants; break;
      case kind::metakind::VARIABLE: skip = d_skipVariables; break;
      default: break;
    }

    if (skip)
    {
      continue;
    }
    if (d_reachCount.find(back) != d_reachCount.end())
    {
      d_reachCount[back] = 1 + d_reachCount[back];
    }
    else
    {
      d_reachCount[back] = 1;
      for (TNode::iterator cit = back.begin(), end = back.end(); cit != end;
           ++cit)
      {
        tovisit.push_back(*cit);
      }
    }
  }
}

void IncomingArcCounter::clear() { d_reachCount.clear(); }

/** ITECompressor. */
ITECompressor::ITECompressor(Env& env, ContainsTermITEVisitor* contains)
    : EnvObj(env),
      d_contains(contains),
      d_assertions(NULL),
      d_incoming(true, true),
      d_statistics(env.getStatisticsRegistry())
{
  Assert(d_contains != NULL);

  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

ITECompressor::~ITECompressor() { reset(); }

void ITECompressor::reset()
{
  d_incoming.clear();
  d_compressed.clear();
}

void ITECompressor::garbageCollect() { reset(); }

ITECompressor::Statistics::Statistics(StatisticsRegistry& reg)
    : d_compressCalls(reg.registerInt("ite-simp::compressCalls")),
      d_skolemsAdded(reg.registerInt("ite-simp::skolems"))
{
}

Node ITECompressor::push_back_boolean(Node original, Node compressed)
{
  Node rewritten = rewrite(compressed);
  // There is a bug if the rewritter takes a pure boolean expression
  // and changes its theory
  if (rewritten.isConst())
  {
    d_compressed[compressed] = rewritten;
    d_compressed[original] = rewritten;
    d_compressed[rewritten] = rewritten;
    return rewritten;
  }
  else if (d_compressed.find(rewritten) != d_compressed.end())
  {
    Node res = d_compressed[rewritten];
    d_compressed[original] = res;
    d_compressed[compressed] = res;
    return res;
  }
  else if (rewritten.isVar()
           || (rewritten.getKind() == kind::NOT && rewritten[0].isVar()))
  {
    d_compressed[original] = rewritten;
    d_compressed[compressed] = rewritten;
    d_compressed[rewritten] = rewritten;
    return rewritten;
  }
  else
  {
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node skolem = sm->mkDummySkolem("compress", nm->booleanType());
    d_compressed[rewritten] = skolem;
    d_compressed[original] = skolem;
    d_compressed[compressed] = skolem;

    Node iff = skolem.eqNode(rewritten);
    d_assertions->push_back(iff);
    ++(d_statistics.d_skolemsAdded);
    return skolem;
  }
}

bool ITECompressor::multipleParents(TNode c)
{
  return d_incoming.lookupIncoming(c) >= 2;
}

Node ITECompressor::compressBooleanITEs(Node toCompress)
{
  Assert(toCompress.getKind() == kind::ITE);
  Assert(toCompress.getType().isBoolean());

  if (!(toCompress[1] == d_false || toCompress[2] == d_false))
  {
    Node cmpCnd = compressBoolean(toCompress[0]);
    if (cmpCnd.isConst())
    {
      Node branch = (cmpCnd == d_true) ? toCompress[1] : toCompress[2];
      Node res = compressBoolean(branch);
      d_compressed[toCompress] = res;
      return res;
    }
    else
    {
      Node cmpThen = compressBoolean(toCompress[1]);
      Node cmpElse = compressBoolean(toCompress[2]);
      Node newIte = cmpCnd.iteNode(cmpThen, cmpElse);
      if (multipleParents(toCompress))
      {
        return push_back_boolean(toCompress, newIte);
      }
      else
      {
        return newIte;
      }
    }
  }

  NodeBuilder nb(kind::AND);
  Node curr = toCompress;
  while (curr.getKind() == kind::ITE
         && (curr[1] == d_false || curr[2] == d_false)
         && (!multipleParents(curr) || curr == toCompress))
  {
    bool negateCnd = (curr[1] == d_false);
    Node compressCnd = compressBoolean(curr[0]);
    if (compressCnd.isConst())
    {
      if (compressCnd.getConst<bool>() == negateCnd)
      {
        return push_back_boolean(toCompress, d_false);
      }
      else
      {
        // equivalent to true don't push back
      }
    }
    else
    {
      Node pb = negateCnd ? compressCnd.notNode() : compressCnd;
      nb << pb;
    }
    curr = negateCnd ? curr[2] : curr[1];
  }
  Assert(toCompress != curr);

  nb << compressBoolean(curr);
  Node res = nb.getNumChildren() == 1 ? nb[0] : (Node)nb;
  return push_back_boolean(toCompress, res);
}

Node ITECompressor::compressTerm(Node toCompress)
{
  if (toCompress.isConst() || toCompress.isVar())
  {
    return toCompress;
  }

  if (d_compressed.find(toCompress) != d_compressed.end())
  {
    return d_compressed[toCompress];
  }
  if (toCompress.getKind() == kind::ITE)
  {
    Node cmpCnd = compressBoolean(toCompress[0]);
    if (cmpCnd.isConst())
    {
      Node branch = (cmpCnd == d_true) ? toCompress[1] : toCompress[2];
      Node res = compressTerm(branch);
      d_compressed[toCompress] = res;
      return res;
    }
    else
    {
      Node cmpThen = compressTerm(toCompress[1]);
      Node cmpElse = compressTerm(toCompress[2]);
      Node newIte = cmpCnd.iteNode(cmpThen, cmpElse);
      d_compressed[toCompress] = newIte;
      return newIte;
    }
  }

  NodeBuilder nb(toCompress.getKind());

  if (toCompress.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    nb << (toCompress.getOperator());
  }
  for (Node::iterator it = toCompress.begin(), end = toCompress.end();
       it != end;
       ++it)
  {
    nb << compressTerm(*it);
  }
  Node compressed = (Node)nb;
  if (multipleParents(toCompress))
  {
    d_compressed[toCompress] = compressed;
  }
  return compressed;
}

Node ITECompressor::compressBoolean(Node toCompress)
{
  static int instance = 0;
  ++instance;
  if (toCompress.isConst() || toCompress.isVar())
  {
    return toCompress;
  }
  if (d_compressed.find(toCompress) != d_compressed.end())
  {
    return d_compressed[toCompress];
  }
  else if (toCompress.getKind() == kind::ITE)
  {
    return compressBooleanITEs(toCompress);
  }
  else
  {
    bool ta = ite::isTheoryAtom(toCompress);
    NodeBuilder nb(toCompress.getKind());
    if (toCompress.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      nb << (toCompress.getOperator());
    }
    for (Node::iterator it = toCompress.begin(), end = toCompress.end();
         it != end;
         ++it)
    {
      Node pb = (ta) ? compressTerm(*it) : compressBoolean(*it);
      nb << pb;
    }
    Node compressed = nb;
    if (ta || multipleParents(toCompress))
    {
      return push_back_boolean(toCompress, compressed);
    }
    else
    {
      return compressed;
    }
  }
}

bool ITECompressor::compress(AssertionPipeline* assertionsToPreprocess)
{
  reset();

  d_assertions = assertionsToPreprocess;
  d_incoming.computeReachability(assertionsToPreprocess->ref());

  ++(d_statistics.d_compressCalls);
  verbose(2) << "Computed reachability" << endl;

  bool nofalses = true;
  const std::vector<Node>& assertions = assertionsToPreprocess->ref();
  size_t original_size = assertions.size();
  verbose(2) << "compressing " << original_size << endl;
  for (size_t i = 0; i < original_size && nofalses; ++i)
  {
    Node assertion = assertions[i];
    Node compressed = compressBoolean(assertion);
    Node rewritten = rewrite(compressed);
    // replace
    assertionsToPreprocess->replace(i, rewritten);
    Assert(!d_contains->containsTermITE(rewritten));

    nofalses = (rewritten != d_false);
  }

  d_assertions = NULL;

  return nofalses;
}

TermITEHeightCounter::TermITEHeightCounter() : d_termITEHeight() {}

TermITEHeightCounter::~TermITEHeightCounter() {}

void TermITEHeightCounter::clear() { d_termITEHeight.clear(); }

size_t TermITEHeightCounter::cache_size() const
{
  return d_termITEHeight.size();
}

namespace ite {
struct TITEHStackElement
{
  TNode curr;
  unsigned pos;
  uint32_t maxChildHeight;
  TITEHStackElement() : curr(), pos(0), maxChildHeight(0) {}
  TITEHStackElement(TNode c) : curr(c), pos(0), maxChildHeight(0) {}
};
} /* namespace ite */

uint32_t TermITEHeightCounter::termITEHeight(TNode e)
{
  if (ite::triviallyContainsNoTermITEs(e))
  {
    return 0;
  }

  NodeCountMap::const_iterator end = d_termITEHeight.end();
  NodeCountMap::const_iterator tmp_it = d_termITEHeight.find(e);
  if (tmp_it != end)
  {
    return (*tmp_it).second;
  }

  uint32_t returnValue = 0;
  // This is initially 0 as the very first call this is included in the max,
  // but this has no effect.
  std::vector<ite::TITEHStackElement> stack;
  stack.push_back(ite::TITEHStackElement(e));
  while (!stack.empty())
  {
    ite::TITEHStackElement& top = stack.back();
    top.maxChildHeight = std::max(top.maxChildHeight, returnValue);
    TNode curr = top.curr;
    if (top.pos >= curr.getNumChildren())
    {
      // done with the current node
      returnValue = top.maxChildHeight + (ite::isTermITE(curr) ? 1 : 0);
      d_termITEHeight[curr] = returnValue;
      stack.pop_back();
      continue;
    }
    else
    {
      if (top.pos == 0 && curr.getKind() == kind::ITE)
      {
        ++top.pos;
        returnValue = 0;
        continue;
      }
      // this is someone's child
      TNode child = curr[top.pos];
      ++top.pos;
      if (ite::triviallyContainsNoTermITEs(child))
      {
        returnValue = 0;
      }
      else
      {
        tmp_it = d_termITEHeight.find(child);
        if (tmp_it != end)
        {
          returnValue = (*tmp_it).second;
        }
        else
        {
          stack.push_back(ite::TITEHStackElement(child));
        }
      }
    }
  }
  return returnValue;
}

ITESimplifier::ITESimplifier(Env& env, ContainsTermITEVisitor* contains)
    : EnvObj(env),
      d_containsVisitor(contains),
      d_termITEHeight(),
      d_constantLeaves(),
      d_allocatedConstantLeaves(),
      d_citeEqConstApplications(0),
      d_constantIteEqualsConstantCache(),
      d_replaceOverCache(),
      d_replaceOverTermIteCache(),
      d_leavesConstCache(),
      d_simpConstCache(),
      d_simpContextCache(),
      d_simpITECache(),
      d_statistics(env.getStatisticsRegistry())
{
  Assert(d_containsVisitor != NULL);
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

ITESimplifier::~ITESimplifier()
{
  clearSimpITECaches();
  Assert(d_constantLeaves.empty());
  Assert(d_allocatedConstantLeaves.empty());
}

bool ITESimplifier::leavesAreConst(TNode e)
{
  return leavesAreConst(e, d_env.theoryOf(e));
}

void ITESimplifier::clearSimpITECaches()
{
  verbose(2) << "clear ite caches " << endl;
  for (size_t i = 0, N = d_allocatedConstantLeaves.size(); i < N; ++i)
  {
    NodeVec* curr = d_allocatedConstantLeaves[i];
    delete curr;
  }
  d_citeEqConstApplications = 0;
  d_constantLeaves.clear();
  d_allocatedConstantLeaves.clear();
  d_termITEHeight.clear();
  d_constantIteEqualsConstantCache.clear();
  d_replaceOverCache.clear();
  d_replaceOverTermIteCache.clear();
  d_simpITECache.clear();
  d_simpVars.clear();
  d_simpConstCache.clear();
  d_leavesConstCache.clear();
  d_simpContextCache.clear();
}

bool ITESimplifier::doneALotOfWorkHeuristic() const
{
  static const size_t SIZE_BOUND = 1000;
  verbose(2) << "d_citeEqConstApplications size " << d_citeEqConstApplications
         << endl;
  return (d_citeEqConstApplications > SIZE_BOUND);
}

ITESimplifier::Statistics::Statistics(StatisticsRegistry& reg)
    : d_maxNonConstantsFolded(
        reg.registerInt("ite-simp::maxNonConstantsFolded")),
      d_unexpected(reg.registerInt("ite-simp::unexpected")),
      d_unsimplified(reg.registerInt("ite-simp::unsimplified")),
      d_exactMatchFold(reg.registerInt("ite-simp::exactMatchFold")),
      d_binaryPredFold(reg.registerInt("ite-simp::binaryPredFold")),
      d_specialEqualityFolds(reg.registerInt("ite-simp::specialEqualityFolds")),
      d_simpITEVisits(reg.registerInt("ite-simp::simpITE.visits")),
      d_inSmaller(reg.registerHistogram<uint32_t>("ite-simp::inSmaller"))
{
}

bool ITESimplifier::isConstantIte(TNode e)
{
  if (e.isConst())
  {
    return true;
  }
  else if (ite::isTermITE(e))
  {
    NodeVec* constants = computeConstantLeaves(e);
    return constants != NULL;
  }
  else
  {
    return false;
  }
}

ITESimplifier::NodeVec* ITESimplifier::computeConstantLeaves(TNode ite)
{
  Assert(ite::isTermITE(ite));
  ConstantLeavesMap::const_iterator it = d_constantLeaves.find(ite);
  ConstantLeavesMap::const_iterator end = d_constantLeaves.end();
  if (it != end)
  {
    return (*it).second;
  }
  TNode thenB = ite[1];
  TNode elseB = ite[2];

  // special case 2 constant children
  if (thenB.isConst() && elseB.isConst())
  {
    NodeVec* pair = new NodeVec(2);
    d_allocatedConstantLeaves.push_back(pair);

    (*pair)[0] = std::min(thenB, elseB);
    (*pair)[1] = std::max(thenB, elseB);
    d_constantLeaves[ite] = pair;
    return pair;
  }
  // At least 1 is an ITE
  if (!(thenB.isConst() || thenB.getKind() == kind::ITE)
      || !(elseB.isConst() || elseB.getKind() == kind::ITE))
  {
    // Cannot be a termITE tree
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  // At least 1 is not a constant
  TNode definitelyITE = thenB.isConst() ? elseB : thenB;
  TNode maybeITE = thenB.isConst() ? thenB : elseB;

  NodeVec* defChildren = computeConstantLeaves(definitelyITE);
  if (defChildren == NULL)
  {
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  NodeVec scratch;
  NodeVec* maybeChildren = NULL;
  if (maybeITE.getKind() == kind::ITE)
  {
    maybeChildren = computeConstantLeaves(maybeITE);
  }
  else
  {
    scratch.push_back(maybeITE);
    maybeChildren = &scratch;
  }
  if (maybeChildren == NULL)
  {
    d_constantLeaves[ite] = NULL;
    return NULL;
  }

  NodeVec* both = new NodeVec(defChildren->size() + maybeChildren->size());
  d_allocatedConstantLeaves.push_back(both);
  NodeVec::iterator newEnd;
  newEnd = std::set_union(defChildren->begin(),
                          defChildren->end(),
                          maybeChildren->begin(),
                          maybeChildren->end(),
                          both->begin());
  both->resize(newEnd - both->begin());
  d_constantLeaves[ite] = both;
  return both;
}

// This is uncached! Better for protoyping or getting limited size examples
struct IteTreeSearchData
{
  set<Node> visited;
  set<Node> constants;
  set<Node> nonConstants;
  int maxConstants;
  int maxNonconstants;
  int maxDepth;
  bool failure;
  IteTreeSearchData()
      : maxConstants(-1), maxNonconstants(-1), maxDepth(-1), failure(false)
  {
  }
};
void iteTreeSearch(Node e, int depth, IteTreeSearchData& search)
{
  if (search.maxDepth >= 0 && depth > search.maxDepth)
  {
    search.failure = true;
  }
  if (search.failure)
  {
    return;
  }
  if (search.visited.find(e) != search.visited.end())
  {
    return;
  }
  else
  {
    search.visited.insert(e);
  }

  if (e.isConst())
  {
    search.constants.insert(e);
    if (search.maxConstants >= 0
        && search.constants.size() > (unsigned)search.maxConstants)
    {
      search.failure = true;
    }
  }
  else if (e.getKind() == kind::ITE)
  {
    iteTreeSearch(e[1], depth + 1, search);
    iteTreeSearch(e[2], depth + 1, search);
  }
  else
  {
    search.nonConstants.insert(e);
    if (search.maxNonconstants >= 0
        && search.nonConstants.size() > (unsigned)search.maxNonconstants)
    {
      search.failure = true;
    }
  }
}

Node ITESimplifier::replaceOver(Node n, Node replaceWith, Node simpVar)
{
  if (n == simpVar)
  {
    return replaceWith;
  }
  else if (n.getNumChildren() == 0)
  {
    return n;
  }
  Assert(n.getNumChildren() > 0);
  Assert(!n.isVar());

  pair<Node, Node> p = make_pair(n, replaceWith);
  if (d_replaceOverCache.find(p) != d_replaceOverCache.end())
  {
    return d_replaceOverCache[p];
  }

  NodeBuilder builder(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << n.getOperator();
  }
  unsigned i = 0;
  for (; i < n.getNumChildren(); ++i)
  {
    Node newChild = replaceOver(n[i], replaceWith, simpVar);
    builder << newChild;
  }
  // Mark the substitution and continue
  Node result = builder;
  d_replaceOverCache[p] = result;
  return result;
}

Node ITESimplifier::replaceOverTermIte(Node e, Node simpAtom, Node simpVar)
{
  if (e.getKind() == kind::ITE)
  {
    pair<Node, Node> p = make_pair(e, simpAtom);
    if (d_replaceOverTermIteCache.find(p) != d_replaceOverTermIteCache.end())
    {
      return d_replaceOverTermIteCache[p];
    }
    Assert(!e.getType().isBoolean());
    Node cnd = e[0];
    Node newThen = replaceOverTermIte(e[1], simpAtom, simpVar);
    Node newElse = replaceOverTermIte(e[2], simpAtom, simpVar);
    Node newIte = cnd.iteNode(newThen, newElse);
    d_replaceOverTermIteCache[p] = newIte;
    return newIte;
  }
  else
  {
    return replaceOver(simpAtom, e, simpVar);
  }
}

Node ITESimplifier::attemptLiftEquality(TNode atom)
{
  if (atom.getKind() == kind::EQUAL)
  {
    TNode left = atom[0];
    TNode right = atom[1];
    if ((left.getKind() == kind::ITE || right.getKind() == kind::ITE)
        && !(left.getKind() == kind::ITE && right.getKind() == kind::ITE))
    {
      // exactly 1 is an ite
      TNode ite = left.getKind() == kind::ITE ? left : right;
      TNode notIte = left.getKind() == kind::ITE ? right : left;

      if (notIte == ite[1])
      {
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(d_true, notIte.eqNode(ite[2]));
      }
      else if (notIte == ite[2])
      {
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(notIte.eqNode(ite[1]), d_true);
      }
      if (notIte.isConst() && (ite[1].isConst() || ite[2].isConst()))
      {
        ++(d_statistics.d_exactMatchFold);
        return ite[0].iteNode(notIte.eqNode(ite[1]), notIte.eqNode(ite[2]));
      }
    }
  }

  // try a similar more relaxed version for non-equality operators
  if (atom.getMetaKind() == kind::metakind::OPERATOR
      && atom.getNumChildren() == 2 && !atom[1].getType().isBoolean())
  {
    TNode left = atom[0];
    TNode right = atom[1];
    if ((left.getKind() == kind::ITE || right.getKind() == kind::ITE)
        && !(left.getKind() == kind::ITE && right.getKind() == kind::ITE))
    {
      // exactly 1 is an ite
      bool leftIsIte = left.getKind() == kind::ITE;
      Node ite = leftIsIte ? left : right;
      Node notIte = leftIsIte ? right : left;

      if (notIte.isConst())
      {
        IteTreeSearchData search;
        search.maxNonconstants = 2;
        iteTreeSearch(ite, 0, search);
        if (!search.failure)
        {
          d_statistics.d_maxNonConstantsFolded.maxAssign(
              search.nonConstants.size());
          Trace("ite::simpite") << "used " << search.nonConstants.size()
                                << " nonconstants" << endl;
          NodeManager* nm = NodeManager::currentNM();
          Node simpVar = getSimpVar(notIte.getType());
          TNode newLeft = leftIsIte ? simpVar : notIte;
          TNode newRight = leftIsIte ? notIte : simpVar;
          Node newAtom = nm->mkNode(atom.getKind(), newLeft, newRight);

          ++(d_statistics.d_binaryPredFold);
          return replaceOverTermIte(ite, newAtom, simpVar);
        }
      }
    }
  }

  // TODO "This is way too tailored. Must generalize!"
  if (atom.getKind() == kind::EQUAL && atom.getNumChildren() == 2
      && ite::isTermITE(atom[0]) && atom[1].getKind() == kind::MULT
      && atom[1].getNumChildren() == 2 && atom[1][0].isConst()
      && atom[1][0].getConst<Rational>().isNegativeOne()
      && ite::isTermITE(atom[1][1])
      && d_termITEHeight.termITEHeight(atom[0]) == 1
      && d_termITEHeight.termITEHeight(atom[1][1]) == 1
      && (atom[0][1].isConst() || atom[0][2].isConst())
      && (atom[1][1][1].isConst() || atom[1][1][2].isConst()))
  {
    // expand all 4 cases

    Node negOne = atom[1][0];

    Node lite = atom[0];
    Node lC = lite[0];
    Node lT = lite[1];
    Node lE = lite[2];

    NodeManager* nm = NodeManager::currentNM();
    Node negRite = atom[1][1];
    Node rC = negRite[0];
    Node rT = nm->mkNode(kind::MULT, negOne, negRite[1]);
    Node rE = nm->mkNode(kind::MULT, negOne, negRite[2]);

    // (ite lC lT lE) = (ite rC rT rE)
    // (ite lc (= lT (ite rC rT rE) (= lE (ite rC rT rE))))
    // (ite lc (ite rC (= lT rT) (= lT rE))
    //         (ite rC (= lE rT) (= lE rE)))

    Node eqTT = lT.eqNode(rT);
    Node eqTE = lT.eqNode(rE);
    Node eqET = lE.eqNode(rT);
    Node eqEE = lE.eqNode(rE);
    Node thenLC = rC.iteNode(eqTT, eqTE);
    Node elseLC = rC.iteNode(eqET, eqEE);
    Node newIte = lC.iteNode(thenLC, elseLC);

    ++(d_statistics.d_specialEqualityFolds);
    return newIte;
  }
  return Node::null();
}

// Interesting classes of atoms:
// 2. Contains constants and 1 constant term ite
// 3. Contains 2 constant term ites
Node ITESimplifier::transformAtom(TNode atom)
{
  if (!d_containsVisitor->containsTermITE(atom))
  {
    if (atom.getKind() == kind::EQUAL && atom[0].isConst() && atom[1].isConst())
    {
      // constant equality
      return NodeManager::currentNM()->mkConst<bool>(atom[0] == atom[1]);
    }
    return Node::null();
  }
  else
  {
    Node acr = attemptConstantRemoval(atom);
    if (!acr.isNull())
    {
      return acr;
    }
    // Node ale = attemptLiftEquality(atom);
    // if(!ale.isNull()){
    //   //return ale;
    // }
    return Node::null();
  }
}

static unsigned numBranches = 0;
static unsigned numFalseBranches = 0;
static unsigned itesMade = 0;

Node ITESimplifier::constantIteEqualsConstant(TNode cite, TNode constant)
{
  static int instance = 0;
  ++instance;
  Trace("ite::constantIteEqualsConstant")
      << instance << "constantIteEqualsConstant(" << cite << ", " << constant
      << ")" << endl;
  if (cite.isConst())
  {
    Node res = (cite == constant) ? d_true : d_false;
    Trace("ite::constantIteEqualsConstant") << instance << "->" << res << endl;
    return res;
  }
  std::pair<Node, Node> pair = make_pair(cite, constant);

  NodePairMap::const_iterator eq_pos =
      d_constantIteEqualsConstantCache.find(pair);
  if (eq_pos != d_constantIteEqualsConstantCache.end())
  {
    Trace("ite::constantIteEqualsConstant")
        << instance << "->" << (*eq_pos).second << endl;
    return (*eq_pos).second;
  }

  ++d_citeEqConstApplications;

  NodeVec* leaves = computeConstantLeaves(cite);
  Assert(leaves != NULL);
  if (std::binary_search(leaves->begin(), leaves->end(), constant))
  {
    if (leaves->size() == 1)
    {
      // probably unreachable
      d_constantIteEqualsConstantCache[pair] = d_true;
      Trace("ite::constantIteEqualsConstant")
          << instance << "->" << d_true << endl;
      return d_true;
    }
    else
    {
      Assert(cite.getKind() == kind::ITE);
      TNode cnd = cite[0];
      TNode tB = cite[1];
      TNode fB = cite[2];
      Node tEqs = constantIteEqualsConstant(tB, constant);
      Node fEqs = constantIteEqualsConstant(fB, constant);
      Node boolIte = cnd.iteNode(tEqs, fEqs);
      if (!(tEqs.isConst() || fEqs.isConst()))
      {
        ++numBranches;
      }
      if (!(tEqs == d_false || fEqs == d_false))
      {
        ++numFalseBranches;
      }
      ++itesMade;
      d_constantIteEqualsConstantCache[pair] = boolIte;
      // Trace("ite::constantIteEqualsConstant") << instance << "->" << boolIte
      // << endl;
      return boolIte;
    }
  }
  else
  {
    d_constantIteEqualsConstantCache[pair] = d_false;
    Trace("ite::constantIteEqualsConstant")
        << instance << "->" << d_false << endl;
    return d_false;
  }
}

Node ITESimplifier::intersectConstantIte(TNode lcite, TNode rcite)
{
  // intersect the constant ite trees lcite and rcite

  if (lcite.isConst() || rcite.isConst())
  {
    bool lIsConst = lcite.isConst();
    TNode constant = lIsConst ? lcite : rcite;
    TNode cite = lIsConst ? rcite : lcite;

    (d_statistics.d_inSmaller) << 1;
    unsigned preItesMade = itesMade;
    unsigned preNumBranches = numBranches;
    unsigned preNumFalseBranches = numFalseBranches;
    Node bterm = constantIteEqualsConstant(cite, constant);
    Trace("intersectConstantIte") << (numBranches - preNumBranches) << " "
                                  << (numFalseBranches - preNumFalseBranches)
                                  << " " << (itesMade - preItesMade) << endl;
    return bterm;
  }
  Assert(lcite.getKind() == kind::ITE);
  Assert(rcite.getKind() == kind::ITE);

  NodeVec* leftValues = computeConstantLeaves(lcite);
  NodeVec* rightValues = computeConstantLeaves(rcite);

  uint32_t smaller = std::min(leftValues->size(), rightValues->size());

  (d_statistics.d_inSmaller) << smaller;
  NodeVec intersection(smaller, Node::null());
  NodeVec::iterator newEnd;
  newEnd = std::set_intersection(leftValues->begin(),
                                 leftValues->end(),
                                 rightValues->begin(),
                                 rightValues->end(),
                                 intersection.begin());
  intersection.resize(newEnd - intersection.begin());
  if (intersection.empty())
  {
    return d_false;
  }
  else
  {
    NodeBuilder nb(kind::OR);
    NodeVec::const_iterator it = intersection.begin(), end = intersection.end();
    for (; it != end; ++it)
    {
      Node inBoth = *it;
      Node lefteq = constantIteEqualsConstant(lcite, inBoth);
      Node righteq = constantIteEqualsConstant(rcite, inBoth);
      Node bothHold = lefteq.andNode(righteq);
      nb << bothHold;
    }
    Node result = (nb.getNumChildren() > 1) ? (Node)nb : nb[0];
    return result;
  }
}

Node ITESimplifier::attemptEagerRemoval(TNode atom)
{
  if (atom.getKind() == kind::EQUAL)
  {
    TNode left = atom[0];
    TNode right = atom[1];
    if ((left.isConst() && right.getKind() == kind::ITE && isConstantIte(right))
        || (right.isConst() && left.getKind() == kind::ITE
            && isConstantIte(left)))
    {
      TNode constant = left.isConst() ? left : right;
      TNode cite = left.isConst() ? right : left;

      std::pair<Node, Node> pair = make_pair(cite, constant);
      NodePairMap::const_iterator eq_pos =
          d_constantIteEqualsConstantCache.find(pair);
      if (eq_pos != d_constantIteEqualsConstantCache.end())
      {
        Node ret = (*eq_pos).second;
        if (ret.isConst())
        {
          return ret;
        }
        else
        {
          return Node::null();
        }
      }

      NodeVec* leaves = computeConstantLeaves(cite);
      Assert(leaves != NULL);
      if (!std::binary_search(leaves->begin(), leaves->end(), constant))
      {
        d_constantIteEqualsConstantCache[pair] = d_false;
        return d_false;
      }
    }
  }
  return Node::null();
}

Node ITESimplifier::attemptConstantRemoval(TNode atom)
{
  if (atom.getKind() == kind::EQUAL)
  {
    TNode left = atom[0];
    TNode right = atom[1];
    if (isConstantIte(left) && isConstantIte(right))
    {
      return intersectConstantIte(left, right);
    }
  }
  return Node::null();
}

bool ITESimplifier::leavesAreConst(TNode e, theory::TheoryId tid)
{
  Assert((e.getKind() == kind::ITE && !e.getType().isBoolean())
         || d_env.theoryOf(e) != theory::THEORY_BOOL);
  if (e.isConst())
  {
    return true;
  }

  unordered_map<Node, bool>::iterator it;
  it = d_leavesConstCache.find(e);
  if (it != d_leavesConstCache.end())
  {
    return (*it).second;
  }

  if (!containsTermITE(e) && theory::Theory::isLeafOf(e, tid))
  {
    d_leavesConstCache[e] = false;
    return false;
  }

  Assert(e.getNumChildren() > 0);
  size_t k = 0, sz = e.getNumChildren();

  if (e.getKind() == kind::ITE)
  {
    k = 1;
  }

  for (; k < sz; ++k)
  {
    if (!leavesAreConst(e[k], tid))
    {
      d_leavesConstCache[e] = false;
      return false;
    }
  }
  d_leavesConstCache[e] = true;
  return true;
}

Node ITESimplifier::simpConstants(TNode simpContext,
                                  TNode iteNode,
                                  TNode simpVar)
{
  NodePairMap::iterator it;
  it = d_simpConstCache.find(pair<Node, Node>(simpContext, iteNode));
  if (it != d_simpConstCache.end())
  {
    return (*it).second;
  }

  if (iteNode.getKind() == kind::ITE)
  {
    NodeBuilder builder(kind::ITE);
    builder << iteNode[0];
    unsigned i = 1;
    for (; i < iteNode.getNumChildren(); ++i)
    {
      Node n = simpConstants(simpContext, iteNode[i], simpVar);
      if (n.isNull())
      {
        return n;
      }
      builder << n;
    }
    // Mark the substitution and continue
    Node result = builder;
    result = rewrite(result);
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = result;
    return result;
  }

  if (!containsTermITE(iteNode))
  {
    Node n = rewrite(simpContext.substitute(simpVar, iteNode));
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }

  Node iteNode2;
  Node simpVar2;
  d_simpContextCache.clear();
  Node simpContext2 = createSimpContext(iteNode, iteNode2, simpVar2);
  if (!simpContext2.isNull())
  {
    Assert(!iteNode2.isNull());
    simpContext2 = simpContext.substitute(simpVar, simpContext2);
    Node n = simpConstants(simpContext2, iteNode2, simpVar2);
    if (n.isNull())
    {
      return n;
    }
    d_simpConstCache[pair<Node, Node>(simpContext, iteNode)] = n;
    return n;
  }
  return Node();
}

Node ITESimplifier::getSimpVar(TypeNode t)
{
  std::unordered_map<TypeNode, Node>::iterator it;
  it = d_simpVars.find(t);
  if (it != d_simpVars.end())
  {
    return (*it).second;
  }
  SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
  Node var = sm->mkDummySkolem(
      "iteSimp", t, "is a variable resulting from ITE simplification");
  d_simpVars[t] = var;
  return var;
}

Node ITESimplifier::createSimpContext(TNode c, Node& iteNode, Node& simpVar)
{
  NodeMap::iterator it;
  it = d_simpContextCache.find(c);
  if (it != d_simpContextCache.end())
  {
    return (*it).second;
  }

  if (!containsTermITE(c))
  {
    d_simpContextCache[c] = c;
    return c;
  }

  if (c.getKind() == kind::ITE && !c.getType().isBoolean())
  {
    // Currently only support one ite node in a simp context
    // Return Null if more than one is found
    if (!iteNode.isNull())
    {
      return Node();
    }
    simpVar = getSimpVar(c.getType());
    if (simpVar.isNull())
    {
      return Node();
    }
    d_simpContextCache[c] = simpVar;
    iteNode = c;
    return simpVar;
  }

  NodeBuilder builder(c.getKind());
  if (c.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << c.getOperator();
  }
  unsigned i = 0;
  for (; i < c.getNumChildren(); ++i)
  {
    Node newChild = createSimpContext(c[i], iteNode, simpVar);
    if (newChild.isNull())
    {
      return newChild;
    }
    builder << newChild;
  }
  // Mark the substitution and continue
  Node result = builder;
  d_simpContextCache[c] = result;
  return result;
}
typedef std::unordered_set<Node> NodeSet;
void countReachable_(Node x, Kind k, NodeSet& visited, uint32_t& reached)
{
  if (visited.find(x) != visited.end())
  {
    return;
  }
  visited.insert(x);
  if (x.getKind() == k)
  {
    ++reached;
  }
  for (unsigned i = 0, N = x.getNumChildren(); i < N; ++i)
  {
    countReachable_(x[i], k, visited, reached);
  }
}

uint32_t countReachable(TNode x, Kind k)
{
  NodeSet visited;
  uint32_t reached = 0;
  countReachable_(x, k, visited, reached);
  return reached;
}

Node ITESimplifier::simpITEAtom(TNode atom)
{
  CVC5_UNUSED static int instance = 0;
  Trace("ite::atom") << "still simplifying " << (++instance) << endl;
  Node attempt = transformAtom(atom);
  Trace("ite::atom") << "  finished " << instance << endl;
  if (!attempt.isNull())
  {
    Node rewritten = rewrite(attempt);
    Trace("ite::print-success")
        << instance << " "
        << "rewriting " << countReachable(rewritten, kind::ITE) << " from "
        << countReachable(atom, kind::ITE) << endl
        << "\t rewritten " << rewritten << endl
        << "\t input " << atom << endl;
    return rewritten;
  }

  if (leavesAreConst(atom))
  {
    Node iteNode;
    Node simpVar;
    d_simpContextCache.clear();
    Node simpContext = createSimpContext(atom, iteNode, simpVar);
    if (!simpContext.isNull())
    {
      if (iteNode.isNull())
      {
        Assert(leavesAreConst(simpContext) && !containsTermITE(simpContext));
        ++(d_statistics.d_unexpected);
        Trace("ite::simpite") << instance << " "
                              << "how about?" << atom << endl;
        Trace("ite::simpite") << instance << " "
                              << "\t" << simpContext << endl;
        return rewrite(simpContext);
      }
      Node n = simpConstants(simpContext, iteNode, simpVar);
      if (!n.isNull())
      {
        ++(d_statistics.d_unexpected);
        Trace("ite::simpite") << instance << " "
                              << "here?" << atom << endl;
        Trace("ite::simpite") << instance << " "
                              << "\t" << n << endl;
        return n;
      }
    }
  }
  if (TraceIsOn("ite::simpite"))
  {
    if (countReachable(atom, kind::ITE) > 0)
    {
      Trace("ite::simpite") << instance << " "
                            << "remaining " << atom << endl;
    }
  }
  ++(d_statistics.d_unsimplified);
  return atom;
}

struct preprocess_stack_element
{
  TNode d_node;
  bool d_children_added;
  preprocess_stack_element(TNode node) : d_node(node), d_children_added(false)
  {
  }
}; /* struct preprocess_stack_element */

Node ITESimplifier::simpITE(TNode assertion)
{
  // Do a topological sort of the subexpressions and substitute them
  vector<preprocess_stack_element> toVisit;
  toVisit.push_back(assertion);

  static int call = 0;
  ++call;
  int iteration = 0;

  while (!toVisit.empty())
  {
    iteration++;
    // cout << "call  " << call << " : " << iteration << endl;
    // The current node we are processing
    preprocess_stack_element& stackHead = toVisit.back();
    TNode current = stackHead.d_node;

    // If node has no ITE's or already in the cache we're done, pop from the
    // stack
    if (current.getNumChildren() == 0
        || (d_env.theoryOf(current) != theory::THEORY_BOOL
            && !containsTermITE(current)))
    {
      d_simpITECache[current] = current;
      ++(d_statistics.d_simpITEVisits);
      toVisit.pop_back();
      continue;
    }

    NodeMap::iterator find = d_simpITECache.find(current);
    if (find != d_simpITECache.end())
    {
      toVisit.pop_back();
      continue;
    }

    // Not yet substituted, so process
    if (stackHead.d_children_added)
    {
      // Children have been processed, so substitute
      NodeBuilder builder(current.getKind());
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        builder << current.getOperator();
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i)
      {
        Assert(d_simpITECache.find(current[i]) != d_simpITECache.end());
        Node child = current[i];
        Node childRes = d_simpITECache[current[i]];
        builder << childRes;
      }
      // Mark the substitution and continue
      Node result = builder;

      // If this is an atom, we process it
      if (d_env.theoryOf(result) != theory::THEORY_BOOL
          && result.getType().isBoolean())
      {
        result = simpITEAtom(result);
      }

      // if(current != result && result.isConst()){
      //   static int instance = 0;
      //   //cout << instance << " " << result << current << endl;
      // }

      result = rewrite(result);
      d_simpITECache[current] = result;
      ++(d_statistics.d_simpITEVisits);
      toVisit.pop_back();
    }
    else
    {
      // Mark that we have added the children if any
      if (current.getNumChildren() > 0)
      {
        stackHead.d_children_added = true;
        // We need to add the children
        for (TNode::iterator child_it = current.begin();
             child_it != current.end();
             ++child_it)
        {
          TNode childNode = *child_it;
          NodeMap::iterator childFind = d_simpITECache.find(childNode);
          if (childFind == d_simpITECache.end())
          {
            toVisit.push_back(childNode);
          }
        }
      }
      else
      {
        // No children, so we're done
        d_simpITECache[current] = current;
        ++(d_statistics.d_simpITEVisits);
        toVisit.pop_back();
      }
    }
  }
  return d_simpITECache[assertion];
}

ITECareSimplifier::ITECareSimplifier() : d_careSetsOutstanding(0), d_usedSets()
{
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

ITECareSimplifier::~ITECareSimplifier()
{
  Assert(d_usedSets.empty());
  Assert(d_careSetsOutstanding == 0);
}

void ITECareSimplifier::clear()
{
  Assert(d_usedSets.empty());
  Assert(d_careSetsOutstanding == 0);
}

ITECareSimplifier::CareSetPtr ITECareSimplifier::getNewSet()
{
  if (d_usedSets.empty())
  {
    d_careSetsOutstanding++;
    return ITECareSimplifier::CareSetPtr::mkNew(*this);
  }
  else
  {
    ITECareSimplifier::CareSetPtr cs =
        ITECareSimplifier::CareSetPtr::recycle(d_usedSets.back());
    cs.getCareSet().clear();
    d_usedSets.pop_back();
    return cs;
  }
}

void ITECareSimplifier::updateQueue(CareMap& queue,
                                    TNode e,
                                    ITECareSimplifier::CareSetPtr& careSet)
{
  CareMap::iterator it = queue.find(e), iend = queue.end();
  if (it != iend)
  {
    set<Node>& cs2 = (*it).second.getCareSet();
    ITECareSimplifier::CareSetPtr csNew = getNewSet();
    set_intersection(careSet.getCareSet().begin(),
                     careSet.getCareSet().end(),
                     cs2.begin(),
                     cs2.end(),
                     inserter(csNew.getCareSet(), csNew.getCareSet().begin()));
    (*it).second = csNew;
  }
  else
  {
    queue[e] = careSet;
  }
}

Node ITECareSimplifier::substitute(TNode e,
                                   TNodeMap& substTable,
                                   TNodeMap& cache)
{
  TNodeMap::iterator it = cache.find(e), iend = cache.end();
  if (it != iend)
  {
    return it->second;
  }

  // do substitution?
  it = substTable.find(e);
  iend = substTable.end();
  if (it != iend)
  {
    Node result = substitute(it->second, substTable, cache);
    cache[e] = result;
    return result;
  }

  size_t sz = e.getNumChildren();
  if (sz == 0)
  {
    cache[e] = e;
    return e;
  }

  NodeBuilder builder(e.getKind());
  if (e.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << e.getOperator();
  }
  for (unsigned i = 0; i < e.getNumChildren(); ++i)
  {
    builder << substitute(e[i], substTable, cache);
  }

  Node result = builder;
  // it = substTable.find(result);
  // if (it != iend) {
  //   result = substitute(it->second, substTable, cache);
  // }
  cache[e] = result;
  return result;
}

Node ITECareSimplifier::simplifyWithCare(TNode e)
{
  TNodeMap substTable;

  /* This extra block is to trigger the destructors for cs and cs2
   * before starting garbage collection.
   */
  {
    CareMap queue;
    CareMap::iterator it;
    ITECareSimplifier::CareSetPtr cs = getNewSet();
    ITECareSimplifier::CareSetPtr cs2;
    queue[e] = cs;

    TNode v;
    bool done;
    unsigned i;

    while (!queue.empty())
    {
      it = queue.end();
      --it;
      v = it->first;
      cs = it->second;
      set<Node>& css = cs.getCareSet();
      queue.erase(v);

      done = false;
      set<Node>::iterator iCare, iCareEnd = css.end();

      switch (v.getKind())
      {
        case kind::ITE:
        {
          iCare = css.find(v[0]);
          if (iCare != iCareEnd)
          {
            Assert(substTable.find(v) == substTable.end());
            substTable[v] = v[1];
            updateQueue(queue, v[1], cs);
            done = true;
            break;
          }
          else
          {
            iCare = css.find(v[0].negate());
            if (iCare != iCareEnd)
            {
              Assert(substTable.find(v) == substTable.end());
              substTable[v] = v[2];
              updateQueue(queue, v[2], cs);
              done = true;
              break;
            }
          }
          updateQueue(queue, v[0], cs);
          cs2 = getNewSet();
          cs2.getCareSet() = css;
          cs2.getCareSet().insert(v[0]);
          updateQueue(queue, v[1], cs2);
          cs2 = getNewSet();
          cs2.getCareSet() = css;
          cs2.getCareSet().insert(v[0].negate());
          updateQueue(queue, v[2], cs2);
          done = true;
          break;
        }
        case kind::AND:
        {
          for (i = 0; i < v.getNumChildren(); ++i)
          {
            iCare = css.find(v[i].negate());
            if (iCare != iCareEnd)
            {
              Assert(substTable.find(v) == substTable.end());
              substTable[v] = d_false;
              done = true;
              break;
            }
          }
          if (done) break;

          Assert(v.getNumChildren() > 1);
          updateQueue(queue, v[0], cs);
          cs2 = getNewSet();
          cs2.getCareSet() = css;
          cs2.getCareSet().insert(v[0]);
          for (i = 1; i < v.getNumChildren(); ++i)
          {
            updateQueue(queue, v[i], cs2);
          }
          done = true;
          break;
        }
        case kind::OR:
        {
          for (i = 0; i < v.getNumChildren(); ++i)
          {
            iCare = css.find(v[i]);
            if (iCare != iCareEnd)
            {
              Assert(substTable.find(v) == substTable.end());
              substTable[v] = d_true;
              done = true;
              break;
            }
          }
          if (done) break;

          Assert(v.getNumChildren() > 1);
          updateQueue(queue, v[0], cs);
          cs2 = getNewSet();
          cs2.getCareSet() = css;
          cs2.getCareSet().insert(v[0].negate());
          for (i = 1; i < v.getNumChildren(); ++i)
          {
            updateQueue(queue, v[i], cs2);
          }
          done = true;
          break;
        }
        default: break;
      }

      if (done)
      {
        continue;
      }

      for (i = 0; i < v.getNumChildren(); ++i)
      {
        updateQueue(queue, v[i], cs);
      }
    }
  }
  /* Perform garbage collection. */
  while (!d_usedSets.empty())
  {
    CareSetPtrVal* used = d_usedSets.back();
    d_usedSets.pop_back();
    Assert(used->safeToGarbageCollect());
    delete used;
    Assert(d_careSetsOutstanding > 0);
    d_careSetsOutstanding--;
  }

  TNodeMap cache;
  return substitute(e, substTable, cache);
}

ITECareSimplifier::CareSetPtr ITECareSimplifier::CareSetPtr::mkNew(
    ITECareSimplifier& simp)
{
  CareSetPtrVal* val = new CareSetPtrVal(simp);
  return CareSetPtr(val);
}

}  // namespace util
}  // namespace preprocessing
}  // namespace cvc5::internal
