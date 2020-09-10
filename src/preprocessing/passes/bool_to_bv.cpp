/*********************                                                        */
/*! \file bool_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Yoni Zohar, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BoolToBV preprocessing pass
 **
 **/

#include "preprocessing/passes/bool_to_bv.h"

#include <string>

#include "base/map_util.h"
#include "expr/node.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace CVC4::theory;

BoolToBV::BoolToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bool-to-bv"), d_statistics()
{
  d_boolToBVMode = options::boolToBitvector();
};

PreprocessingPassResult BoolToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  size_t size = assertionsToPreprocess->size();

  if (d_boolToBVMode == options::BoolToBVMode::ALL)
  {
    for (size_t i = 0; i < size; ++i)
    {
      Node newAssertion = lowerAssertion((*assertionsToPreprocess)[i], true);
      assertionsToPreprocess->replace(i, Rewriter::rewrite(newAssertion));
    }
  }
  else
  {
    Assert(d_boolToBVMode == options::BoolToBVMode::ITE);
    for (size_t i = 0; i < size; ++i)
    {
      assertionsToPreprocess->replace(
          i, Rewriter::rewrite(lowerIte((*assertionsToPreprocess)[i])));
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

void BoolToBV::updateCache(TNode n, TNode rebuilt)
{
  // check more likely case first
  if ((n.getKind() != kind::ITE) || !n[1].getType().isBitVector())
  {
    d_lowerCache[n] = rebuilt;
  }
  else
  {
    d_iteBVLowerCache[n] = rebuilt;
  }
}

Node BoolToBV::fromCache(TNode n) const
{
  // check more likely case first
  if (n.getKind() != kind::ITE)
  {
    if (d_lowerCache.find(n) != d_lowerCache.end())
    {
      return d_lowerCache.at(n);
    }
  }
  else
  {
    if (d_iteBVLowerCache.find(n) != d_iteBVLowerCache.end())
    {
      return d_iteBVLowerCache.at(n);
    }
  }
  return n;
}

inline bool BoolToBV::inCache(const Node& n) const
{
  return (ContainsKey(d_lowerCache, n) || ContainsKey(d_iteBVLowerCache, n));
}

bool BoolToBV::needToRebuild(TNode n) const
{
  // check if any children were rebuilt
  for (const Node& nn : n)
  {
    if (inCache(nn))
    {
      return true;
    }
  }
  return false;
}

Node BoolToBV::lowerAssertion(const TNode& assertion, bool allowIteIntroduction)
{
  // first try to lower all the children
  for (const Node& c : assertion)
  {
    lowerNode(c, allowIteIntroduction);
  }

  // now try lowering the assertion, but don't force it with an ITE (even in mode all)
  lowerNode(assertion, false);
  Node newAssertion = fromCache(assertion);
  TypeNode newAssertionType = newAssertion.getType();
  if (newAssertionType.isBitVector())
  {
    Assert(newAssertionType.getBitVectorSize() == 1);
    newAssertion = NodeManager::currentNM()->mkNode(
        kind::EQUAL, newAssertion, bv::utils::mkOne(1));
    newAssertionType = newAssertion.getType();
  }
  Assert(newAssertionType.isBoolean());
  return newAssertion;
}

Node BoolToBV::lowerNode(const TNode& node, bool allowIteIntroduction)
{
  std::vector<TNode> to_visit;
  to_visit.push_back(node);
  std::unordered_set<TNode, TNodeHashFunction> visited;

  while (!to_visit.empty())
  {
    TNode n = to_visit.back();
    to_visit.pop_back();

    Debug("bool-to-bv") << "BoolToBV::lowerNode: Post-order traversal with "
                        << n << " and visited = " << ContainsKey(visited, n)
                        << std::endl;

    // Mark as visited
    if (ContainsKey(visited, n))
    {
      visit(n, allowIteIntroduction);
    }
    else
    {
      visited.insert(n);
      to_visit.push_back(n);

      // insert children in reverse order so that they're processed in order
      //    important for rewriting which sorts by node id
      // NOTE: size_t is unsigned, so using underflow for termination condition
      size_t numChildren = n.getNumChildren();
      for (size_t i = numChildren - 1; i < numChildren; --i)
      {
        to_visit.push_back(n[i]);
      }
    }
  }

  return fromCache(node);
}

void BoolToBV::visit(const TNode& n, bool allowIteIntroduction)
{
  Kind k = n.getKind();

  // easy case -- just replace boolean constant
  if (k == kind::CONST_BOOLEAN)
  {
    updateCache(n,
                (n == bv::utils::mkTrue()) ? bv::utils::mkOne(1)
                                           : bv::utils::mkZero(1));
    return;
  }

  NodeManager* nm = NodeManager::currentNM();
  Kind new_kind = k;
  switch (k)
  {
    case kind::EQUAL: new_kind = kind::BITVECTOR_COMP; break;
    case kind::AND: new_kind = kind::BITVECTOR_AND; break;
    case kind::OR: new_kind = kind::BITVECTOR_OR; break;
    case kind::NOT: new_kind = kind::BITVECTOR_NOT; break;
    case kind::XOR: new_kind = kind::BITVECTOR_XOR; break;
    case kind::IMPLIES: new_kind = kind::BITVECTOR_OR; break;
    case kind::ITE: new_kind = kind::BITVECTOR_ITE; break;
    case kind::BITVECTOR_ULT: new_kind = kind::BITVECTOR_ULTBV; break;
    case kind::BITVECTOR_SLT: new_kind = kind::BITVECTOR_SLTBV; break;
    case kind::BITVECTOR_ULE:
    case kind::BITVECTOR_UGT:
    case kind::BITVECTOR_UGE:
    case kind::BITVECTOR_SLE:
    case kind::BITVECTOR_SGT:
    case kind::BITVECTOR_SGE:
      // Should have been removed by rewriting.
      Unreachable();
    default: break;
  }

  // check if it's safe to lower or rebuild the node
  // Note: might have to rebuild to keep changes to children, even if this node
  // isn't being lowered

  // it's safe to lower if all the children are bit-vectors
  bool safe_to_lower =
      (new_kind != k);  // don't need to lower at all if kind hasn't changed

  // it's safe to rebuild if rebuilding doesn't change any of the types of the
  // children
  bool safe_to_rebuild = true;

  for (const Node& nn : n)
  {
    safe_to_lower = safe_to_lower && fromCache(nn).getType().isBitVector();
    safe_to_rebuild = safe_to_rebuild && (fromCache(nn).getType() == nn.getType());

    // if it's already not safe to do either, stop checking
    if (!safe_to_lower && !safe_to_rebuild)
    {
      break;
    }
  }

  Debug("bool-to-bv") << "safe_to_lower = " << safe_to_lower
                      << ", safe_to_rebuild = " << safe_to_rebuild << std::endl;

  if (new_kind != k && safe_to_lower)
  {
    // lower to BV
    rebuildNode(n, new_kind);
    return;
  }
  else if (new_kind != k && allowIteIntroduction && fromCache(n).getType().isBoolean())
  {
    // lower to BV using an ITE

    if (safe_to_rebuild && needToRebuild(n))
    {
      // need to rebuild to keep changes made to descendants
      rebuildNode(n, k);
    }

    updateCache(n,
                nm->mkNode(kind::ITE,
                           fromCache(n),
                           bv::utils::mkOne(1),
                           bv::utils::mkZero(1)));
    Debug("bool-to-bv") << "BoolToBV::visit forcing " << n
                        << " =>\n"
                        << fromCache(n) << std::endl;
    ++(d_statistics.d_numIntroducedItes);
    return;
  }
  else if (safe_to_rebuild && needToRebuild(n))
  {
    // rebuild to incorporate changes to children
    Assert(k == new_kind);
    rebuildNode(n, k);
  }
  else if (allowIteIntroduction && fromCache(n).getType().isBoolean())
  {
    // force booleans (which haven't already been converted) to bit-vector
    // needed to maintain the invariant that all boolean children
    // have been converted (even constants and variables) when forcing
    // with ITE introductions
    updateCache(
        n, nm->mkNode(kind::ITE, n, bv::utils::mkOne(1), bv::utils::mkZero(1)));
    Debug("bool-to-bv") << "BoolToBV::visit forcing " << n
                        << " =>\n"
                        << fromCache(n) << std::endl;
    ++(d_statistics.d_numIntroducedItes);
  }
  else
  {
    // do nothing
    Debug("bool-to-bv") << "BoolToBV::visit skipping: " << n
                        << std::endl;
  }
}

Node BoolToBV::lowerIte(const TNode& node)
{
  std::vector<TNode> visit;
  visit.push_back(node);
  std::unordered_set<TNode, TNodeHashFunction> visited;

  while (!visit.empty())
  {
    TNode n = visit.back();
    visit.pop_back();

    Debug("bool-to-bv") << "BoolToBV::lowerIte: Post-order traversal with " << n
                        << " and visited = " << ContainsKey(visited, n)
                        << std::endl;

    // Look for ITEs and mark visited
    if (!ContainsKey(visited, n))
    {
      if ((n.getKind() == kind::ITE) && n[1].getType().isBitVector())
      {
        Debug("bool-to-bv") << "BoolToBV::lowerIte: adding " << n[0]
                            << " to set of ite conditions" << std::endl;
        // don't force in this case -- forcing only introduces more ITEs
        Node loweredNode = lowerNode(n, false);
        // some of the lowered nodes might appear elsewhere but not in an ITE
        // reset the cache to prevent lowering them
        // the bit-vector ITEs are still tracked in d_iteBVLowerCache though
        d_lowerCache.clear();
      }
      else
      {
        visit.push_back(n);
        visited.insert(n);
        // insert in reverse order so that they're processed in order
        for (int i = n.getNumChildren() - 1; i >= 0; --i)
        {
          visit.push_back(n[i]);
        }
      }
    }
    else if (needToRebuild(n))
    {
      // Note: it's always safe to rebuild here, because we've only lowered
      //       ITEs of type bit-vector to BITVECTOR_ITE
      rebuildNode(n, n.getKind());
    }
    else
    {
      Debug("bool-to-bv")
          << "BoolToBV::lowerIte Skipping because don't need to rebuild: " << n
          << std::endl;
    }
  }
  return fromCache(node);
}

void BoolToBV::rebuildNode(const TNode& n, Kind new_kind)
{
  Kind k = n.getKind();
  NodeManager* nm = NodeManager::currentNM();
  NodeBuilder<> builder(new_kind);

  Debug("bool-to-bv") << "BoolToBV::rebuildNode with " << n
                      << " and new_kind = " << kindToString(new_kind)
                      << std::endl;

  if ((d_boolToBVMode == options::BoolToBVMode::ALL) && (new_kind != k))
  {
    ++(d_statistics.d_numTermsLowered);
  }

  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << n.getOperator();
  }

  // special case IMPLIES because needs to be rewritten
  if ((k == kind::IMPLIES) && (new_kind != k))
  {
    builder << nm->mkNode(kind::BITVECTOR_NOT, fromCache(n[0]));
    builder << fromCache(n[1]);
  }
  else
  {
    for (const Node& nn : n)
    {
      builder << fromCache(nn);
    }
  }

  Debug("bool-to-bv") << "BoolToBV::rebuildNode " << n << " =>\n"
                      << builder << std::endl;

  updateCache(n, builder.constructNode());
}

BoolToBV::Statistics::Statistics()
    : d_numIteToBvite("preprocessing::passes::BoolToBV::NumIteToBvite", 0),
      d_numTermsLowered("preprocessing::passes:BoolToBV::NumTermsLowered", 0),
      d_numIntroducedItes(
          "preprocessing::passes::BoolToBV::NumTermsForcedLowered", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numIteToBvite);
  if (options::boolToBitvector() == options::BoolToBVMode::ALL)
  {
    // these statistics wouldn't be correct in the ITE mode,
    // because it might discard rebuilt nodes if it fails to
    // convert a bool to width-one bit-vector (never forces)
    smtStatisticsRegistry()->registerStat(&d_numTermsLowered);
    smtStatisticsRegistry()->registerStat(&d_numIntroducedItes);
  }
}

BoolToBV::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numIteToBvite);
  if (options::boolToBitvector() == options::BoolToBVMode::ALL)
  {
    smtStatisticsRegistry()->unregisterStat(&d_numTermsLowered);
    smtStatisticsRegistry()->unregisterStat(&d_numIntroducedItes);
  }
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
