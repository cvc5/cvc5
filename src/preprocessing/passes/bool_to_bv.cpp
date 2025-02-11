/******************************************************************************
 * Top contributors (to current version):
 *   Makai Mann, Yoni Zohar, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BoolToBV preprocessing pass.
 *
 */

#include "preprocessing/passes/bool_to_bv.h"

#include <string>

#include "base/map_util.h"
#include "expr/node.h"
#include "options/bv_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {
using namespace cvc5::internal::theory;

BoolToBV::BoolToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bool-to-bv"),
      d_statistics(statisticsRegistry())
{
  d_boolToBVMode = options().bv.boolToBitvector;
};

PreprocessingPassResult BoolToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  size_t size = assertionsToPreprocess->size();
  Assert(d_boolToBVMode == options::BoolToBVMode::ALL
         || d_boolToBVMode == options::BoolToBVMode::ITE);
  for (size_t i = 0; i < size; ++i)
  {
    Node newAssertion;
    if (d_boolToBVMode == options::BoolToBVMode::ALL)
    {
      newAssertion = lowerAssertion((*assertionsToPreprocess)[i], true);
    }
    else
    {
      newAssertion = lowerIte((*assertionsToPreprocess)[i]);
    }
    assertionsToPreprocess->replace(
        i, newAssertion, nullptr, TrustId::PREPROCESS_BOOL_TO_BV);
    assertionsToPreprocess->ensureRewritten(i);
    if (assertionsToPreprocess->isInConflict())
    {
      return PreprocessingPassResult::CONFLICT;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

void BoolToBV::updateCache(TNode n, TNode rebuilt)
{
  // check more likely case first
  if ((n.getKind() != Kind::ITE) || !n[1].getType().isBitVector())
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
  if (n.getKind() != Kind::ITE)
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
    NodeManager* nm = nodeManager();
    newAssertion =
        nm->mkNode(Kind::EQUAL, newAssertion, bv::utils::mkOne(nm, 1));
    newAssertionType = newAssertion.getType();
  }
  Assert(newAssertionType.isBoolean());
  return newAssertion;
}

Node BoolToBV::lowerNode(const TNode& node, bool allowIteIntroduction)
{
  std::vector<TNode> to_visit;
  to_visit.push_back(node);
  std::unordered_set<TNode> visited;

  while (!to_visit.empty())
  {
    TNode n = to_visit.back();
    to_visit.pop_back();

    Trace("bool-to-bv") << "BoolToBV::lowerNode: Post-order traversal with "
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

  NodeManager* nm = nodeManager();
  // easy case -- just replace boolean constant
  if (k == Kind::CONST_BOOLEAN)
  {
    updateCache(n,
                (n == bv::utils::mkTrue(nm)) ? bv::utils::mkOne(nm, 1)
                                             : bv::utils::mkZero(nm, 1));
    return;
  }

  Kind new_kind = k;
  switch (k)
  {
    case Kind::EQUAL: new_kind = Kind::BITVECTOR_COMP; break;
    case Kind::AND: new_kind = Kind::BITVECTOR_AND; break;
    case Kind::OR: new_kind = Kind::BITVECTOR_OR; break;
    case Kind::NOT: new_kind = Kind::BITVECTOR_NOT; break;
    case Kind::XOR: new_kind = Kind::BITVECTOR_XOR; break;
    case Kind::IMPLIES: new_kind = Kind::BITVECTOR_OR; break;
    case Kind::ITE: new_kind = Kind::BITVECTOR_ITE; break;
    case Kind::BITVECTOR_ULT: new_kind = Kind::BITVECTOR_ULTBV; break;
    case Kind::BITVECTOR_SLT: new_kind = Kind::BITVECTOR_SLTBV; break;
    case Kind::BITVECTOR_ULE:
    case Kind::BITVECTOR_UGT:
    case Kind::BITVECTOR_UGE:
    case Kind::BITVECTOR_SLE:
    case Kind::BITVECTOR_SGT:
    case Kind::BITVECTOR_SGE:
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
  Trace("bool-to-bv") << "safe_to_lower = " << safe_to_lower
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
                nm->mkNode(Kind::ITE,
                           fromCache(n),
                           bv::utils::mkOne(nm, 1),
                           bv::utils::mkZero(nm, 1)));
    Trace("bool-to-bv") << "BoolToBV::visit forcing " << n
                        << " =>\n"
                        << fromCache(n) << std::endl;
    if (d_boolToBVMode == options::BoolToBVMode::ALL)
    {
      // this statistic only makes sense for ALL mode
      ++(d_statistics.d_numIntroducedItes);
    }
    return;
  }
  else if (safe_to_rebuild && needToRebuild(n))
  {
    // rebuild to incorporate changes to children
    rebuildNode(n, k);
  }
  else if (allowIteIntroduction && fromCache(n).getType().isBoolean())
  {
    // force booleans (which haven't already been converted) to bit-vector
    // needed to maintain the invariant that all boolean children
    // have been converted (even constants and variables) when forcing
    // with ITE introductions
    updateCache(
        n,
        nm->mkNode(
            Kind::ITE, n, bv::utils::mkOne(nm, 1), bv::utils::mkZero(nm, 1)));
    Trace("bool-to-bv") << "BoolToBV::visit forcing " << n
                        << " =>\n"
                        << fromCache(n) << std::endl;
    if (d_boolToBVMode == options::BoolToBVMode::ALL)
    {
      // this statistic only makes sense for ALL mode
      ++(d_statistics.d_numIntroducedItes);
    }
  }
  else
  {
    // do nothing
    Trace("bool-to-bv") << "BoolToBV::visit skipping: " << n
                        << std::endl;
  }
}

Node BoolToBV::lowerIte(const TNode& node)
{
  std::vector<TNode> visit;
  visit.push_back(node);
  std::unordered_set<TNode> visited;

  while (!visit.empty())
  {
    TNode n = visit.back();
    visit.pop_back();

    Trace("bool-to-bv") << "BoolToBV::lowerIte: Post-order traversal with " << n
                        << " and visited = " << ContainsKey(visited, n)
                        << std::endl;

    // Look for ITEs and mark visited
    if (!ContainsKey(visited, n))
    {
      if ((n.getKind() == Kind::ITE) && n[1].getType().isBitVector())
      {
        Trace("bool-to-bv") << "BoolToBV::lowerIte: adding " << n[0]
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
      Trace("bool-to-bv")
          << "BoolToBV::lowerIte Skipping because don't need to rebuild: " << n
          << std::endl;
    }
  }
  return fromCache(node);
}

void BoolToBV::rebuildNode(const TNode& n, Kind new_kind)
{
  Kind k = n.getKind();
  NodeManager* nm = nodeManager();
  NodeBuilder builder(nm, new_kind);

  Trace("bool-to-bv") << "BoolToBV::rebuildNode with " << n
                      << " and new_kind = " << kindToString(new_kind)
                      << std::endl;

  if ((d_boolToBVMode == options::BoolToBVMode::ALL) && (new_kind != k))
  {
    // this statistic only makes sense for ALL mode
    ++(d_statistics.d_numTermsLowered);
  }

  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << n.getOperator();
  }
  // special case IMPLIES because needs to be rewritten
  if ((k == Kind::IMPLIES) && (new_kind != k))
  {
    builder << nm->mkNode(Kind::BITVECTOR_NOT, fromCache(n[0]));
    builder << fromCache(n[1]);
  }
  else
  {
    for (const Node& nn : n)
    {
      builder << fromCache(nn);
    }
  }

  Trace("bool-to-bv") << "BoolToBV::rebuildNode " << n << " =>\n"
                      << builder << std::endl;

  updateCache(n, builder.constructNode());
}

BoolToBV::Statistics::Statistics(StatisticsRegistry& reg)
    : d_numIteToBvite(
        reg.registerInt("preprocessing::passes::BoolToBV::NumIteToBvite")),
      // the following two statistics are not correct in the ITE mode, because
      // we might discard rebuilt nodes if we fails to convert a bool to
      // width-one bit-vector (never forces)
      d_numTermsLowered(
          reg.registerInt("preprocessing::passes:BoolToBV::NumTermsLowered")),
      d_numIntroducedItes(reg.registerInt(
          "preprocessing::passes::BoolToBV::NumTermsForcedLowered"))
{
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
