/*********************                                                        */
/*! \file bool_to_bv.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann, Yoni Zohar, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include "options/bv_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace CVC4::theory;

BoolToBV::BoolToBV(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bool-to-bv"), d_statistics(){};

PreprocessingPassResult BoolToBV::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager::currentResourceManager()->spendResource(
      ResourceManager::Resource::PreprocessStep);

  unsigned size = assertionsToPreprocess->size();
  for (unsigned i = 0; i < size; ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(lowerAssertion((*assertionsToPreprocess)[i])));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node BoolToBV::fromCache(TNode n) const
{
  if (d_lowerCache.find(n) != d_lowerCache.end())
  {
    return d_lowerCache.find(n)->second;
  }
  return n;
}

bool BoolToBV::needToRebuild(TNode n) const
{
  // check if any children were rebuilt
  for (const Node& nn : n)
  {
    if (ContainsKey(d_lowerCache, nn))
    {
      return true;
    }
  }
  return false;
}

Node BoolToBV::lowerAssertion(const TNode& a)
{
  bool optionITE = options::boolToBitvector() == options::BoolToBVMode::ITE;
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TNode> visit;
  visit.push_back(a);
  std::unordered_set<TNode, TNodeHashFunction> visited;
  // for ite mode, keeps track of whether you're in an ite condition
  // for all mode, unused
  std::unordered_set<TNode, TNodeHashFunction> ite_cond;

  while (!visit.empty())
  {
    TNode n = visit.back();
    visit.pop_back();

    int numChildren = n.getNumChildren();
    Kind k = n.getKind();
    Debug("bool-to-bv") << "BoolToBV::lowerAssertion Post-traversal with " << n
                        << " and visited = " << ContainsKey(visited, n)
                        << std::endl;

    // Mark as visited
    /* Optimization: if it's a leaf, don't need to wait to do the work */
    if (!ContainsKey(visited, n) && (numChildren > 0))
    {
      visited.insert(n);
      visit.push_back(n);

      // insert children in reverse order so that they're processed in order
      //     important for rewriting which sorts by node id
      for (int i = numChildren - 1; i >= 0; --i)
      {
        visit.push_back(n[i]);
      }

      if (optionITE)
      {
        // check for ite-conditions
        if (k == kind::ITE)
        {
          ite_cond.insert(n[0]);
        }
        else if (ContainsKey(ite_cond, n))
        {
          // being part of an ite condition is inherited from the parent
          ite_cond.insert(n.begin(), n.end());
        }
      }
    }
    /* Optimization for ite mode */
    else if (optionITE && !ContainsKey(ite_cond, n) && !needToRebuild(n))
    {
      Debug("bool-to-bv")
          << "BoolToBV::lowerAssertion Skipping because don't need to rebuild: "
          << n << std::endl;
      // in ite mode, if you've already visited the node but it's not
      // in an ite condition and doesn't need to be rebuilt, then
      // don't need to do anything
      continue;
    }
    else
    {
      lowerNode(n);
    }
  }

  if (fromCache(a).getType().isBitVector())
  {
    return nm->mkNode(kind::EQUAL, fromCache(a), bv::utils::mkOne(1));
  }
  else
  {
    Assert(a == fromCache(a));
    return a;
  }
}

void BoolToBV::lowerNode(const TNode& n)
{
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n.getKind();

  bool all_bv = true;
  // check if it was able to convert all children to bitvectors
  for (const Node& nn : n)
  {
    all_bv = all_bv && fromCache(nn).getType().isBitVector();
    if (!all_bv)
    {
      break;
    }
  }

  if (!all_bv || (n.getNumChildren() == 0))
  {
    if ((options::boolToBitvector() == options::BoolToBVMode::ALL)
        && n.getType().isBoolean())
    {
      if (k == kind::CONST_BOOLEAN)
      {
        d_lowerCache[n] = (n == bv::utils::mkTrue()) ? bv::utils::mkOne(1)
                                                     : bv::utils::mkZero(1);
      }
      else
      {
        d_lowerCache[n] =
            nm->mkNode(kind::ITE, n, bv::utils::mkOne(1), bv::utils::mkZero(1));
      }

      Debug("bool-to-bv") << "BoolToBV::lowerNode " << n << " =>\n"
                          << fromCache(n) << std::endl;
      ++(d_statistics.d_numTermsForcedLowered);
      return;
    }
    else
    {
      // invariant
      // either one of the children is not a bit-vector or bool
      //   i.e. something that can't be 'forced' to a bitvector
      // or it's in 'ite' mode which will give up on bools that
      //   can't be converted easily

      Debug("bool-to-bv") << "BoolToBV::lowerNode skipping: " << n << std::endl;
      return;
    }
  }

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

  NodeBuilder<> builder(new_kind);
  if ((options::boolToBitvector() == options::BoolToBVMode::ALL)
      && (new_kind != k))
  {
    ++(d_statistics.d_numTermsLowered);
  }

  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << n.getOperator();
  }

  // special case IMPLIES because needs to be rewritten
  if (k == kind::IMPLIES)
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

  Debug("bool-to-bv") << "BoolToBV::lowerNode " << n << " =>\n"
                      << builder << std::endl;

  d_lowerCache[n] = builder.constructNode();
}

BoolToBV::Statistics::Statistics()
    : d_numIteToBvite("preprocessing::passes::BoolToBV::NumIteToBvite", 0),
      d_numTermsLowered("preprocessing::passes:BoolToBV::NumTermsLowered", 0),
      d_numTermsForcedLowered(
          "preprocessing::passes::BoolToBV::NumTermsForcedLowered", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numIteToBvite);
  if (options::boolToBitvector() == options::BoolToBVMode::ALL)
  {
    // these statistics wouldn't be correct in the ITE mode,
    // because it might discard rebuilt nodes if it fails to
    // convert a bool to width-one bit-vector (never forces)
    smtStatisticsRegistry()->registerStat(&d_numTermsLowered);
    smtStatisticsRegistry()->registerStat(&d_numTermsForcedLowered);
  }
}

BoolToBV::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numIteToBvite);
  if (options::boolToBitvector() == options::BoolToBVMode::ALL)
  {
    smtStatisticsRegistry()->unregisterStat(&d_numTermsLowered);
    smtStatisticsRegistry()->unregisterStat(&d_numTermsForcedLowered);
  }
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
