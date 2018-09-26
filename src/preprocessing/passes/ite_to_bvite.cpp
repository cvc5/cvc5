/*********************                                                        */
/*! \file ite_to_bvite.cpp
** \verbatim
** Top contributors (to current version):
**   Makai Mann
** This file is part of the CVC4 project.
** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file COPYING in the top-level source
** directory for licensing information.\endverbatim
**
** \brief The IteToBvite preprocessing pass. Converts ITEs to BITVECTOR_ITEs
**         when it's convenient to do so, as implemented by easyToLower
**
**/

#include "preprocessing/passes/ite_to_bvite.h"

#include <string>

#include "expr/node.h"
#include "smt/smt_statistics_registry.h"
#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {
using namespace CVC4::theory;

IteToBvite::IteToBvite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-to-bvite"), d_statistics(){};

PreprocessingPassResult IteToBvite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager::currentResourceManager()->spendResource(
      options::preprocessStep());

  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(i,
        Rewriter::rewrite(lowerAssertion(assertionsToPreprocess->operator[](i))));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node IteToBvite::fromCache(TNode n)
{
  if (d_lowerCache.find(n) != d_lowerCache.end())
    {
      return d_lowerCache.find(n)->second;
    }
  return n;
}

bool IteToBvite::needToRebuild(TNode n)
{
  // check if any children were rebuilt
  for (const Node& nn : n)
    {
      if (d_lowerCache.count(nn))
        {
          return true;
        }
    }
  return false;
}

Node IteToBvite::lowerAssertion(TNode a)
{
  bool optionITE = true;
  NodeManager* nm = NodeManager::currentNM();
  std::vector<TNode> terms;
  terms.push_back(a);
  std::unordered_set<TNode, TNodeHashFunction> visited;
  // for optionITE, keeps track of whether you're in an ite condition
  std::unordered_set<TNode, TNodeHashFunction> ite_cond;
  // TODO: Refactor this a bit
  while(!terms.empty())
  {
    TNode n = terms.back();
    terms.pop_back();
    Kind k = n.getKind();
    Debug("ite-to-bvite") << "IteToBvite Post-traversal with " << n
                          << " and visited = " << visited.count(n) << std::endl;

    // TODO: Optimization: if it's a leaf, then don't need to wait for visited=1 to do the work

    if (visited.count(n) == 0)
    {
      visited.insert(n);
      terms.push_back(n);
      for (const Node& nn : n)
      {
        terms.push_back(nn);
      }

      // check for ite-conditions
      if (k == kind::ITE)
      {
        ite_cond.insert(n[0]);
      }
      else if (ite_cond.count(n)) {
        // being part of an ite condition is inherited from the parent
        for (const Node& nn : n)
        {
          ite_cond.insert(nn);
        }
      }
    }
    else if (optionITE && (ite_cond.count(n) == 0) && !needToRebuild(n))
    {
      Debug("ite-to-bvite") << "Skipping because don't need to rebuild: " << n << std::endl;
      // in ite mode, if you've already visited the node but it's not
      // in an ite condition and doesn't need to be rebuilt, then
      // don't need to do anything
      continue;
    }
    else
    {
      TypeNode t = n.getType();
      if ((t.isBitVector() || t.isBoolean()) && (n.getNumChildren() == 0))
      {
        if (!optionITE && (k == kind::CONST_BOOLEAN))
        {
          d_lowerCache[n] = nm->mkNode(kind::ITE, n, bv::utils::mkOne(1), bv::utils::mkZero(1));
          ++(d_statistics.d_numTermsForcedLowered);
        }
        // if it's already a bit-vector with no children, we don't need to do anything
        // for option=ite, give up instead of forcing a bool to be a bit-vector
        Debug("ite-to-bvite") << "Skipping because no children: " << n << std::endl;
      }
      else
      {
          AlwaysAssert(n.getNumChildren() > 0);

          bool all_bv = true;
          // check if it was able to convert all children to bitvectors
          for (const Node& nn : n)
            {
              all_bv = all_bv && fromCache(nn).getType().isBitVector();
            }

          if (all_bv)
            {
              Kind k = n.getKind();
              Kind new_kind = k;
              switch(k)
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

              Debug("ite-to-bvite") << "IteToBvite: Processing " << n
                                    << " with new_kind = " << new_kind
                                    << std::endl;

              NodeBuilder<> builder(new_kind);
              if (!optionITE && (new_kind != k))
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
                  for (const Node &nn : n)
                    {
                      builder << fromCache(nn);
                    }
                }

              d_lowerCache[n] = builder;
            }
      }
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

IteToBvite::Statistics::Statistics()
  : d_numIteToBvite("preprocessing::passes::IteToBvite::NumIteToBvite", 0),
    d_numTermsLowered("preprocessing::passes:IteToBvite::NumTermsLowered", 0),
    d_numTermsForcedLowered("preprocessing::passes::IteToBvite::NumTermsForcedLowered", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numIteToBvite);
  // TODO: only register/unregister these if option=all
  smtStatisticsRegistry()->registerStat(&d_numTermsLowered);
  smtStatisticsRegistry()->registerStat(&d_numTermsForcedLowered);
}

IteToBvite::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&d_numIteToBvite);
  smtStatisticsRegistry()->unregisterStat(&d_numTermsLowered);
  smtStatisticsRegistry()->unregisterStat(&d_numTermsForcedLowered);

}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
