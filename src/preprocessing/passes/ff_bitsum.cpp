/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * parse ff bitsums
 */

#include "preprocessing/passes/ff_bitsum.h"

// external includes

// std includes
#include <unordered_set>

// internal includes
#include "expr/algorithm/flatten.h"
#include "expr/node_traversal.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

FfBitsum::FfBitsum(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ff-bitsum")
{
}

Node mkAdd(NodeManager* nm, const std::vector<Node>& children)
{
  Assert(children.size() > 0);
  return children.size() == 1 ? children[0]
                              : nm->mkNode(Kind::FINITE_FIELD_ADD, children);
}

PreprocessingPassResult FfBitsum::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  // collect bits
  std::unordered_set<Node> bits;
  for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    std::vector<TNode> anded{};
    TNode assertion = (*assertionsToPreprocess)[i];
    expr::algorithm::flatten(assertion, anded, Kind::AND);
    for (const auto& fact : anded)
    {
      if (fact.getKind() == Kind::EQUAL && fact[0].getType().isFiniteField())
      {
        auto bitOpt = theory::ff::parse::bitConstraint(fact);
        if (bitOpt.has_value())
        {
          bits.insert(*bitOpt);
        }
      }
    }
  }

  // collect bitsums
  auto nm = nodeManager();
  std::unordered_map<Node, Node> cache{};
  for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Node fact = (*assertionsToPreprocess)[i];
    for (TNode current :
         NodeDfsIterable(fact, VisitOrder::POSTORDER, [&cache](TNode nn) {
           return cache.count(nn);
         }))
    {
      Node translation;
      Assert(!cache.count(current));
      if (current.getNumChildren() == 0)
      {
        translation = current;
      }
      else
      {
        Kind oldKind = current.getKind();
        NodeBuilder builder(nm, oldKind);
        if (current.getMetaKind() == kind::MetaKind::PARAMETERIZED)
        {
          builder << current.getOperator();
        }
        for (TNode c : current)
        {
          builder << cache.at(c);
        }
        translation = builder;
        if (translation.getKind() == Kind::FINITE_FIELD_ADD)
        {
          auto bs = theory::ff::parse::bitSums(translation, bits);
          if (bs.has_value() && bs->first.size() > 0)
          {
            for (const auto& [multiplier, bitSeq] : bs->first)
            {
              Assert(bitSeq.size() > 1);
              Node bitsum = nm->mkNode(Kind::FINITE_FIELD_BITSUM, bitSeq);
              Node scaled = multiplier.isOne()
                                ? bitsum
                                : nm->mkNode(Kind::FINITE_FIELD_MULT,
                                             nm->mkConst(multiplier),
                                             bitsum);
              Trace("ff::bitsum") << "found " << scaled << std::endl;
              bs->second.push_back(scaled);
            }
            translation = mkAdd(nm, std::move(bs->second));
          }
        }
      }
      cache[current] = translation;
    }
    Node newFact = cache[fact];
    if (newFact != fact)
    {
      assertionsToPreprocess->replace(
          i, newFact, nullptr, TrustId::PREPROCESS_FF_BITSUM);
    }
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
