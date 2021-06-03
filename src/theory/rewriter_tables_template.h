/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriter tables for various theories.
 *
 * This file contains template code for the rewriter tables that are generated
 * from the Theory kinds files.
 */

#include "cvc5_private.h"

#pragma once

#include "expr/attribute.h"
#include "expr/attribute_unique_id.h"
#include "theory/rewriter.h"
#include "theory/rewriter_attributes.h"

// clang-format off
${rewriter_includes}
// clang-format on

namespace cvc5 {
namespace theory {

Node Rewriter::getPreRewriteCache(theory::TheoryId theoryId, TNode node)
{
  switch (theoryId)
  {
    // clang-format off
${pre_rewrite_get_cache}
      // clang-format on
    default: Unreachable();
  }
}

Node Rewriter::getPostRewriteCache(theory::TheoryId theoryId, TNode node)
{
  switch (theoryId)
  {
    // clang-format off
${post_rewrite_get_cache}
      // clang-format on
    default: Unreachable();
  }
}

void Rewriter::setPreRewriteCache(theory::TheoryId theoryId,
                                  TNode node,
                                  TNode cache)
{
  switch (theoryId)
  {
    // clang-format off
${pre_rewrite_set_cache}
      // clang-format on
    default: Unreachable();
  }
}

void Rewriter::setPostRewriteCache(theory::TheoryId theoryId,
                                   TNode node,
                                   TNode cache)
{
  switch (theoryId)
  {
    // clang-format off
${post_rewrite_set_cache}
      // clang-format on
    default: Unreachable();
  }
}

Rewriter::Rewriter() : d_tpg(nullptr)
{
  for (size_t i = 0; i < kind::LAST_KIND; ++i)
  {
    d_preRewriters[i] = nullptr;
    d_postRewriters[i] = nullptr;
  }

  for (size_t i = 0; i < theory::THEORY_LAST; ++i)
  {
    d_preRewritersEqual[i] = nullptr;
    d_postRewritersEqual[i] = nullptr;
  }
}

void Rewriter::clearCachesInternal()
{
  typedef cvc5::expr::attr::AttributeUniqueId AttributeUniqueId;
  std::vector<AttributeUniqueId> preids;
  // clang-format off
  ${pre_rewrite_attribute_ids}  // clang-format on

  std::vector<AttributeUniqueId>
      postids;
  // clang-format off
  ${post_rewrite_attribute_ids}  // clang-format on

  std::vector<const AttributeUniqueId*>
      allids;
  for (size_t i = 0, size = preids.size(); i < size; ++i)
  {
    allids.push_back(&preids[i]);
  }
  for (size_t i = 0, size = postids.size(); i < size; ++i)
  {
    allids.push_back(&postids[i]);
  }
  NodeManager::currentNM()->deleteAttributes(allids);
}

}  // namespace theory
}  // namespace cvc5
