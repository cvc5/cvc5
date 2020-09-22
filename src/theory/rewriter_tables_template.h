/*********************                                                        */
/*! \file rewriter_tables_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter tables for various theories
 **
 ** This file contains template code for the rewriter tables that are generated
 ** from the Theory kinds files.
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/rewriter.h"
#include "theory/rewriter_attributes.h"
#include "expr/attribute_unique_id.h"
#include "expr/attribute.h"

${rewriter_includes}

namespace CVC4 {
namespace theory {

Node Rewriter::getPreRewriteCache(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${pre_rewrite_get_cache}
  default:
    Unreachable();
  }
}

Node Rewriter::getPostRewriteCache(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${post_rewrite_get_cache}
    default:
    Unreachable();
  }
}

void Rewriter::setPreRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache) {
  switch(theoryId) {
${pre_rewrite_set_cache}
  default:
    Unreachable();
  }
}

void Rewriter::setPostRewriteCache(theory::TheoryId theoryId, TNode node, TNode cache) {
  switch(theoryId) {
${post_rewrite_set_cache}
  default:
    Unreachable();
  }
}

Rewriter::Rewriter()
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

void Rewriter::clearCachesInternal() {
  typedef CVC4::expr::attr::AttributeUniqueId AttributeUniqueId;
  std::vector<AttributeUniqueId> preids;
  ${pre_rewrite_attribute_ids}

  std::vector<AttributeUniqueId> postids;
  ${post_rewrite_attribute_ids}

  std::vector<const AttributeUniqueId*> allids;
  for(unsigned i = 0; i < preids.size(); ++i){
    allids.push_back(&preids[i]);
  }
  for(unsigned i = 0; i < postids.size(); ++i){
    allids.push_back(&postids[i]);
  }
  NodeManager::currentNM()->deleteAttributes(allids);
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
