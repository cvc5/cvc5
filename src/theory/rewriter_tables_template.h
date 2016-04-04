/*********************                                                        */
/*! \file rewriter_tables_template.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

RewriteResponse Rewriter::callPreRewrite(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${pre_rewrite_calls}
  default:
    Unreachable();
  }
}

RewriteResponse Rewriter::callPostRewrite(theory::TheoryId theoryId, TNode node) {
  switch(theoryId) {
${post_rewrite_calls}
  default:
    Unreachable();
  }
}

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

void Rewriter::init() {
${rewrite_init}
}

void Rewriter::shutdown() {
${rewrite_shutdown}
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
