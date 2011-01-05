#pragma once

#include "theory/rewriter.h"
#include "theory/rewriter_attributes.h"

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

}
}
