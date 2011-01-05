/*
 * theory_bv_rewriter.cpp
 *
 *  Created on: Dec 21, 2010
 *      Author: dejan
 */

#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

RewriteResponse TheoryBVRewriter::postRewrite(TNode node) {

  Debug("bitvector") << "TheoryBV::postRewrite(" << node << ")" << std::endl;

  Node result;

  if (node.getKind() == kind::CONST_BITVECTOR /* || isLeaf(n)) */)
    result = node;
  else {
    switch (node.getKind()) {
    case kind::BITVECTOR_CONCAT:
      result = LinearRewriteStrategy<
                  // Flatten the top level concatenations
                  CoreRewriteRules::ConcatFlatten,
                  // Merge the adjacent extracts on non-constants
                  CoreRewriteRules::ConcatExtractMerge,
                  // Merge the adjacent extracts on constants
                  CoreRewriteRules::ConcatConstantMerge,
                  // At this point only Extract-Whole could apply, if the result is only one extract
                  // or at some sub-expression if the result is a concatenation.
                  ApplyRuleToChildren<kind::BITVECTOR_CONCAT, CoreRewriteRules::ExtractWhole>
               >::apply(node);
      break;
    case kind::BITVECTOR_EXTRACT:
      result = LinearRewriteStrategy<
                  // Extract over a constant gives a constant
                  CoreRewriteRules::ExtractConstant,
                  // Extract over an extract is simplified to one extract
                  CoreRewriteRules::ExtractExtract,
                  // Extract over a concatenation is distributed to the appropriate concatenations
                  CoreRewriteRules::ExtractConcat,
                  // At this point only Extract-Whole could apply
                  CoreRewriteRules::ExtractWhole
                >::apply(node);
      break;
    case kind::EQUAL:
      result = LinearRewriteStrategy<
                  // Two distinct values rewrite to false
                  CoreRewriteRules::FailEq,
                  // If both sides are equal equality is true
                  CoreRewriteRules::SimplifyEq
                >::apply(node);
      break;
    default:
      // TODO: figure out when this is an operator
      result = node;
      break;
      // Unhandled();
    }
  }

  Debug("bitvector") << "TheoryBV::postRewrite(" << node << ") => " << result << std::endl;

  return RewriteResponse(REWRITE_DONE, result);
}

