#include "theory_bv.h"
#include "theory_bv_utils.h"
#include "theory_bv_rewrite_rules.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

RewriteResponse TheoryBV::postRewrite(TNode node, bool topLevel) {

  Debug("bitvector") << "postRewrite(" << node << ", topLevel = " << (topLevel? "true" : "false") << ")" << std::endl;

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
      if (node[0] == node[1]) result = mkTrue();
      else result = node;
      break;
    default:
      // TODO: figure out when this is an operator
      result = node;
      break;
      // Unhandled();
    }
  }

  Debug("bitvector") << "postRewrite(" << node << ", topLevel = " << (topLevel? "true" : "false") << ") => " << result << std::endl;

  return RewriteComplete(result);
}
