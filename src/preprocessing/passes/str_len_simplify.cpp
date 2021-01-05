/*********************                                                        */
/*! \file str_len_simplify.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The str_len_simplify preprocessing pass
 **
 ** Simplifies Arithmetic nodes by calling 
 ** CVC4::theory::strings::ArithEntail::check
 ** on each GEQ node.
 **/

#include "preprocessing/passes/str_len_simplify.h"

#include "expr/node_traversal.h"
#include "theory/strings/arith_entail.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;


StrLenSimplify::StrLenSimplify(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "str-len-simplify"), d_cache(preprocContext->getUserContext()){};


Node StrLenSimplify::simplify(Node n) 
{
  n = Rewriter::rewrite(n);
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER, [this](TNode tn) {return d_cache.find(tn) != d_cache.end();} )) {
    if (current.getKind() == kind::GEQ) {
      Assert(d_cache.find(current[0]) != d_cache.end());
      Assert(d_cache.find(current[1]) != d_cache.end());
      Trace("str-len-simplify") << "current: " << current << std::endl;
      bool b = theory::strings::ArithEntail::check(d_cache[current[0]], d_cache[current[1]], false);
      Trace("str-len-simplify") << "check result: " << b << std::endl;
      if (b) {
            d_cache[current] = NodeManager::currentNM()->mkConst<bool>(true);
      } else {
        d_cache[current] = current;
        }
    } else {
        if (current.getNumChildren() == 0) {
          d_cache[current] = current;
        } else {
          NodeBuilder<> builder(current.getKind());
          if (current.getMetaKind() == kind::metakind::PARAMETERIZED)    {
            builder << current.getOperator();
          }
          for (size_t i = 0; i < current.getNumChildren(); i++) {
            Assert(d_cache.find(current[i]) != d_cache.end());
            builder << d_cache[current[i]].get();
          }
          Node result = builder.constructNode();
          d_cache[current] = result;
        }
      }
  }
  if (d_cache.find(n) == d_cache.end()) {
    Assert(false);
  } else {
    return d_cache[n];
  }
}

PreprocessingPassResult StrLenSimplify::applyInternal(
  AssertionPipeline* assertionsToPreprocess)
{
  Trace("str-len-simplify") << "apply internal of StrLenSimplify" << std::endl;
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i) {
    assertionsToPreprocess->replace(i, Rewriter::rewrite(simplify((*assertionsToPreprocess)[i])));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
