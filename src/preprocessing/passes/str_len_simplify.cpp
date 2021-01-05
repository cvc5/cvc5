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
  for (TNode current : NodeDfsIterable(n, VisitOrder::POSTORDER, [this](TNode tn) {std::cout << "panda kind: " << tn.getKind() << std::endl; bool b = d_cache.find(tn) != d_cache.end() || tn.getKind() != kind::GEQ; cout << "panda b: " << b << std::endl; return b;})) {
    kind::Kind_t k = current.getKind();
      Trace("str-len-simplify") << "kind: " << k << std::endl;
      if (k == kind::GEQ) {
        if (theory::strings::ArithEntail::check(current[0], current[1],false)) {
          d_cache[current] = NodeManager::currentNM()->mkConst<bool>(true);
        }
      }
  }
  if (d_cache.find(n) == d_cache.end()) {
    return n;
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
