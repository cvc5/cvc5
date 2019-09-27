/*********************                                                        */
/*! \file apply_to_const.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The ApplyToConst preprocessing pass
 **
 ** Rewrites applies to constants
 **/

#include "preprocessing/passes/apply_to_const.h"

#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

ApplyToConst::ApplyToConst(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "apply-to-const"){};

Node ApplyToConst::rewriteApplyToConst(TNode n, NodeMap& cache)
{
  Trace("rewriteApplyToConst") << "rewriteApplyToConst :: " << n << std::endl;

  if (n.getMetaKind() == kind::metakind::CONSTANT
      || n.getMetaKind() == kind::metakind::VARIABLE
      || n.getMetaKind() == kind::metakind::NULLARY_OPERATOR)
  {
    return n;
  }

  if (cache.find(n) != cache.end())
  {
    Trace("rewriteApplyToConst") << "in cache :: " << cache[n] << std::endl;
    return cache[n];
  }

  if (n.getKind() == kind::APPLY_UF)
  {
    if (n.getNumChildren() == 1 && n[0].isConst() && n[0].getType().isInteger())
    {
      stringstream ss;
      ss << n.getOperator() << "_";
      if (n[0].getConst<Rational>() < 0)
      {
        ss << "m" << -n[0].getConst<Rational>();
      }
      else
      {
        ss << n[0];
      }
      Node newvar =
          NodeManager::currentNM()->mkSkolem(ss.str(),
                                             n.getType(),
                                             "rewriteApplyToConst skolem",
                                             NodeManager::SKOLEM_EXACT_NAME);
      cache[n] = newvar;
      Trace("rewriteApplyToConst") << "made :: " << newvar << std::endl;
      return newvar;
    }
    stringstream ss;
    ss << "The rewrite-apply-to-const preprocessor is currently limited;\n"
       << "it only works if all function symbols are unary and with Integer\n"
       << "domain, and all applications are to integer values.\n"
       << "Found application: " << n;
    Unhandled(ss.str());
  }

  NodeBuilder<> builder(n.getKind());
  if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    builder << n.getOperator();
  }
  for (unsigned i = 0; i < n.getNumChildren(); ++i)
  {
    builder << rewriteApplyToConst(n[i], cache);
  }
  Node rewr = builder;
  cache[n] = rewr;
  Trace("rewriteApplyToConst") << "built :: " << rewr << std::endl;
  return rewr;
}

PreprocessingPassResult ApplyToConst::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeMap cache;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i,
                                    Rewriter::rewrite(rewriteApplyToConst(
                                        (*assertionsToPreprocess)[i], cache)));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
