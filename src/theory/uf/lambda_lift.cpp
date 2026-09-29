/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/node_algorithm.h"
#include "expr/sort_type_size.h"
#include "theory/uf/function_const.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

LambdaLift::LambdaLift(Env& env) : EnvObj(env) {}

bool LambdaLift::needsLift(const Node& lam)
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::map<Node, bool>::iterator it = d_needsLift.find(lam);
  if (it != d_needsLift.end())
  {
    return it->second;
  }
  // Model construction considers types in order of their type size
  // (SortTypeSize::getTypeSize). If the lambda has a free variable, that
  // comes later in the model construction, it may need to be lifted.
  // As an example, say f : Int -> Int, g : Int x Int -> Int
  // The following lambdas require lifting:
  // - (lambda ((x Int)) (g x x))
  // - (lambda ((x Int) (y Int)) (f (g x y)))
  // The following lambdas do not require lifting:
  // - (lambda ((x Int)) (+ x 1)), since it has no free symbols.
  // - (lambda ((x Int) (y Int)) (f x)), since its free symbol f has a type
  // Int -> Int which is processed before the type of the lambda, i.e.
  // Int x Int -> Int.
  // Note that we only lift lambdas that furthermore impact model
  // construction, which is only the case if the lambda is equated to an
  // ordinary function symbol.
  bool shouldLift = false;
  std::unordered_set<Node> syms;
  expr::getSymbols(lam[1], syms);
  SortTypeSize sts;
  size_t lsize = sts.getTypeSize(lam.getType());
  Trace("uf-lazy-ll") << "Lift " << lam << "?" << std::endl;
  for (const Node& v : syms)
  {
    TypeNode tn = v.getType();
    if (!tn.isFirstClass())
    {
      // don't need to worry about constructor/selector/testers/etc.
      continue;
    }
    size_t vsize = sts.getTypeSize(tn);
    if (vsize >= lsize)
    {
      shouldLift = true;
      Trace("uf-lazy-ll") << "...yes due to " << v << std::endl;
      break;
    }
  }
  d_needsLift[lam] = shouldLift;
  return shouldLift;
}

Node LambdaLift::getLiftLemma(const Node& f, const Node& n) const
{
  Node lam = getLambdaFor(n);
  Assert(!lam.isNull());
  NodeManager* nm = nodeManager();
  std::vector<Node> fapp;
  std::vector<Node> lapp;
  fapp.push_back(f);
  lapp.push_back(lam);
  fapp.insert(fapp.end(), lam[0].begin(), lam[0].end());
  lapp.insert(lapp.end(), lam[0].begin(), lam[0].end());
  // We use (lam x) instead of the body of lam as the right hand side, since
  // beta reduction uses capture-avoiding substitution.
  Node eq =
      nm->mkNode(Kind::APPLY_UF, fapp).eqNode(nm->mkNode(Kind::APPLY_UF, lapp));
  Node univ = nm->mkNode(Kind::FORALL, lam[0], eq);
  return nm->mkNode(Kind::IMPLIES, f.eqNode(n), univ);
}

Node LambdaLift::getLambdaFor(TNode n) { return FunctionConst::toLambda(n); }

bool LambdaLift::isLambda(TNode n)
{
  Kind k = n.getKind();
  return k == Kind::LAMBDA || k == Kind::FUNCTION_ARRAY_CONST;
}

Node LambdaLift::betaReduce(TNode lam, const std::vector<Node>& args) const
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::vector<Node> betaRed;
  betaRed.push_back(lam);
  betaRed.insert(betaRed.end(), args.begin(), args.end());
  Node app = nodeManager()->mkNode(Kind::APPLY_UF, betaRed);
  app = rewrite(app);
  return app;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
