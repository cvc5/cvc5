/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The RealToInt preprocessing pass.
 *
 * Converts real operations into integer operations.
 */

#include "preprocessing/passes/real_to_int.h"

#include <string>

#include "expr/skolem_manager.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

RealToInt::RealToInt(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "real-to-int"), d_cache(userContext())
{
}

Node RealToInt::realToIntInternal(TNode n, NodeMap& cache, std::vector<Node>& var_eq)
{
  Trace("real-as-int-debug") << "Convert : " << n << std::endl;
  NodeMap::iterator find = cache.find(n);
  if (find != cache.end())
  {
    return (*find).second;
  }
  else
  {
    NodeManager* nm = nodeManager();
    SkolemManager* sm = nm->getSkolemManager();
    Node ret = n;
    if (n.getNumChildren() > 0)
    {
      if ((n.getKind() == Kind::EQUAL && n[0].getType().isReal())
          || n.getKind() == Kind::GEQ || n.getKind() == Kind::LT
          || n.getKind() == Kind::GT || n.getKind() == Kind::LEQ)
      {
        ret = rewrite(n);
        Trace("real-as-int-debug") << "Now looking at : " << ret << std::endl;
        if (!ret.isConst())
        {
          Node ret_lit = ret.getKind() == Kind::NOT ? ret[0] : ret;
          bool ret_pol = ret.getKind() != Kind::NOT;
          std::map<Node, Node> msum;
          if (ArithMSum::getMonomialSumLit(ret_lit, msum))
          {
            // get common coefficient
            std::vector<Node> coeffs;
            for (std::map<Node, Node>::iterator itm = msum.begin();
                 itm != msum.end();
                 ++itm)
            {
              Node v = itm->first;
              Node c = itm->second;
              if (!c.isNull())
              {
                Assert(c.isConst());
                coeffs.push_back(nm->mkConstInt(
                    Rational(c.getConst<Rational>().getDenominator())));
              }
            }
            Node cc = coeffs.empty()
                          ? Node::null()
                          : (coeffs.size() == 1 ? coeffs[0]
                                                : rewrite(nodeManager()->mkNode(
                                                    Kind::MULT, coeffs)));
            std::vector<Node> sum;
            for (std::map<Node, Node>::iterator itm = msum.begin();
                 itm != msum.end();
                 ++itm)
            {
              Node v = itm->first;
              Node c = itm->second;
              Node s;
              if (c.isNull())
              {
                c = cc.isNull() ? nodeManager()->mkConstInt(Rational(1)) : cc;
              }
              else
              {
                if (!cc.isNull())
                {
                  c = nm->mkConstInt(c.getConst<Rational>()
                                     * cc.getConst<Rational>());
                }
              }
              Assert(c.getType().isInteger());
              if (v.isNull())
              {
                sum.push_back(c);
              }
              else
              {
                Node vv = realToIntInternal(v, cache, var_eq);
                if (vv.getType().isInteger())
                {
                  sum.push_back(nodeManager()->mkNode(Kind::MULT, c, vv));
                }
                else
                {
                  throw TypeCheckingExceptionPrivate(
                      v,
                      std::string("Cannot translate to Int: ") + v.toString());
                }
              }
            }
            Node sumt =
                sum.empty()
                    ? nm->mkConstInt(Rational(0))
                    : (sum.size() == 1 ? sum[0] : nm->mkNode(Kind::ADD, sum));
            ret = nm->mkNode(
                ret_lit.getKind(), sumt, nm->mkConstInt(Rational(0)));
            if (!ret_pol)
            {
              ret = ret.negate();
            }
            Trace("real-as-int") << "Convert : " << std::endl;
            Trace("real-as-int") << "   " << n << std::endl;
            Trace("real-as-int") << "   " << ret << std::endl;
          }
        }
      }
      else
      {
        bool childChanged = false;
        std::vector<Node> children;
        Kind k = n.getKind();
        bool preserveTypes = true;
        // We change Real equalities to Int equalities, we handle other kinds
        // here as well.
        if (k==Kind::EQUAL || k==Kind::MULT || k==Kind::NONLINEAR_MULT ||
          k==Kind::ADD || k==Kind::SUB || k==Kind::NEG)
        {
          preserveTypes = false;
        }
        for (size_t i = 0; i < n.getNumChildren(); i++)
        {
          Node nc = realToIntInternal(n[i], cache, var_eq);
          // must preserve types if we don't belong to arithmetic, cast back
          if (preserveTypes)
          {
            if (!n[i].getType().isInteger() && nc.getType().isInteger())
            {
              nc = nm->mkNode(Kind::TO_REAL, nc);
            }
          }
          childChanged = childChanged || nc != n[i];
          children.push_back(nc);
        }
        if (childChanged)
        {
          if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            children.insert(children.begin(), n.getOperator());
          }
          ret = nm->mkNode(k, children);
        }
      }
    }
    else
    {
      TypeNode tn = n.getType();
      if (tn.isReal())
      {
        if (n.getKind() == Kind::BOUND_VARIABLE)
        {
          // cannot change the type of quantified variables, since this leads
          // to incompleteness.
          throw TypeCheckingExceptionPrivate(
              n,
              std::string("Cannot translate bound variable to Int: ")
                  + n.toString());
        }
        else if (n.isVar())
        {
          Node toIntN = nm->mkNode(Kind::TO_INTEGER, n);
          ret = sm->mkPurifySkolem(toIntN);
          Node retToReal = nm->mkNode(Kind::TO_REAL, ret);
          var_eq.push_back(n.eqNode(retToReal));
          // add the substitution to the preprocessing context, which ensures
          // the model for n is correct, as well as substituting it in the input
          // assertions when necessary.
          // The model value for the Real variable n we are eliminating is
          // (to_real k), where k is the Int skolem whose unpurified form is
          // (to_int n).
          d_preprocContext->addSubstitution(n, retToReal);
        }
      }
    }
    cache[n] = ret;
    return ret;
  }
}

PreprocessingPassResult RealToInt::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> var_eq;
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    Node a = (*assertionsToPreprocess)[i];
    Node ac = realToIntInternal(a, d_cache, var_eq);
    if (ac != a)
    {
      // this pass is refutation unsound, "unsat" will be "unknown"
      assertionsToPreprocess->markRefutationUnsound();
      Trace("real-to-int") << "Converted " << a << " to " << ac << std::endl;
      assertionsToPreprocess->replace(
          i, ac, nullptr, TrustId::PREPROCESS_REAL_TO_INT);
      assertionsToPreprocess->ensureRewritten(i);
      if (assertionsToPreprocess->isInConflict())
      {
        return PreprocessingPassResult::CONFLICT;
      }
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
