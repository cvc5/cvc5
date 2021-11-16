/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

using namespace cvc5::kind;
using namespace cvc5::theory;

namespace cvc5 {
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
    NodeManager* nm = NodeManager::currentNM();
    SkolemManager* sm = nm->getSkolemManager();
    Node ret = n;
    if (n.getNumChildren() > 0)
    {
      if ((n.getKind() == kind::EQUAL && n[0].getType().isReal())
          || n.getKind() == kind::GEQ || n.getKind() == kind::LT
          || n.getKind() == kind::GT || n.getKind() == kind::LEQ)
      {
        ret = rewrite(n);
        Trace("real-as-int-debug") << "Now looking at : " << ret << std::endl;
        if (!ret.isConst())
        {
          Node ret_lit = ret.getKind() == kind::NOT ? ret[0] : ret;
          bool ret_pol = ret.getKind() != kind::NOT;
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
                coeffs.push_back(NodeManager::currentNM()->mkConst(
                    CONST_RATIONAL,
                    Rational(c.getConst<Rational>().getDenominator())));
              }
            }
            Node cc = coeffs.empty()
                          ? Node::null()
                          : (coeffs.size() == 1
                                 ? coeffs[0]
                                 : rewrite(NodeManager::currentNM()->mkNode(
                                     kind::MULT, coeffs)));
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
                c = cc.isNull() ? NodeManager::currentNM()->mkConst(
                        CONST_RATIONAL, Rational(1))
                                : cc;
              }
              else
              {
                if (!cc.isNull())
                {
                  c = rewrite(
                      NodeManager::currentNM()->mkNode(kind::MULT, c, cc));
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
                  sum.push_back(
                      NodeManager::currentNM()->mkNode(kind::MULT, c, vv));
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
                    ? NodeManager::currentNM()->mkConst(CONST_RATIONAL,
                                                        Rational(0))
                    : (sum.size() == 1
                           ? sum[0]
                           : NodeManager::currentNM()->mkNode(kind::PLUS, sum));
            ret = NodeManager::currentNM()->mkNode(
                ret_lit.getKind(),
                sumt,
                NodeManager::currentNM()->mkConst(CONST_RATIONAL, Rational(0)));
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
        for (unsigned i = 0; i < n.getNumChildren(); i++)
        {
          Node nc = realToIntInternal(n[i], cache, var_eq);
          childChanged = childChanged || nc != n[i];
          children.push_back(nc);
        }
        if (childChanged)
        {
          if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
          {
            children.insert(children.begin(), n.getOperator());
          }
          ret = NodeManager::currentNM()->mkNode(n.getKind(), children);
        }
      }
    }
    else
    {
      TypeNode tn = n.getType();
      if (tn.isReal() && !tn.isInteger())
      {
        if (n.getKind() == kind::BOUND_VARIABLE)
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
          Node toIntN = nm->mkNode(kind::TO_INTEGER, n);
          ret = sm->mkPurifySkolem(toIntN, "__realToIntInternal_var");
          var_eq.push_back(n.eqNode(ret));
          // add the substitution to the preprocessing context, which ensures
          // the model for n is correct, as well as substituting it in the input
          // assertions when necessary.
          d_preprocContext->addSubstitution(n, ret);
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
    assertionsToPreprocess->replace(
        i, realToIntInternal((*assertionsToPreprocess)[i], d_cache, var_eq));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
