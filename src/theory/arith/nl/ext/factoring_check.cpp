/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of factoring check.
 */

#include "theory/arith/nl/ext/factoring_check.h"

#include "expr/node.h"
#include "expr/skolem_manager.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/ext_state.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

FactoringCheck::FactoringCheck(Env& env, ExtState* data)
    : EnvObj(env), d_data(data)
{
  d_one = NodeManager::currentNM()->mkConstReal(Rational(1));
}

void FactoringCheck::check(const std::vector<Node>& asserts,
                           const std::vector<Node>& false_asserts)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext") << "Get factoring lemmas..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != Kind::NOT;
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    Node litv = d_data->d_model.computeConcreteModelValue(lit);
    bool considerLit = false;
    // Only consider literals that are in false_asserts.
    considerLit = std::find(false_asserts.begin(), false_asserts.end(), lit)
                  != false_asserts.end();

    if (considerLit)
    {
      std::map<Node, Node> msum;
      if (ArithMSum::getMonomialSumLit(atom, msum))
      {
        Trace("nl-ext-factor") << "Factoring for literal " << lit
                               << ", monomial sum is : " << std::endl;
        if (TraceIsOn("nl-ext-factor"))
        {
          ArithMSum::debugPrintMonomialSum(msum, "nl-ext-factor");
        }
        std::map<Node, std::vector<Node> > factor_to_mono;
        std::map<Node, std::vector<Node> > factor_to_mono_orig;
        for (std::map<Node, Node>::iterator itm = msum.begin();
             itm != msum.end();
             ++itm)
        {
          if (!itm->first.isNull())
          {
            if (itm->first.getKind() == Kind::NONLINEAR_MULT)
            {
              std::vector<Node> children;
              for (unsigned i = 0; i < itm->first.getNumChildren(); i++)
              {
                children.push_back(itm->first[i]);
              }
              std::map<Node, bool> processed;
              for (unsigned i = 0; i < itm->first.getNumChildren(); i++)
              {
                if (processed.find(itm->first[i]) == processed.end())
                {
                  processed[itm->first[i]] = true;
                  children[i] = d_one;
                  if (!itm->second.isNull())
                  {
                    children.push_back(itm->second);
                  }
                  Node val = nm->mkNode(Kind::MULT, children);
                  if (!itm->second.isNull())
                  {
                    children.pop_back();
                  }
                  children[i] = itm->first[i];
                  val = rewrite(val);
                  factor_to_mono[itm->first[i]].push_back(val);
                  factor_to_mono_orig[itm->first[i]].push_back(itm->first);
                }
              }
            }
          }
        }
        for (std::map<Node, std::vector<Node> >::iterator itf =
                 factor_to_mono.begin();
             itf != factor_to_mono.end();
             ++itf)
        {
          Node x = itf->first;
          if (itf->second.size() == 1)
          {
            std::map<Node, Node>::iterator itm = msum.find(x);
            if (itm != msum.end())
            {
              itf->second.push_back(itm->second.isNull() ? d_one : itm->second);
              factor_to_mono_orig[x].push_back(x);
            }
          }
          if (itf->second.size() <= 1)
          {
            continue;
          }
          Node sum = nm->mkNode(Kind::ADD, itf->second);
          sum = rewrite(sum);
          // remove TO_REAL if necessary here
          sum = sum.getKind() == TO_REAL ? sum[0] : sum;
          Trace("nl-ext-factor")
              << "* Factored sum for " << x << " : " << sum << std::endl;

          CDProof* proof = nullptr;
          if (d_data->isProofEnabled())
          {
            proof = d_data->getProof();
          }
          Node kf = getFactorSkolem(sum, proof);
          std::vector<Node> poly;
          poly.push_back(nm->mkNode(Kind::MULT, x, kf));
          std::map<Node, std::vector<Node> >::iterator itfo =
              factor_to_mono_orig.find(x);
          Assert(itfo != factor_to_mono_orig.end());
          for (std::map<Node, Node>::iterator itm = msum.begin();
               itm != msum.end();
               ++itm)
          {
            if (std::find(itfo->second.begin(), itfo->second.end(), itm->first)
                == itfo->second.end())
            {
              poly.push_back(ArithMSum::mkCoeffTerm(
                  itm->second, itm->first.isNull() ? d_one : itm->first));
            }
          }
          Node polyn = poly.size() == 1 ? poly[0] : nm->mkNode(Kind::ADD, poly);
          Trace("nl-ext-factor")
              << "...factored polynomial : " << polyn << std::endl;
          Node zero = nm->mkConstRealOrInt(polyn.getType(), Rational(0));
          Node conc_lit = nm->mkNode(atom.getKind(), polyn, zero);
          conc_lit = rewrite(conc_lit);
          if (!polarity)
          {
            conc_lit = conc_lit.negate();
          }

          std::vector<Node> lemma_disj;
          lemma_disj.push_back(conc_lit);
          lemma_disj.push_back(lit.negate());
          Node flem = nm->mkNode(Kind::OR, lemma_disj);
          Trace("nl-ext-factor") << "...lemma is " << flem << std::endl;
          if (d_data->isProofEnabled())
          {
            Node k_eq = kf.eqNode(sum);
            Node split = nm->mkNode(Kind::OR, lit, lit.notNode());
            proof->addStep(split, PfRule::SPLIT, {}, {lit});
            proof->addStep(
                flem, PfRule::MACRO_SR_PRED_TRANSFORM, {split, k_eq}, {flem});
          }
          d_data->d_im.addPendingLemma(
              flem, InferenceId::ARITH_NL_FACTOR, proof);
        }
      }
    }
  }
}

Node FactoringCheck::getFactorSkolem(Node n, CDProof* proof)
{
  std::map<Node, Node>::iterator itf = d_factor_skolem.find(n);
  Node k;
  if (itf == d_factor_skolem.end())
  {
    NodeManager* nm = NodeManager::currentNM();
    k = nm->getSkolemManager()->mkPurifySkolem(n);
    Node k_eq = k.eqNode(n);
    Trace("nl-ext-factor") << "...adding factor skolem " << k << " == " << n
                           << std::endl;
    d_data->d_im.addPendingLemma(k_eq, InferenceId::ARITH_NL_FACTOR, proof);
    d_factor_skolem[n] = k;
  }
  else
  {
    k = itf->second;
  }
  if (d_data->isProofEnabled())
  {
    Node k_eq = k.eqNode(n);
    proof->addStep(k_eq, PfRule::MACRO_SR_PRED_INTRO, {}, {k_eq});
  }
  return k;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
