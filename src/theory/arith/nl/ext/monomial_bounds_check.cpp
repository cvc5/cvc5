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
 * Check for monomial bound inference lemmas.
 */

#include "theory/arith/nl/ext/monomial_bounds_check.h"

#include "expr/node.h"
#include "options/arith_options.h"
#include "proof/proof.h"
#include "theory/arith/arith_msum.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/ext/ext_state.h"
#include "theory/arith/nl/nl_model.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

namespace {
void debugPrintBound(const char* c, Node coeff, Node x, Kind type, Node rhs)
{
  Node t = ArithMSum::mkCoeffTerm(coeff, x);
  Trace(c) << t << " " << type << " " << rhs;
}

bool hasNewMonomials(Node n, const std::vector<Node>& existing)
{
  std::set<Node> visited;

  std::vector<Node> worklist;
  worklist.push_back(n);
  while (!worklist.empty())
  {
    Node current = worklist.back();
    worklist.pop_back();
    if (visited.find(current) == visited.end())
    {
      visited.insert(current);
      if (current.getKind() == Kind::NONLINEAR_MULT)
      {
        if (std::find(existing.begin(), existing.end(), current)
            == existing.end())
        {
          return true;
        }
      }
      else
      {
        worklist.insert(worklist.end(), current.begin(), current.end());
      }
    }
  }
  return false;
}
}  // namespace

MonomialBoundsCheck::MonomialBoundsCheck(Env& env, ExtState* data)
    : EnvObj(env), d_data(data), d_cdb(d_data->d_mdb)
{
}

void MonomialBoundsCheck::init()
{
  d_ci.clear();
  d_ci_exp.clear();
  d_ci_max.clear();
}

void MonomialBoundsCheck::checkBounds(const std::vector<Node>& asserts,
                                      const std::vector<Node>& false_asserts)
{
  // sort monomials by degree
  Trace("nl-ext-proc") << "Sort monomials by degree..." << std::endl;
  d_data->d_mdb.sortByDegree(d_data->d_ms);
  // all monomials
  d_data->d_mterms.insert(d_data->d_mterms.end(),
                          d_data->d_ms_vars.begin(),
                          d_data->d_ms_vars.end());
  d_data->d_mterms.insert(
      d_data->d_mterms.end(), d_data->d_ms.begin(), d_data->d_ms.end());

  const std::map<Node, std::map<Node, ConstraintInfo> >& cim =
      d_cdb.getConstraints();

  NodeManager* nm = NodeManager::currentNM();
  // register constraints
  Trace("nl-ext-debug") << "Register bound constraints..." << std::endl;
  for (const Node& lit : asserts)
  {
    bool polarity = lit.getKind() != Kind::NOT;
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    d_cdb.registerConstraint(atom);
    bool is_false_lit =
        std::find(false_asserts.begin(), false_asserts.end(), lit)
        != false_asserts.end();
    // add information about bounds to variables
    std::map<Node, std::map<Node, ConstraintInfo> >::const_iterator itc =
        cim.find(atom);
    if (itc == cim.end())
    {
      continue;
    }
    for (const std::pair<const Node, ConstraintInfo>& itcc : itc->second)
    {
      Node x = itcc.first;
      Node coeff = itcc.second.d_coeff;
      Node rhs = itcc.second.d_rhs;
      Kind type = itcc.second.d_type;
      Node exp = lit;
      if (!polarity)
      {
        // reverse
        if (type == Kind::EQUAL)
        {
          // we will take the strict inequality in the direction of the
          // model
          Node lhs = ArithMSum::mkCoeffTerm(coeff, x);
          Node query = nm->mkNode(Kind::GT, lhs, rhs);
          Node query_mv = d_data->d_model.computeAbstractModelValue(query);
          if (query_mv == d_data->d_true)
          {
            exp = query;
            type = Kind::GT;
          }
          else
          {
            Assert(query_mv == d_data->d_false);
            exp = nm->mkNode(Kind::LT, lhs, rhs);
            type = Kind::LT;
          }
        }
        else
        {
          type = negateKind(type);
        }
      }
      // add to status if maximal degree
      d_ci_max[x][coeff][rhs] = d_cdb.isMaximal(atom, x);
      if (TraceIsOn("nl-ext-bound-debug2"))
      {
        Node t = ArithMSum::mkCoeffTerm(coeff, x);
        Trace("nl-ext-bound-debug2") << "Add Bound: " << t << " " << type << " "
                                     << rhs << " by " << exp << std::endl;
      }
      bool updated = true;
      std::map<Node, Kind>::iterator its = d_ci[x][coeff].find(rhs);
      if (its == d_ci[x][coeff].end())
      {
        d_ci[x][coeff][rhs] = type;
        d_ci_exp[x][coeff][rhs] = exp;
      }
      else if (type != its->second)
      {
        Trace("nl-ext-bound-debug2")
            << "Joining kinds : " << type << " " << its->second << std::endl;
        Kind jk = joinKinds(type, its->second);
        if (jk == Kind::UNDEFINED_KIND)
        {
          updated = false;
        }
        else if (jk != its->second)
        {
          if (jk == type)
          {
            d_ci[x][coeff][rhs] = type;
            d_ci_exp[x][coeff][rhs] = exp;
          }
          else
          {
            d_ci[x][coeff][rhs] = jk;
            d_ci_exp[x][coeff][rhs] =
                nm->mkNode(Kind::AND, d_ci_exp[x][coeff][rhs], exp);
          }
        }
        else
        {
          updated = false;
        }
      }
      if (TraceIsOn("nl-ext-bound"))
      {
        if (updated)
        {
          Trace("nl-ext-bound") << "Bound: ";
          debugPrintBound("nl-ext-bound", coeff, x, d_ci[x][coeff][rhs], rhs);
          Trace("nl-ext-bound") << " by " << d_ci_exp[x][coeff][rhs];
          if (d_ci_max[x][coeff][rhs])
          {
            Trace("nl-ext-bound") << ", is max degree";
          }
          Trace("nl-ext-bound") << std::endl;
        }
      }
      // compute if bound is not satisfied, and store what is required
      // for a possible refinement
      if (options().arith.nlExtTangentPlanes)
      {
        if (is_false_lit)
        {
          d_data->d_tplane_refine.insert(x);
        }
      }
    }
  }
  // reflexive constraints
  Node null_coeff;
  for (unsigned j = 0; j < d_data->d_mterms.size(); j++)
  {
    Node n = d_data->d_mterms[j];
    d_ci[n][null_coeff][n] = Kind::EQUAL;
    d_ci_exp[n][null_coeff][n] = d_data->d_true;
    d_ci_max[n][null_coeff][n] = false;
  }

  Trace("nl-ext") << "Get inferred bound lemmas..." << std::endl;
  const std::map<Node, std::vector<Node> >& cpMap =
      d_data->d_mdb.getContainsParentMap();
  for (unsigned k = 0; k < d_data->d_mterms.size(); k++)
  {
    Node x = d_data->d_mterms[k];
    Trace("nl-ext-bound-debug")
        << "Process bounds for " << x << " : " << std::endl;
    std::map<Node, std::vector<Node> >::const_iterator itm = cpMap.find(x);
    if (itm == cpMap.end())
    {
      Trace("nl-ext-bound-debug") << "...has no parent monomials." << std::endl;
      continue;
    }
    Trace("nl-ext-bound-debug")
        << "...has " << itm->second.size() << " parent monomials." << std::endl;
    // check derived bounds
    std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itc =
        d_ci.find(x);
    if (itc == d_ci.end())
    {
      continue;
    }
    for (std::map<Node, std::map<Node, Kind> >::iterator itcc =
             itc->second.begin();
         itcc != itc->second.end();
         ++itcc)
    {
      Node coeff = itcc->first;
      Node t = ArithMSum::mkCoeffTerm(coeff, x);
      for (std::map<Node, Kind>::iterator itcr = itcc->second.begin();
           itcr != itcc->second.end();
           ++itcr)
      {
        Node rhs = itcr->first;
        // only consider this bound if maximal degree
        if (!d_ci_max[x][coeff][rhs])
        {
          continue;
        }
        Kind type = itcr->second;
        for (unsigned j = 0; j < itm->second.size(); j++)
        {
          Node y = itm->second[j];
          Node mult = d_data->d_mdb.getContainsDiff(x, y);
          // x <k> t => m*x <k'> t  where y = m*x
          // get the sign of mult
          Node mmv = d_data->d_model.computeConcreteModelValue(mult);
          Trace("nl-ext-bound-debug2")
              << "Model value of " << mult << " is " << mmv << std::endl;
          if (!mmv.isConst())
          {
            Trace("nl-ext-bound-debug")
                << "     ...coefficient " << mult
                << " is non-constant (probably transcendental)." << std::endl;
            continue;
          }
          int mmv_sign = mmv.getConst<Rational>().sgn();
          Trace("nl-ext-bound-debug2")
              << "  sign of " << mmv << " is " << mmv_sign << std::endl;
          if (mmv_sign == 0)
          {
            Trace("nl-ext-bound-debug")
                << "     ...coefficient " << mult << " is zero." << std::endl;
            continue;
          }
          Node lhsTgt = t;
          Node rhsTgt = rhs;
          // if we are making an equality below, we require making it
          // well-typed so that lhs/rhs have the same type. We use the
          // mkSameType utility to do this
          if (type == kind::EQUAL)
          {
            std::tie(lhsTgt, rhsTgt) = mkSameType(lhsTgt, rhsTgt);
          }
          Trace("nl-ext-bound-debug")
              << "  from " << x << " * " << mult << " = " << y << " and " << t
              << " " << type << " " << rhs << ", infer : " << std::endl;
          Kind infer_type = mmv_sign == -1 ? reverseRelationKind(type) : type;
          Node infer_lhs = nm->mkNode(Kind::MULT, mult, lhsTgt);
          Node infer_rhs = nm->mkNode(Kind::MULT, mult, rhsTgt);
          Node infer = nm->mkNode(infer_type, infer_lhs, infer_rhs);
          Trace("nl-ext-bound-debug") << "     " << infer << std::endl;
          Node infer_mv =
              d_data->d_model.computeAbstractModelValue(rewrite(infer));
          Trace("nl-ext-bound-debug")
              << "       ...infer model value is " << infer_mv << std::endl;
          if (infer_mv.isConst() && !infer_mv.getConst<bool>())
          {
            Node exp = nm->mkNode(
                Kind::AND,
                nm->mkNode(
                    mmv_sign == 1 ? Kind::GT : Kind::LT, mult, d_data->d_zero),
                d_ci_exp[x][coeff][rhs]);
            Node iblem = nm->mkNode(Kind::IMPLIES, exp, infer);
            Node iblem_rw = rewrite(iblem);
            bool introNewTerms = hasNewMonomials(iblem_rw, d_data->d_ms);
            Trace("nl-ext-bound-lemma")
                << "*** Bound inference lemma : " << iblem_rw
                << " (pre-rewrite : " << iblem << ")" << std::endl;
            CDProof* proof = nullptr;
            Node orig = d_ci_exp[x][coeff][rhs];
            if (d_data->isProofEnabled())
            {
              proof = d_data->getProof();
              Node simpleeq = nm->mkNode(type, lhsTgt, rhsTgt);
              // this is iblem, but uses (type t rhs) instead of the original
              // variant (which is identical under rewriting)
              // we first infer the "clean" version of the lemma and then
              // use MACRO_SR_PRED_TRANSFORM to rewrite
              Node tmplem = nm->mkNode(Kind::IMPLIES,
                                       nm->mkNode(Kind::AND, exp[0], simpleeq),
                                       infer);
              proof->addStep(tmplem,
                             mmv_sign == 1 ? PfRule::ARITH_MULT_POS
                                           : PfRule::ARITH_MULT_NEG,
                             {},
                             {mult, simpleeq});
              if (type == Kind::EQUAL && (rewrite(simpleeq) != rewrite(exp[1])))
              {
                // it is not identical under rewriting and we need to do some work here
                // The proof looks like this:
                // (SCOPE
                //   (MODUS_PONENS
                //     <tmplem>
                //     (AND_INTRO
                //       <first premise of iblem>
                //       (ARITH_TRICHOTOMY ***
                //         (AND_ELIM <second premise of iblem> 1)
                //         (AND_ELIM <second premise of iblem> 2)
                //       )
                //     )
                //   )
                //   :args <the two premises of iblem>
                // )
                // ***: the result of the AND_ELIM are rewritten forms of what
                // ARITH_TRICHOTOMY expects, and also their order is not clear.
                // Hence, we apply MACRO_SR_PRED_TRANSFORM to them, and check
                // which corresponds to which subterm of the premise.
                proof->addStep(exp[1][0],
                               PfRule::AND_ELIM,
                               {exp[1]},
                               {nm->mkConstInt(Rational(0))});
                proof->addStep(exp[1][1],
                               PfRule::AND_ELIM,
                               {exp[1]},
                               {nm->mkConstInt(Rational(1))});
                Node lb = nm->mkNode(Kind::GEQ, simpleeq[0], simpleeq[1]);
                Node rb = nm->mkNode(Kind::LEQ, simpleeq[0], simpleeq[1]);
                if (rewrite(lb) == rewrite(exp[1][0]))
                {
                  proof->addStep(
                      lb, PfRule::MACRO_SR_PRED_TRANSFORM, {exp[1][0]}, {lb});
                  proof->addStep(
                      rb, PfRule::MACRO_SR_PRED_TRANSFORM, {exp[1][1]}, {rb});
                }
                else
                {
                  proof->addStep(
                      lb, PfRule::MACRO_SR_PRED_TRANSFORM, {exp[1][1]}, {lb});
                  proof->addStep(
                      rb, PfRule::MACRO_SR_PRED_TRANSFORM, {exp[1][0]}, {rb});
                }
                proof->addStep(
                    simpleeq, PfRule::ARITH_TRICHOTOMY, {lb, rb}, {simpleeq});
                proof->addStep(
                    tmplem[0], PfRule::AND_INTRO, {exp[0], simpleeq}, {});
                proof->addStep(
                    tmplem[1], PfRule::MODUS_PONENS, {tmplem[0], tmplem}, {});
                proof->addStep(
                    iblem, PfRule::SCOPE, {tmplem[1]}, {exp[0], exp[1]});
              }
              else
              {
                proof->addStep(
                    iblem, PfRule::MACRO_SR_PRED_TRANSFORM, {tmplem}, {iblem});
              }
            }
            d_data->d_im.addPendingLemma(iblem,
                                         InferenceId::ARITH_NL_INFER_BOUNDS_NT,
                                         proof,
                                         introNewTerms);
          }
        }
      }
    }
  }
}

void MonomialBoundsCheck::checkResBounds()
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("nl-ext") << "Get monomial resolution inferred bound lemmas..."
                  << std::endl;
  size_t nmterms = d_data->d_mterms.size();
  for (unsigned j = 0; j < nmterms; j++)
  {
    Node a = d_data->d_mterms[j];
    std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itca =
        d_ci.find(a);
    if (itca == d_ci.end())
    {
      continue;
    }
    for (unsigned k = (j + 1); k < nmterms; k++)
    {
      Node b = d_data->d_mterms[k];
      std::map<Node, std::map<Node, std::map<Node, Kind> > >::iterator itcb =
          d_ci.find(b);
      if (itcb == d_ci.end())
      {
        continue;
      }
      Trace("nl-ext-rbound-debug") << "resolution inferences : compare " << a
                                   << " and " << b << std::endl;
      // if they have common factors
      std::map<Node, Node>::iterator ita = d_data->d_mono_diff[a].find(b);
      if (ita == d_data->d_mono_diff[a].end())
      {
        continue;
      }
      Trace("nl-ext-rbound") << "Get resolution inferences for [a] " << a
                             << " vs [b] " << b << std::endl;
      std::map<Node, Node>::iterator itb = d_data->d_mono_diff[b].find(a);
      Assert(itb != d_data->d_mono_diff[b].end());
      Node mv_a = d_data->d_model.computeAbstractModelValue(ita->second);
      Assert(mv_a.isConst());
      int mv_a_sgn = mv_a.getConst<Rational>().sgn();
      if (mv_a_sgn == 0)
      {
        // we don't compare monomials whose current model value is zero
        continue;
      }
      Node mv_b = d_data->d_model.computeAbstractModelValue(itb->second);
      Assert(mv_b.isConst());
      int mv_b_sgn = mv_b.getConst<Rational>().sgn();
      if (mv_b_sgn == 0)
      {
        // we don't compare monomials whose current model value is zero
        continue;
      }
      Trace("nl-ext-rbound") << "  [a] factor is " << ita->second
                             << ", sign in model = " << mv_a_sgn << std::endl;
      Trace("nl-ext-rbound") << "  [b] factor is " << itb->second
                             << ", sign in model = " << mv_b_sgn << std::endl;

      std::vector<Node> exp;
      // bounds of a
      for (std::map<Node, std::map<Node, Kind> >::iterator itcac =
               itca->second.begin();
           itcac != itca->second.end();
           ++itcac)
      {
        Node coeff_a = itcac->first;
        for (std::map<Node, Kind>::iterator itcar = itcac->second.begin();
             itcar != itcac->second.end();
             ++itcar)
        {
          Node rhs_a = itcar->first;
          Node rhs_a_res_base = nm->mkNode(Kind::MULT, itb->second, rhs_a);
          rhs_a_res_base = rewrite(rhs_a_res_base);
          if (hasNewMonomials(rhs_a_res_base, d_data->d_ms))
          {
            continue;
          }
          Kind type_a = itcar->second;
          exp.push_back(d_ci_exp[a][coeff_a][rhs_a]);

          // bounds of b
          for (std::map<Node, std::map<Node, Kind> >::iterator itcbc =
                   itcb->second.begin();
               itcbc != itcb->second.end();
               ++itcbc)
          {
            Node coeff_b = itcbc->first;
            Node rhs_a_res = ArithMSum::mkCoeffTerm(coeff_b, rhs_a_res_base);
            for (std::map<Node, Kind>::iterator itcbr = itcbc->second.begin();
                 itcbr != itcbc->second.end();
                 ++itcbr)
            {
              Node rhs_b = itcbr->first;
              Node rhs_b_res = nm->mkNode(Kind::MULT, ita->second, rhs_b);
              rhs_b_res = ArithMSum::mkCoeffTerm(coeff_a, rhs_b_res);
              rhs_b_res = rewrite(rhs_b_res);
              if (hasNewMonomials(rhs_b_res, d_data->d_ms))
              {
                continue;
              }
              Kind type_b = itcbr->second;
              exp.push_back(d_ci_exp[b][coeff_b][rhs_b]);
              if (TraceIsOn("nl-ext-rbound"))
              {
                Trace("nl-ext-rbound") << "* try bounds : ";
                debugPrintBound("nl-ext-rbound", coeff_a, a, type_a, rhs_a);
                Trace("nl-ext-rbound") << std::endl;
                Trace("nl-ext-rbound") << "               ";
                debugPrintBound("nl-ext-rbound", coeff_b, b, type_b, rhs_b);
                Trace("nl-ext-rbound") << std::endl;
              }
              Kind types[2];
              for (unsigned r = 0; r < 2; r++)
              {
                Node pivot_factor = r == 0 ? itb->second : ita->second;
                int pivot_factor_sign = r == 0 ? mv_b_sgn : mv_a_sgn;
                types[r] = r == 0 ? type_a : type_b;
                if (pivot_factor_sign == (r == 0 ? 1 : -1))
                {
                  types[r] = reverseRelationKind(types[r]);
                }
                if (pivot_factor_sign == 1)
                {
                  exp.push_back(
                      nm->mkNode(Kind::GT, pivot_factor, d_data->d_zero));
                }
                else
                {
                  exp.push_back(
                      nm->mkNode(Kind::LT, pivot_factor, d_data->d_zero));
                }
              }
              Kind jk = transKinds(types[0], types[1]);
              Trace("nl-ext-rbound-debug")
                  << "trans kind : " << types[0] << " + " << types[1] << " = "
                  << jk << std::endl;
              if (jk != Kind::UNDEFINED_KIND)
              {
                Node conc = nm->mkNode(jk, rhs_a_res, rhs_b_res);
                Node conc_mv = d_data->d_model.computeAbstractModelValue(conc);
                if (conc_mv == d_data->d_false)
                {
                  Node rblem = nm->mkNode(Kind::IMPLIES, nm->mkAnd(exp), conc);
                  Trace("nl-ext-rbound-lemma-debug")
                      << "Resolution bound lemma "
                         "(pre-rewrite) "
                         ": "
                      << rblem << std::endl;
                  rblem = rewrite(rblem);
                  Trace("nl-ext-rbound-lemma")
                      << "Resolution bound lemma : " << rblem << std::endl;
                  d_data->d_im.addPendingLemma(
                      rblem, InferenceId::ARITH_NL_RES_INFER_BOUNDS);
                }
              }
              exp.pop_back();
              exp.pop_back();
              exp.pop_back();
            }
          }
          exp.pop_back();
        }
      }
    }
  }
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
