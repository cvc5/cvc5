/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewriting based on learned literals
 */

#include "preprocessing/passes/learned_rewrite.h"

#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "preprocessing/assertion_pipeline.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

const char* toString(LearnedRewriteId i)
{
  switch (i)
  {
    case LearnedRewriteId::NON_ZERO_DEN: return "NON_ZERO_DEN";
    case LearnedRewriteId::INT_MOD_RANGE: return "INT_MOD_RANGE";
    case LearnedRewriteId::PRED_POS_LB: return "PRED_POS_LB";
    case LearnedRewriteId::PRED_ZERO_LB: return "PRED_ZERO_LB";
    case LearnedRewriteId::PRED_NEG_UB: return "PRED_NEG_UB";
    case LearnedRewriteId::NONE: return "NONE";
    default: return "?LearnedRewriteId?";
  }
}

std::ostream& operator<<(std::ostream& out, LearnedRewriteId i)
{
  out << toString(i);
  return out;
}

LearnedRewrite::LearnedRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "learned-rewrite"),
      d_lrewCount(smtStatisticsRegistry().registerHistogram<LearnedRewriteId>(
          "LearnedRewrite::lrewCount"))
{
}

PreprocessingPassResult LearnedRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  arith::BoundInference binfer;
  std::vector<Node> learnedLits = d_preprocContext->getLearnedLiterals();
  std::unordered_set<Node> llrw;
  std::unordered_map<TNode, Node> visited;
  if (learnedLits.empty())
  {
    Trace("learned-rewrite-ll") << "No learned literals" << std::endl;
    return PreprocessingPassResult::NO_CONFLICT;
  }
  else
  {
    Trace("learned-rewrite-ll") << "Learned literals:" << std::endl;
    std::map<Node, Node> originLit;
    for (const Node& l : learnedLits)
    {
      // maybe use the literal for bound inference?
      bool pol = l.getKind()!=NOT;
      TNode atom = pol ? l : l[0];
      Kind ak = atom.getKind();
      Assert(ak != LT && ak != GT && ak != LEQ);
      if ((ak == EQUAL && pol) || ak == GEQ)
      {
        // provide as < if negated >=
        Node atomu;
        if (!pol)
        {
          atomu = nm->mkNode(LT, atom[0], atom[1]);
          originLit[atomu] = l;
        }
        else
        {
          atomu = l;
          originLit[l] = l;
        }
        binfer.add(atomu);
      }
      Trace("learned-rewrite-ll") << "- " << l << std::endl;
    }
    const std::map<Node, arith::Bounds>& bs = binfer.get();
    // get the literals that were critical, i.e. used in the derivation of a
    // bound
    for (const std::pair<const Node, arith::Bounds>& b : bs)
    {
      for (size_t i = 0; i < 2; i++)
      {
        Node origin = i == 0 ? b.second.lower_origin : b.second.upper_origin;
        if (!origin.isNull())
        {
          Assert (originLit.find(origin)!=originLit.end());
          llrw.insert(originLit[origin]);
        }
      }
    }
    // rewrite the non-critical learned literals, some may be redundant
    for (const Node& l : learnedLits)
    {
      if (llrw.find(l) != llrw.end())
      {
        continue;
      }
      Node e = rewriteLearnedRec(l, binfer, llrw, visited);
      if (e.isConst())
      {
        // ignore true
        if (e.getConst<bool>())
        {
          continue;
        }
        // conflict, we are done
        assertionsToPreprocess->push_back(e);
        return PreprocessingPassResult::CONFLICT;
      }
      llrw.insert(e);
    }
    Trace("learned-rewrite-ll") << "end" << std::endl;
  }
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Trace("learned-rewrite-assert")
        << "LearnedRewrite: assert: " << prev << std::endl;
    Node e = rewriteLearnedRec(prev, binfer, llrw, visited);
    if (e != prev)
    {
      Trace("learned-rewrite-assert")
          << ".......................: " << e << std::endl;
      assertionsToPreprocess->replace(i, e);
    }
  }
  // Add the conjunction of learned literals back to assertions. Notice that
  // in some cases we may add top-level assertions back to the assertion list
  // unchanged.
  if (!llrw.empty())
  {
    std::vector<Node> llrvec(llrw.begin(), llrw.end());
    Node llc = nm->mkAnd(llrvec);
    Trace("learned-rewrite-assert")
        << "Re-add rewritten learned conjunction: " << llc << std::endl;
    assertionsToPreprocess->push_back(llc);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node LearnedRewrite::rewriteLearnedRec(Node n,
                                       arith::BoundInference& binfer,
                                       std::unordered_set<Node>& lems,
                                       std::unordered_map<TNode, Node>& visited)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);
    if (lems.find(cur) != lems.end())
    {
      // n is a learned literal: replace by true, not considered a rewrite
      // for statistics
      visited[cur] = nm->mkConst(true);
      continue;
    }
    if (it == visited.end())
    {
      // mark pre-visited with null; will post-visit to construct final node
      // in the block below.
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool needsRcons = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        needsRcons = needsRcons || cn != it->second;
        children.push_back(it->second);
      }
      if (needsRcons)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // rewrite here
      ret = rewriteLearned(ret, binfer, lems);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node LearnedRewrite::rewriteLearned(Node n,
                                    arith::BoundInference& binfer,
                                    std::unordered_set<Node>& lems)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("learned-rewrite-rr-debug") << "Rewrite " << n << std::endl;
  Node nr = Rewriter::rewrite(n);
  Kind k = nr.getKind();
  if (k == INTS_DIVISION || k == INTS_MODULUS || k == DIVISION)
  {
    // simpler if we know the divisor is non-zero
    Node num = n[0];
    Node den = n[1];
    bool isNonZeroDen = false;
    if (den.isConst())
    {
      isNonZeroDen = (den.getConst<Rational>().sgn() != 0);
    }
    else
    {
      arith::Bounds db = binfer.get(den);
      Trace("learned-rewrite-rr-debug")
          << "Bounds for " << den << " : " << db.lower_value << " "
          << db.upper_value << std::endl;
      if (!db.lower_value.isNull()
          && db.lower_value.getConst<Rational>().sgn() == 1)
      {
        isNonZeroDen = true;
      }
      else if (!db.upper_value.isNull()
               && db.upper_value.getConst<Rational>().sgn() == -1)
      {
        isNonZeroDen = true;
      }
    }
    if (isNonZeroDen)
    {
      Trace("learned-rewrite-rr-debug")
          << "...non-zero denominator" << std::endl;
      Kind nk = k;
      switch (k)
      {
        case INTS_DIVISION: nk = INTS_DIVISION_TOTAL; break;
        case INTS_MODULUS: nk = INTS_MODULUS_TOTAL; break;
        case DIVISION: nk = DIVISION_TOTAL; break;
        default: Assert(false); break;
      }
      std::vector<Node> children;
      children.insert(children.end(), n.begin(), n.end());
      Node ret = nm->mkNode(nk, children);
      nr = returnRewriteLearned(nr, ret, LearnedRewriteId::NON_ZERO_DEN);
      nr = Rewriter::rewrite(nr);
      k = nr.getKind();
    }
  }
  // constant int mod elimination by bound inference
  if (k == INTS_MODULUS_TOTAL)
  {
    Node num = n[0];
    Node den = n[1];
    arith::Bounds db = binfer.get(den);
    if ((!db.lower_value.isNull()
         && db.lower_value.getConst<Rational>().sgn() == 1)
        || (!db.upper_value.isNull()
            && db.upper_value.getConst<Rational>().sgn() == -1))
    {
      Rational bden = db.upper_value.isNull()
                          ? db.lower_value.getConst<Rational>()
                          : db.upper_value.getConst<Rational>().abs();
      // if 0 <= UB(num) < LB(den) or 0 <= UB(num) < -UB(den)
      arith::Bounds nb = binfer.get(num);
      if (!nb.upper_value.isNull())
      {
        Rational bnum = nb.upper_value.getConst<Rational>();
        if (bnum.sgn() != -1 && bnum < bden)
        {
          nr = returnRewriteLearned(nr, nr[0], LearnedRewriteId::INT_MOD_RANGE);
        }
      }
      // could also do num + k*den checks
    }
  }
  else if (k == GEQ || (k == EQUAL && nr[0].getType().isReal()))
  {
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(nr, msum))
    {
      Rational lb(0);
      Rational ub(0);
      bool lbSuccess = true;
      bool ubSuccess = true;
      Rational one(1);
      if (Trace.isOn("learned-rewrite-arith-lit"))
      {
        Trace("learned-rewrite-arith-lit")
            << "Arithmetic lit: " << nr << std::endl;
        for (const std::pair<const Node, Node>& m : msum)
        {
          Trace("learned-rewrite-arith-lit")
              << "  " << m.first << ", " << m.second << std::endl;
        }
      }
      for (const std::pair<const Node, Node>& m : msum)
      {
        bool isOneCoeff = m.second.isNull();
        Assert(isOneCoeff || m.second.isConst());
        if (m.first.isNull())
        {
          lb = lb + (isOneCoeff ? one : m.second.getConst<Rational>());
          ub = ub + (isOneCoeff ? one : m.second.getConst<Rational>());
        }
        else
        {
          arith::Bounds b = binfer.get(m.first);
          bool isNeg = !isOneCoeff && m.second.getConst<Rational>().sgn() == -1;
          // flip lower/upper if negative coefficient
          TNode l = isNeg ? b.upper_value : b.lower_value;
          TNode u = isNeg ? b.lower_value : b.upper_value;
          if (lbSuccess && !l.isNull())
          {
            Rational lc = l.getConst<Rational>();
            lb = lb
                 + (isOneCoeff ? lc
                               : Rational(lc * m.second.getConst<Rational>()));
          }
          else
          {
            lbSuccess = false;
          }
          if (ubSuccess && !u.isNull())
          {
            Rational uc = u.getConst<Rational>();
            ub = ub
                 + (isOneCoeff ? uc
                               : Rational(uc * m.second.getConst<Rational>()));
          }
          else
          {
            ubSuccess = false;
          }
          if (!lbSuccess && !ubSuccess)
          {
            break;
          }
        }
      }
      if (lbSuccess)
      {
        if (lb.sgn() == 1)
        {
          // if positive lower bound, then GEQ is true, EQUAL is false
          Node ret = nm->mkConst(k == GEQ);
          nr = returnRewriteLearned(nr, ret, LearnedRewriteId::PRED_POS_LB);
          return nr;
        }
        else if (lb.sgn() == 0 && k == GEQ)
        {
          // zero lower bound, GEQ is true
          Node ret = nm->mkConst(true);
          nr = returnRewriteLearned(nr, ret, LearnedRewriteId::PRED_ZERO_LB);
          return nr;
        }
      }
      else if (ubSuccess)
      {
        if (ub.sgn() == -1)
        {
          // if negative upper bound, then GEQ and EQUAL are false
          Node ret = nm->mkConst(false);
          nr = returnRewriteLearned(nr, ret, LearnedRewriteId::PRED_NEG_UB);
          return nr;
        }
      }
    }
  }
  return nr;
}

Node LearnedRewrite::returnRewriteLearned(Node n, Node nr, LearnedRewriteId id)
{
  if (Trace.isOn("learned-rewrite"))
  {
    Trace("learned-rewrite") << "LearnedRewrite::Rewrite: (" << id << ") " << n
                             << " == " << nr << std::endl;
  }
  d_lrewCount << id;
  return nr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
