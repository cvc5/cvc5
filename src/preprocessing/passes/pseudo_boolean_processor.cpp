/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "preprocessing/passes/pseudo_boolean_processor.h"

#include "base/output.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;
using namespace cvc5::internal::theory::arith;

PseudoBooleanProcessor::PseudoBooleanProcessor(
    PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "pseudo-boolean-processor"),
      d_pbBounds(userContext()),
      d_subCache(userContext()),
      d_pbs(userContext(), 0)
{
}

PreprocessingPassResult PseudoBooleanProcessor::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  learn(assertionsToPreprocess->ref());
  if (likelyToHelp())
  {
    applyReplacements(assertionsToPreprocess);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

bool PseudoBooleanProcessor::decomposeAssertion(Node assertion, bool negated)
{
  if (assertion.getKind() != kind::GEQ)
  {
    return false;
  }
  Assert(assertion.getKind() == kind::GEQ);

  Trace("pbs::rewrites") << "decomposeAssertion" << assertion << std::endl;

  Node l = assertion[0];
  Node r = assertion[1];

  if (!r.isConst())
  {
    Trace("pbs::rewrites") << "not rhs constant" << assertion << std::endl;
    return false;
  }
  // don't bother matching on anything other than + on the left hand side
  if (l.getKind() != kind::ADD)
  {
    Trace("pbs::rewrites") << "not plus" << assertion << std::endl;
    return false;
  }

  if (!linear::Polynomial::isMember(l))
  {
    Trace("pbs::rewrites") << "not polynomial" << assertion << std::endl;
    return false;
  }

  linear::Polynomial p = linear::Polynomial::parsePolynomial(l);
  clear();
  if (negated)
  {
    // (not (>= p r))
    // (< p r)
    // (> (-p) (-r))
    // (>= (-p) (-r +1))
    d_off = (-r.getConst<Rational>());

    if (d_off.value().isIntegral())
    {
      d_off = d_off.value() + Rational(1);
    }
    else
    {
      d_off = Rational(d_off.value().ceiling());
    }
  }
  else
  {
    // (>= p r)
    d_off = r.getConst<Rational>();
    d_off = Rational(d_off.value().ceiling());
  }
  Assert(d_off.value().isIntegral());

  int adj = negated ? -1 : 1;
  for (linear::Polynomial::iterator i = p.begin(), end = p.end(); i != end; ++i)
  {
    linear::Monomial m = *i;
    const Rational& coeff = m.getConstant().getValue();
    if (!(coeff.isOne() || coeff.isNegativeOne()))
    {
      return false;
    }
    Assert(coeff.sgn() != 0);

    const linear::VarList& vl = m.getVarList();
    Node v = vl.getNode();

    if (!isPseudoBoolean(v))
    {
      return false;
    }
    int sgn = adj * coeff.sgn();
    if (sgn > 0)
    {
      d_pos.push_back(v);
    }
    else
    {
      d_neg.push_back(v);
    }
  }
  // all of the variables are pseudoboolean
  // with coefficients +/- and the offsetoff
  return true;
}

bool PseudoBooleanProcessor::isPseudoBoolean(Node v) const
{
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);
  if (ci != d_pbBounds.end())
  {
    const std::pair<Node, Node>& p = (*ci).second;
    return !(p.first).isNull() && !(p.second).isNull();
  }
  return false;
}

void PseudoBooleanProcessor::addGeqZero(Node v, Node exp)
{
  Assert(isIntVar(v));
  Assert(!exp.isNull());
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);

  Trace("pbs::rewrites") << "addGeqZero " << v << std::endl;

  if (ci == d_pbBounds.end())
  {
    d_pbBounds.insert(v, std::make_pair(exp, Node::null()));
  }
  else
  {
    const std::pair<Node, Node>& p = (*ci).second;
    if (p.first.isNull())
    {
      Assert(!p.second.isNull());
      d_pbBounds.insert(v, std::make_pair(exp, p.second));
      Trace("pbs::rewrites") << "add pbs " << v << std::endl;
      Assert(isPseudoBoolean(v));
      d_pbs = d_pbs + 1;
    }
  }
}

void PseudoBooleanProcessor::addLeqOne(Node v, Node exp)
{
  Assert(isIntVar(v));
  Assert(!exp.isNull());
  Trace("pbs::rewrites") << "addLeqOne " << v << std::endl;
  CDNode2PairMap::const_iterator ci = d_pbBounds.find(v);
  if (ci == d_pbBounds.end())
  {
    d_pbBounds.insert(v, std::make_pair(Node::null(), exp));
  }
  else
  {
    const std::pair<Node, Node>& p = (*ci).second;
    if (p.second.isNull())
    {
      Assert(!p.first.isNull());
      d_pbBounds.insert(v, std::make_pair(p.first, exp));
      Trace("pbs::rewrites") << "add pbs " << v << std::endl;
      Assert(isPseudoBoolean(v));
      d_pbs = d_pbs + 1;
    }
  }
}

void PseudoBooleanProcessor::learnRewrittenGeq(Node assertion,
                                               bool negated,
                                               Node orig)
{
  Assert(assertion.getKind() == kind::GEQ);
  Assert(assertion == rewrite(assertion));

  // assume assertion is rewritten
  Node l = assertion[0];
  Node r = assertion[1];

  if (r.isConst())
  {
    const Rational& rc = r.getConst<Rational>();
    if (isIntVar(l))
    {
      if (!negated && rc.isZero())
      {  // (>= x 0)
        addGeqZero(l, orig);
      }
      else if (negated && rc == Rational(2))
      {
        addLeqOne(l, orig);
      }
    }
    else if (l.getKind() == kind::MULT && l.getNumChildren() == 2)
    {
      Node c = l[0], v = l[1];
      if (c.isConst() && c.getConst<Rational>().isNegativeOne())
      {
        if (isIntVar(v))
        {
          if (!negated && rc.isNegativeOne())
          {  // (>= (* -1 x) -1)
            addLeqOne(v, orig);
          }
        }
      }
    }
  }

  if (!negated)
  {
    learnGeqSub(assertion);
  }
}

void PseudoBooleanProcessor::learnInternal(Node assertion,
                                           bool negated,
                                           Node orig)
{
  switch (assertion.getKind())
  {
    case kind::GEQ:
    case kind::GT:
    case kind::LEQ:
    case kind::LT:
    {
      Node rw = rewrite(assertion);
      if (assertion == rw)
      {
        if (assertion.getKind() == kind::GEQ)
        {
          learnRewrittenGeq(assertion, negated, orig);
        }
      }
      else
      {
        learnInternal(rw, negated, orig);
      }
    }
    break;
    case kind::NOT: learnInternal(assertion[0], !negated, orig); break;
    default: break;  // do nothing
  }
}

void PseudoBooleanProcessor::learn(Node assertion)
{
  if (assertion.getKind() == kind::AND)
  {
    Node::iterator ci = assertion.begin(), cend = assertion.end();
    for (; ci != cend; ++ci)
    {
      learn(*ci);
    }
  }
  else
  {
    learnInternal(assertion, false, assertion);
  }
}

Node PseudoBooleanProcessor::mkGeqOne(Node v)
{
  NodeManager* nm = NodeManager::currentNM();
  return nm->mkNode(
      kind::GEQ, v, nm->mkConstRealOrInt(v.getType(), Rational(1)));
}

void PseudoBooleanProcessor::learn(const std::vector<Node>& assertions)
{
  std::vector<Node>::const_iterator ci, cend;
  ci = assertions.begin();
  cend = assertions.end();
  for (; ci != cend; ++ci)
  {
    learn(*ci);
  }
}

void PseudoBooleanProcessor::addSub(Node from, Node to)
{
  if (!d_subCache.hasSubstitution(from))
  {
    Node rw_to = rewrite(to);
    d_subCache.addSubstitution(from, rw_to);
  }
}

void PseudoBooleanProcessor::learnGeqSub(Node geq)
{
  Assert(geq.getKind() == kind::GEQ);
  const bool negated = false;
  bool success = decomposeAssertion(geq, negated);
  if (!success)
  {
    Trace("pbs::rewrites") << "failed " << std::endl;
    return;
  }
  Assert(d_off.value().isIntegral());
  Integer off = d_off.value().ceiling();

  // \sum pos >= \sum neg + off

  // for now special case everything we want
  // target easy clauses
  if (d_pos.size() == 1 && d_neg.size() == 1 && off.isZero())
  {
    // x >= y
    // |- (y >= 1) => (x >= 1)
    Node x = d_pos.front();
    Node y = d_neg.front();

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    Node imp = yGeq1.impNode(xGeq1);
    addSub(geq, imp);
  }
  else if (d_pos.size() == 0 && d_neg.size() == 2 && off.isNegativeOne())
  {
    // 0 >= (x + y -1)
    // |- 1 >= x + y
    // |- (or (not (x >= 1)) (not (y >= 1)))
    Node x = d_neg[0];
    Node y = d_neg[1];

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    Node cases = (xGeq1.notNode()).orNode(yGeq1.notNode());
    addSub(geq, cases);
  }
  else if (d_pos.size() == 2 && d_neg.size() == 1 && off.isZero())
  {
    // (x + y) >= z
    // |- (z >= 1) => (or (x >= 1) (y >=1 ))
    Node x = d_pos[0];
    Node y = d_pos[1];
    Node z = d_neg[0];

    Node xGeq1 = mkGeqOne(x);
    Node yGeq1 = mkGeqOne(y);
    Node zGeq1 = mkGeqOne(z);
    NodeManager* nm = NodeManager::currentNM();
    Node dis = nm->mkNode(kind::OR, zGeq1.notNode(), xGeq1, yGeq1);
    addSub(geq, dis);
  }
}

Node PseudoBooleanProcessor::applyReplacements(Node pre)
{
  Node assertion = rewrite(pre);

  Node result = d_subCache.apply(assertion);
  if (TraceIsOn("pbs::rewrites") && result != assertion)
  {
    Trace("pbs::rewrites") << "applyReplacements" << assertion << "-> "
                           << result << std::endl;
  }
  return result;
}

bool PseudoBooleanProcessor::likelyToHelp() const { return d_pbs >= 100; }

void PseudoBooleanProcessor::applyReplacements(
    AssertionPipeline* assertionsToPreprocess)
{
  for (size_t i = 0, N = assertionsToPreprocess->size(); i < N; ++i)
  {
    assertionsToPreprocess->replace(
        i, applyReplacements((*assertionsToPreprocess)[i]));
  }
}

void PseudoBooleanProcessor::clear()
{
  d_off.reset();
  d_pos.clear();
  d_neg.clear();
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
