/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Diophantine equation solver
 *
 * A Diophantine equation solver for the theory of arithmetic.
 */
#include "theory/arith/linear/dio_solver.h"

#include <algorithm>
#include <iostream>
#include <numeric>

#include "base/output.h"
#include "expr/skolem_manager.h"
#include "options/arith_options.h"
#include "smt/env.h"
#include "theory/arith/linear/partial_model.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

inline Node makeIntegerVariable(NodeManager* nm)
{
  return NodeManager::mkDummySkolem("intvar", nm->integerType());
}

DioSolver::DioSolver(Env& env)
    : EnvObj(env),
      d_inputConstraints(context()),
      d_nextInputConstraintToEnqueue(context(), 0),
      d_trail(context()),
      d_subs(context()),
      d_currentF(),
      d_savedQueue(context()),
      d_savedQueueIndex(context(), 0),
      d_conflictIndex(context()),
      d_maxInputCoefficientLength(context(), 0),
      d_usedDecomposeIndex(context(), false),
      d_lastPureSubstitution(context(), 0),
      d_pureSubstitionIter(context(), 0),
      d_decompositionLemmaQueue(context()),
      d_statistics(statisticsRegistry())
{
}

DioSolver::Statistics::Statistics(StatisticsRegistry& sr)
    : d_conflictCalls(sr.registerInt("theory::arith::dio::conflictCalls")),
      d_cutCalls(sr.registerInt("theory::arith::dio::cutCalls")),
      d_cuts(sr.registerInt("theory::arith::dio::cuts")),
      d_conflicts(sr.registerInt("theory::arith::dio::conflicts")),
      d_conflictTimer(sr.registerTimer("theory::arith::dio::conflictTimer")),
      d_cutTimer(sr.registerTimer("theory::arith::dio::cutTimer"))
{
}

DioSolver::Var DioSolver::varId(TNode n)
{
  auto it = d_varIds.find(n);
  if (it != d_varIds.end())
  {
    return it->second;
  }
  Var v = static_cast<Var>(d_varNodes.size());
  d_varNodes.push_back(n);
  d_varIds.emplace(n, v);
  Trace("arith::dio") << "dio var v" << v << " = " << n << endl;
  return v;
}

int DioSolver::varListCmp(Var a, Var b) const
{
  return VarList::parseVarList(d_varNodes[a])
      .cmp(VarList::parseVarList(d_varNodes[b]));
}

DioSolver::Form::Term DioSolver::minimalTerm(const Form& eq) const
{
  const std::vector<Form::Term>& terms = eq.getTerms();
  if (terms.empty())
  {
    return Form::Term(0, Integer(0));
  }
  size_t best = 0;
  Integer bestAbs = terms[0].second.abs();
  for (size_t i = 1, n = terms.size(); i < n; ++i)
  {
    Integer a = terms[i].second.abs();
    if (a < bestAbs
        || (a == bestAbs && varListCmp(terms[i].first, terms[best].first) < 0))
    {
      best = i;
      bestAbs = a;
    }
  }
  return terms[best];
}

DioSolver::TrailIndex DioSolver::pushToTrail(const Form& eq,
                                             const ProofForm& proof)
{
  TrailIndex k = d_trail.size();
  d_trail.push_back(Constraint(eq, proof, minimalTerm(eq)));
  return k;
}

bool DioSolver::queueConditions(TrailIndex t)
{
  Trace("queueConditions") << !inConflict() << std::endl;
  Trace("queueConditions") << gcdIsOne(t) << std::endl;
  Trace("queueConditions") << !debugAnySubstitionApplies(t) << std::endl;
  Trace("queueConditions") << !triviallySat(t) << std::endl;
  Trace("queueConditions") << !triviallyUnsat(t) << std::endl;

  return !inConflict() && gcdIsOne(t) && !debugAnySubstitionApplies(t)
         && !triviallySat(t) && !triviallyUnsat(t);
}

Node DioSolver::nextPureSubstitution()
{
  Assert(hasMorePureSubstitutions());
  SubIndex curr = d_pureSubstitionIter;
  d_pureSubstitionIter = d_pureSubstitionIter + 1;

  Assert(!d_subs[curr].d_hasFresh);
  Variable v(d_varNodes[d_subs[curr].d_eliminated]);

  SumPair sp = d_trail[d_subs[curr].d_constraint].d_eq.toSumPair(nodeManager(),
                                                                d_varNodes);
  Polynomial p = sp.getPolynomial();
  Polynomial cancelV = p + Polynomial::mkPolynomial(v);
  Node eq = nodeManager()->mkNode(Kind::EQUAL, v.getNode(), cancelV.getNode());
  return eq;
}

bool DioSolver::debugEqualityInInputEquations(Node eq)
{
  typedef context::CDList<InputConstraint>::const_iterator const_iterator;
  const_iterator i = d_inputConstraints.begin(), end = d_inputConstraints.end();
  for (; i != end; ++i)
  {
    Node reason_i = (*i).d_reason;
    if (eq == reason_i)
    {
      return true;
    }
  }
  return false;
}

void DioSolver::pushInputConstraint(const Comparison& eq, Node reason)
{
  Assert(!debugEqualityInInputEquations(reason));
  Assert(eq.debugIsIntegral());
  Assert(eq.getNode().getKind() == Kind::EQUAL);

  SumPair sp = eq.toSumPair();
  Assert(!sp.isNonlinear());
  Form f = Form::fromSumPair(sp, [this](TNode n) { return varId(n); });

  uint32_t length = f.maxLength();
  if (length > d_maxInputCoefficientLength)
  {
    d_maxInputCoefficientLength = length;
  }

  // The proof of an input constraint is the constraint itself, referred to by
  // its index in d_inputConstraints.
  InputConstraintIndex posInConstraintList = d_inputConstraints.size();
  TrailIndex posInTrail = d_trail.size();
  Trace("dio::pushInputConstraint")
      << "pushInputConstraint @ " << posInTrail << " " << eq.getNode() << " "
      << reason << endl;
  pushToTrail(f, ProofForm::mkVariable(static_cast<Var>(posInConstraintList)));
  d_inputConstraints.push_back(InputConstraint(reason, posInTrail));
}

DioSolver::TrailIndex DioSolver::scaleEqAtIndex(DioSolver::TrailIndex i,
                                                const Integer& g)
{
  Assert(g != 0);
  Form newEq = d_trail[i].d_eq.exactDivide(g);
  ProofForm newProof = d_trail[i].d_proof * Rational(Integer(1), g);

  Assert(newEq.gcdWithConstant().isOne());

  TrailIndex j = pushToTrail(newEq, newProof);

  Trace("arith::dio") << "scaleEqAtIndex(" << i << "," << g << ")" << endl;
  Trace("arith::dio") << "derived " << newEq << " with proof "
                      << newProof.toString("in") << endl;
  return j;
}

Node DioSolver::proveIndex(TrailIndex i)
{
  Assert(inRange(i));
  const ProofForm& proof = d_trail[i].d_proof;
  Assert(!proof.isConstant());
  Assert(proof.getConstant().isZero());

  NodeBuilder nb(nodeManager(), Kind::AND);
  for (const ProofForm::Term& t : proof.getTerms())
  {
    Assert(t.first < d_inputConstraints.size());
    Node input = d_inputConstraints[t.first].d_reason;
    if (input.getKind() == Kind::AND)
    {
      for (Node::iterator input_iter = input.begin(), input_end = input.end();
           input_iter != input_end;
           ++input_iter)
      {
        Node inputChild = *input_iter;
        nb << inputChild;
      }
    }
    else
    {
      nb << input;
    }
  }

  Node result = (nb.getNumChildren() == 1) ? nb[0] : (Node)nb;
  Trace("arith::dio") << "Proof at " << i << " is " << d_trail[i].d_eq << endl
                      << proof.toString("in") << endl
                      << " which becomes " << result << endl;
  return result;
}

bool DioSolver::anyCoefficientExceedsMaximum(TrailIndex j) const
{
  const Form& eq = d_trail[j].d_eq;
  uint32_t length = eq.maxLength();
  uint32_t nmonos = eq.size();

  bool result =
      nmonos >= 2 && length > d_maxInputCoefficientLength + MAX_GROWTH_RATE;
  if (TraceIsOn("arith::dio::max") && result)
  {
    Trace("arith::dio::max") << "about to drop:" << std::endl;
    Trace("arith::dio::max")
        << "d_trail[" << j << "].d_eq = " << eq << std::endl;
    Trace("arith::dio::max") << "d_trail[" << j << "].d_proof = "
                             << d_trail[j].d_proof.toString("in") << std::endl;
  }
  return result;
}

void DioSolver::enqueueInputConstraints()
{
  Assert(d_currentF.empty());
  while (d_savedQueueIndex < d_savedQueue.size())
  {
    d_currentF.push_back(d_savedQueue[d_savedQueueIndex]);
    d_savedQueueIndex = d_savedQueueIndex + 1;
  }

  while (d_nextInputConstraintToEnqueue < d_inputConstraints.size()
         && !inConflict())
  {
    size_t curr = d_nextInputConstraintToEnqueue;
    d_nextInputConstraintToEnqueue = d_nextInputConstraintToEnqueue + 1;

    TrailIndex i = d_inputConstraints[curr].d_trailPos;
    TrailIndex j = applyAllSubstitutionsToIndex(i);

    if (!triviallySat(j))
    {
      if (triviallyUnsat(j))
      {
        raiseConflict(j);
      }
      else
      {
        TrailIndex k = reduceByGCD(j);

        if (!inConflict())
        {
          if (triviallyUnsat(k))
          {
            raiseConflict(k);
          }
          else if (!(triviallySat(k) || anyCoefficientExceedsMaximum(k)))
          {
            pushToQueueBack(k);
          }
        }
      }
    }
  }
}

/*TODO Currently linear in the size of the Queue
 *It is not clear if am O(log n) strategy would be better.
 *Right before this in the algorithm is a substitution which could potentially
 *effect the key values of everything in the queue.
 */
void DioSolver::moveMinimumByAbsToQueueFront()
{
  Assert(!queueEmpty());

  // Select the minimum element.
  size_t indexInQueue = 0;
  const Integer* minAbs = &d_trail[d_currentF[indexInQueue]].d_minAbs;

  size_t N = d_currentF.size();
  for (size_t i = 1; i < N; ++i)
  {
    const Integer& curr = d_trail[d_currentF[i]].d_minAbs;
    if (curr < *minAbs)
    {
      indexInQueue = i;
      minAbs = &curr;
    }
  }

  TrailIndex tmp = d_currentF[indexInQueue];
  d_currentF[indexInQueue] = d_currentF.front();
  d_currentF.front() = tmp;
}

bool DioSolver::queueEmpty() const { return d_currentF.empty(); }

bool DioSolver::columnGcdIsOne(Var& out) const
{
  std::unordered_map<Var, Integer> gcdMap;
  std::vector<size_t> order;

  for (TrailIndex curr : d_currentF)
  {
    const std::vector<Form::Term>& terms = d_trail[curr].d_eq.getTerms();
    // Visit the terms in VarList order, so that the variable found first is
    // the same as when equations were Polynomials.
    order.resize(terms.size());
    std::iota(order.begin(), order.end(), 0);
    std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
      return varListCmp(terms[a].first, terms[b].first) < 0;
    });
    for (size_t k : order)
    {
      Var v = terms[k].first;
      const Integer& c = terms[k].second;
      auto it = gcdMap.find(v);
      if (it == gcdMap.end())
      {
        // have not seen v yet.
        // gcd is c
        Assert(!c.abs().isOne());
        gcdMap.emplace(v, c.abs());
      }
      else
      {
        Integer newGcd = it->second.gcd(c);
        if (newGcd.isOne())
        {
          out = v;
          return true;
        }
        it->second = newGcd;
      }
    }
  }
  return false;
}

void DioSolver::saveQueue()
{
  std::deque<TrailIndex>::const_iterator iter, end;
  for (iter = d_currentF.begin(), end = d_currentF.end(); iter != end; ++iter)
  {
    d_savedQueue.push_back(*iter);
  }
}

DioSolver::TrailIndex DioSolver::impliedGcdOfOne()
{
  Var var;
  if (!columnGcdIsOne(var))
  {
    return 0;
  }
  else
  {
    TrailIndex current;
    Integer currentCoeff, currentGcd;

    // step 1 find the first equation containing var
    // Set current and currentCoefficient
    std::deque<TrailIndex>::const_iterator iter, end;
    for (iter = d_currentF.begin(), end = d_currentF.end(); true; ++iter)
    {
      Assert(iter != end);
      current = *iter;
      const Integer* coeff = d_trail[current].d_eq.findCoefficient(var);
      if (coeff != nullptr)
      {
        currentCoeff = *coeff;
        currentGcd = currentCoeff.abs();

        ++iter;
        break;
      }
    }

    // For the rest of the equations keep reducing until the coefficient is one
    for (; iter != end; ++iter)
    {
      Trace("arith::dio") << "next round : " << currentCoeff << " "
                          << currentGcd << endl;
      TrailIndex inQueue = *iter;
      const Integer* iqc = d_trail[inQueue].d_eq.findCoefficient(var);
      if (iqc != nullptr)
      {
        // Copy: combineEqAtIndexes below appends to the trail.
        Integer inQueueCoeff = *iqc;

        // mpz_gcdext (mpz_t g, mpz_t s, mpz_t t, mpz_t a, mpz_t b);
        Integer g, s, t;
        // g = a*s + b*t
        Integer::extendedGcd(g, s, t, currentCoeff, inQueueCoeff);

        Trace("arith::dio") << "extendedReduction : " << endl;
        Trace("arith::dio") << g << " = " << s << "*" << currentCoeff << " + "
                            << t << "*" << inQueueCoeff << endl;

        Assert(g <= currentGcd);
        if (g < currentGcd)
        {
          if (s.sgn() == 0)
          {
            Trace("arith::dio") << "extendedReduction drop" << endl;
            Assert(inQueueCoeff.divides(currentGcd));
            current = *iter;
            currentCoeff = inQueueCoeff;
            currentGcd = inQueueCoeff.abs();
          }
          else
          {
            Trace("arith::dio") << "extendedReduction combine" << endl;
            TrailIndex next = combineEqAtIndexes(current, s, inQueue, t);

            Assert(d_trail[next].d_eq.getCoefficient(var) == g);

            current = next;
            currentCoeff = g;
            currentGcd = g;
            if (currentGcd == 1)
            {
              return current;
            }
          }
        }
      }
    }
    // This is not reachble as it is assured that the gcd of the column is 1
    Unreachable();
  }
}

bool DioSolver::processEquations(bool allowDecomposition)
{
  Assert(!inConflict());

  enqueueInputConstraints();
  while (!queueEmpty() && !inConflict())
  {
    moveMinimumByAbsToQueueFront();

    TrailIndex minimum = d_currentF.front();
    TrailIndex reduceIndex;

    Assert(inRange(minimum));
    Assert(!inConflict());

    Trace("arith::dio") << "processEquations " << minimum << " : "
                        << d_trail[minimum].d_eq << endl;

    Assert(queueConditions(minimum));

    bool canDirectlySolve = d_trail[minimum].d_minAbs.isOne();

    std::pair<SubIndex, TrailIndex> p;
    if (canDirectlySolve)
    {
      d_currentF.pop_front();
      p = solveIndex(minimum);
      reduceIndex = minimum;
    }
    else
    {
      TrailIndex implied = impliedGcdOfOne();

      if (implied != 0)
      {
        p = solveIndex(implied);
        reduceIndex = implied;
      }
      else if (allowDecomposition)
      {
        d_currentF.pop_front();
        p = decomposeIndex(minimum);
        reduceIndex = minimum;
      }
      else
      {
        // Cannot make progress without decomposeIndex
        saveQueue();
        break;
      }
    }

    SubIndex subIndex = p.first;
    TrailIndex next = p.second;
    subAndReduceCurrentFByIndex(subIndex);

    if (next != reduceIndex)
    {
      if (triviallyUnsat(next))
      {
        raiseConflict(next);
      }
      else if (!triviallySat(next))
      {
        pushToQueueBack(next);
      }
    }
  }

  d_currentF.clear();
  return inConflict();
}

Node DioSolver::processEquationsForConflict()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_conflictTimer);
  ++(d_statistics.d_conflictCalls);

  Assert(!inConflict());
  if (processEquations(true))
  {
    ++(d_statistics.d_conflicts);
    return proveIndex(getConflictIndex());
  }
  else
  {
    return Node::null();
  }
}

SumPair DioSolver::processEquationsForCut()
{
  TimerStat::CodeTimer codeTimer(d_statistics.d_cutTimer);
  ++(d_statistics.d_cutCalls);

  Assert(!inConflict());
  if (processEquations(true))
  {
    ++(d_statistics.d_cuts);
    return purifyIndex(getConflictIndex());
  }
  else
  {
    return SumPair::mkZero(nodeManager());
  }
}

SumPair DioSolver::purifyIndex(TrailIndex i)
{
  // TODO: "This uses the substitution trail to reverse the substitutions from
  // the sum term. Using the proof term should be more efficient."

  Form curr = d_trail[i].d_eq;

  for (size_t revIter = d_subs.size(); revIter > 0; --revIter)
  {
    size_t i2 = revIter - 1;
    if (!d_subs[i2].d_hasFresh)
    {
      continue;
    }
    Var var = d_subs[i2].d_fresh;
    const Integer* a = curr.findCoefficient(var);
    if (a != nullptr)
    {
      const Form& sj = d_trail[d_subs[i2].d_constraint].d_eq;
      Assert(sj.getCoefficient(var).isOne());
      // Copy: a points into curr, which is replaced below.
      Integer coeff = *a;
      curr = Form::combine(Integer(-1), curr, coeff, sj);
      Assert(curr.findCoefficient(var) == nullptr);
    }
  }
  return curr.toSumPair(nodeManager(), d_varNodes);
}

DioSolver::TrailIndex DioSolver::combineEqAtIndexes(DioSolver::TrailIndex i,
                                                    const Integer& q,
                                                    DioSolver::TrailIndex j,
                                                    const Integer& r)
{
  Trace("arith::dio") << "combineEqAtIndexes(" << i << "," << q << "," << j
                      << "," << r << ")" << endl;
  Trace("arith::dio") << "d_facts[i] = " << d_trail[i].d_eq << endl
                      << "d_facts[j] = " << d_trail[j].d_eq << endl;

  Form newEq = Form::combine(q, d_trail[i].d_eq, r, d_trail[j].d_eq);
  ProofForm newProof = ProofForm::combine(
      Rational(q), d_trail[i].d_proof, Rational(r), d_trail[j].d_proof);

  TrailIndex k = pushToTrail(newEq, newProof);

  Trace("arith::dio") << "derived " << newEq << " with proof "
                      << newProof.toString("in") << endl;

  return k;
}

DioSolver::TrailIndex DioSolver::applyAllSubstitutionsToIndex(
    DioSolver::TrailIndex trailIndex)
{
  TrailIndex currentIndex = trailIndex;
  for (SubIndex subIter = 0, siEnd = d_subs.size(); subIter < siEnd; ++subIter)
  {
    currentIndex = applySubstitution(subIter, currentIndex);
  }
  return currentIndex;
}

bool DioSolver::debugSubstitutionApplies(DioSolver::SubIndex si,
                                         DioSolver::TrailIndex ti)
{
  return d_trail[ti].d_eq.findCoefficient(d_subs[si].d_eliminated) != nullptr;
}

bool DioSolver::debugAnySubstitionApplies(DioSolver::TrailIndex i)
{
  for (SubIndex subIter = 0, siEnd = d_subs.size(); subIter < siEnd; ++subIter)
  {
    if (debugSubstitutionApplies(subIter, i))
    {
      return true;
    }
  }
  return false;
}

std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> DioSolver::solveIndex(
    DioSolver::TrailIndex i)
{
  Trace("arith::dio") << "before solveIndex(" << i << ":" << d_trail[i].d_eq
                      << ")" << endl;

  Assert(!d_trail[i].d_eq.isConstant());
  Assert(minimalTerm(d_trail[i].d_eq) == d_trail[i].d_minTerm);
  // Copy: scaleEqAtIndex below appends to the trail.
  const Form::Term av = d_trail[i].d_minTerm;
  Var var = av.first;
  const Integer& a = av.second;

  Assert(a.abs().isOne());

  TrailIndex ci = a.sgn() > 0 ? scaleEqAtIndex(i, Integer(-1)) : i;

  SubIndex subBy = d_subs.size();
  d_subs.push_back(Substitution(false, 0, var, ci));

  Trace("arith::dio") << "after solveIndex " << d_trail[ci].d_eq << " for "
                      << a << "*v" << var << endl;
  Assert(d_trail[ci].d_eq.getCoefficient(var).isNegativeOne());

  return make_pair(subBy, i);
}

std::pair<DioSolver::SubIndex, DioSolver::TrailIndex> DioSolver::decomposeIndex(
    DioSolver::TrailIndex i)
{
  d_usedDecomposeIndex = true;

  Trace("arith::dio") << "before decomposeIndex(" << i << ":"
                      << d_trail[i].d_eq << ")" << endl;

  Assert(!d_trail[i].d_eq.isConstant());
  Assert(minimalTerm(d_trail[i].d_eq) == d_trail[i].d_minTerm);
  // Copies: pushToTrail below appends to the trail.
  const Form::Term av = d_trail[i].d_minTerm;
  const ProofForm proof = d_trail[i].d_proof;
  Var var = av.first;
  const Integer& a = av.second;

  Assert(a.abs() > 1);

  // It is not sufficient to reduce the case where abs(a) == 1 to abs(a) > 1.
  // We need to handle both cases seperately to ensure termination.
  auto [q, r] = d_trail[i].d_eq.computeQR(a);

  Assert(q.getCoefficient(var).isOne());
  Assert(!r.isZero());

  Node freshNode = makeIntegerVariable(nodeManager());
  Var fresh = varId(freshNode);
  Form freshOne = Form::mkVariable(fresh);

  // this normalizes the coefficient of var to -1
  Form newSI = freshOne - q;

  TrailIndex ci = pushToTrail(newSI, ProofForm());
  addTrailElementAsLemma(ci);

  Trace("arith::dio") << "Decompose ci(" << ci << ":" << d_trail[ci].d_eq
                      << ") for " << a << "*v" << var << endl;
  Assert(d_trail[ci].d_eq.getCoefficient(var).isNegativeOne());

  Form newFact = r + freshOne * a;

  TrailIndex nextIndex = pushToTrail(newFact, proof);

  SubIndex subBy = d_subs.size();
  d_subs.push_back(Substitution(true, fresh, var, ci));

  Trace("arith::dio") << "Decompose nextIndex " << d_trail[nextIndex].d_eq
                      << endl;
  return make_pair(subBy, nextIndex);
}

DioSolver::TrailIndex DioSolver::applySubstitution(DioSolver::SubIndex si,
                                                   DioSolver::TrailIndex ti)
{
  Var var = d_subs[si].d_eliminated;
  TrailIndex subIndex = d_subs[si].d_constraint;

  const Integer* a = d_trail[ti].d_eq.findCoefficient(var);
  if (a == nullptr)
  {
    return ti;
  }
  // Copy: combineEqAtIndexes appends to the trail.
  Integer coeff = *a;
  Integer one(1);
  TrailIndex afterSub = combineEqAtIndexes(ti, one, subIndex, coeff);
  Assert(d_trail[afterSub].d_eq.findCoefficient(var) == nullptr);
  return afterSub;
}

DioSolver::TrailIndex DioSolver::reduceByGCD(DioSolver::TrailIndex ti)
{
  const Form& eq = d_trail[ti].d_eq;

  Trace("arith::dio") << "reduceByGCD " << eq << endl;
  Assert(!eq.isConstant());
  Integer g = eq.coefficientGcd();
  Assert(g >= 1);
  Trace("arith::dio") << "gcd=" << g << ", constant=" << eq.getConstant()
                      << endl;
  if (g.divides(eq.getConstant()))
  {
    if (g > 1)
    {
      return scaleEqAtIndex(ti, g);
    }
    else
    {
      return ti;
    }
  }
  else
  {
    raiseConflict(ti);
    return ti;
  }
}

bool DioSolver::triviallySat(TrailIndex i)
{
  const Form& eq = d_trail[i].d_eq;
  return eq.isConstant() && eq.getConstant().isZero();
}

bool DioSolver::triviallyUnsat(DioSolver::TrailIndex i)
{
  const Form& eq = d_trail[i].d_eq;
  return eq.isConstant() && !eq.getConstant().isZero();
}

bool DioSolver::gcdIsOne(DioSolver::TrailIndex i)
{
  return d_trail[i].d_eq.gcdWithConstant().isOne();
}

void DioSolver::subAndReduceCurrentFByIndex(DioSolver::SubIndex subIndex)
{
  size_t N = d_currentF.size();

  size_t readIter = 0, writeIter = 0;
  for (; readIter < N && !inConflict(); ++readIter)
  {
    TrailIndex curr = d_currentF[readIter];
    TrailIndex nextTI = applySubstitution(subIndex, curr);
    if (nextTI == curr)
    {
      d_currentF[writeIter] = curr;
      ++writeIter;
    }
    else
    {
      Assert(nextTI != curr);

      if (triviallyUnsat(nextTI))
      {
        raiseConflict(nextTI);
      }
      else if (!triviallySat(nextTI))
      {
        TrailIndex nextNextTI = reduceByGCD(nextTI);

        if (!(inConflict() || anyCoefficientExceedsMaximum(nextNextTI)))
        {
          Assert(queueConditions(nextNextTI));
          d_currentF[writeIter] = nextNextTI;
          ++writeIter;
        }
      }
    }
  }
  if (!inConflict() && writeIter < N)
  {
    d_currentF.resize(writeIter);
  }
}

void DioSolver::addTrailElementAsLemma(TrailIndex i)
{
  if (options().arith.exportDioDecompositions)
  {
    d_decompositionLemmaQueue.push(i);
  }
}

Node DioSolver::trailIndexToEquality(TrailIndex i) const
{
  SumPair sp = d_trail[i].d_eq.toSumPair(nodeManager(), d_varNodes);
  Node n = sp.getNode();
  Node zero = nodeManager()->mkConstRealOrInt(n.getType(), Rational(0));
  Node eq = n.eqNode(zero);
  return eq;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
