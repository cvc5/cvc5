/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Extension to the theory of arithmetic for the LIA* predicate
 * int.star-contains.
 *
 * --------------------------------------------------------------------------
 * What the lia* operator means
 * --------------------------------------------------------------------------
 * A literal
 *     (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) v_1 ... v_n)
 * asserts that the vector v = (v_1, ..., v_n) belongs to the *star* (additive
 * closure) of the set
 *     S = { x in Z^n : p(x) }.
 * The star of S is
 *     S* = { the sum of finitely many (>= 0) elements of S },
 * with the empty sum giving the zero vector. So v in S* iff v can be written as
 * a finite sum of vectors each of which satisfies the predicate p. This is the
 * integer analogue of Kleene star in the monoid (Z^n, +); the sets S* are
 * exactly the semilinear sets. With --arith-liastar-assume-nonnegative the
 * summands are additionally taken to be nonnegative.
 *
 * --------------------------------------------------------------------------
 * The decision procedure (Levatich, Bjorner, Piskac, Shoham, VMCAI 2020,
 * "Solving LIA* Using Approximations")
 * --------------------------------------------------------------------------
 * 1. Put p into disjunctive normal form, p <=> D_1 or ... or D_m, where each
 *    D_j is a conjunction of linear (in)equalities, i.e. a convex polyhedron.
 *    Then S = S_1 union ... union S_m, with S_j the integer points of D_j.
 *    (See liastar_utils.cpp for the normalization.)
 *
 * 2. The additive closure distributes over the union as a Minkowski sum:
 *        S* = S_1* + ... + S_m*,
 *    because any sum of elements of S can be grouped by the polyhedron each
 *    summand came from. So a vector is in S* iff it is the sum of one
 *    contribution from each cone's semigroup S_j* (each including 0).
 *
 * 3. For each polyhedron Normaliz computes a Hilbert basis and module
 *    generators. The integer points of D_j are
 *        { g + sum_k l_k h_k : g a module generator, l_k >= 0 },
 *    where the h_k are the Hilbert basis of the recession cone (its rays). The
 *    semigroup S_j* is then captured by giving each module generator g a
 *    non-negative multiplier mu_g (how many copies of g are taken) and each ray
 *    a multiplier l_k, coupled by `mu_g = 0 => l_k = 0` (a ray of g is only
 *    available when g itself is used). See `LiaStarUtils::getGeneratorBody`.
 *
 * 4. Summing these contributions over all cones gives the *star constraints*: a
 *    system of linear constraints over fresh non-negative integers whose
 *    satisfiability is equivalent to `v in S*`. The extension then emits the
 *    reduction lemma `atom = star`.
 *
 * --------------------------------------------------------------------------
 * Two strategies
 * --------------------------------------------------------------------------
 * Eager (`eagerCheckStar`): compute the full DNF, build every cone up front and
 *   emit the exact equivalence `atom = star` in one shot.
 *
 * Lazy (`lazyCheckStar` / `lazyHilbert`): the DNF can blow up, so instead keep
 * a persistent incremental QF_LIA subsolver seeded with p. Each round it
 *   produces a model in a region of p not yet covered by a cone; the convex
 *   cell containing that model is read off (`LiaStarUtils::getDisjunct`),
 *   turned into a cone, and added to the accumulated set. The star built from
 *   the cones found so far is an *under-approximation*, so the equivalence is
 *   asserted only tentatively under a fresh boolean guard `g` (`g => (atom =
 *   star)`), biased true, until the subsolver becomes unsat -- meaning every
 *   cell of p is covered and the encoding is exact, at which point the
 *   unconditional equivalence is emitted.
 *
 * --------------------------------------------------------------------------
 * Where lemmas come from
 * --------------------------------------------------------------------------
 * `checkFullEffort` is the entry point. For each int.star-contains literal, of
 * either polarity, it emits:
 *   - with --arith-liastar-assume-nonnegative, a non-negativity lemma (the
 *     vector lives in the non-negative orthant where the atom holds);
 *   - a split on the substituted predicate `p[v]` (if v itself satisfies p it
 *     is a single-summand member of S*);
 *   - and then, unless the current model already satisfies a positive literal,
 *     the star reduction via the eager or lazy strategy.
 * The skolems of the reduction witness v in S* when the atom holds, but when
 * the atom is false the lemma only says that this one choice of them is not a
 * witness. Once the reduction is exact, a negative literal is therefore also
 * reduced by `(or atom (forall x. not star[x]))`, see `recordReduction`, which
 * the quantifier instantiation for linear arithmetic handles. In the lazy
 * strategy a negative literal discovers one cell per round, without the
 * shortcuts of the positive case, until the enumeration is complete.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

#include <algorithm>

#include "liastar_utils.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/theory_arith.h"
#include "theory/theory_model.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

using namespace libnormaliz;

using libnormaliz::operator<<;

/** Print the elements of l separated by spaces, for traces. */
template <typename T>
std::string toString(const std::vector<T>& l)
{
  std::stringstream ss;
  for (const auto& i : l)
  {
    ss << i << " ";
  }
  ss << std::endl;
  return ss.str();
}

namespace {

/**
 * Build the "sum constraints" that tie the star vector to the cone
 * contributions: for each coordinate i,
 *     vec[i] = sum over all generators of (point[i] + sum over rays of ray[i]).
 * `lambdas` holds one (point, rays) contribution per module generator across
 * all cones (as produced by `LiaStarUtils::getGeneratorBody`); `vec` is the
 * star vector (the v_1 ... v_n). Returns the n equalities. For a polyhedron
 * Normaliz appends a homogenizing coordinate to each generator, e.g. the
 * module generator 2 1 1 for (and (>= x 2) (= y 1)); the sums ignore it.
 */
std::vector<Node> buildSumConstraints(
    NodeManager* nm,
    Node zero,
    const std::vector<Node>& vec,
    const std::vector<std::pair<Vector, std::vector<Vector>>>& lambdas)
{
  size_t dimension = vec.size();
  Vector sums(dimension, zero);
  for (const std::pair<Vector, std::vector<Vector>>& lambda : lambdas)
  {
    for (size_t i = 0; i < dimension; i++)
    {
      sums[i] = nm->mkNode(Kind::ADD, sums[i], lambda.first[i]);
      for (const Vector& ray : lambda.second)
      {
        sums[i] = nm->mkNode(Kind::ADD, sums[i], ray[i]);
      }
    }
  }
  std::vector<Node> result;
  for (size_t i = 0; i < dimension; i++)
  {
    result.push_back(vec[i].eqNode(sums[i]));
  }
  return result;
}

/**
 * Trace the cone's Hilbert basis and return its module generators -- the base
 * lattice points g of the decomposition { g + sum_j l_j h_j } of the cone's
 * integer points. A purely homogeneous cone, e.g. the one of
 * (and (>= x y) (>= y 0)), has no module generators; its single base point is
 * then the origin, so the zero vector is returned instead.
 */
std::vector<std::vector<Integer>> getConeGenerators(
    libnormaliz::Cone<Integer>& cone, size_t dimension)
{
  Trace("liastar-ext") << "Hilbert basis:" << std::endl;
  for (const auto& basis : cone.getHilbertBasis())
  {
    Trace("liastar-ext") << toString(basis) << std::endl;
  }
  Trace("liastar-ext") << "Module generators:" << std::endl;
  if (!cone.getModuleGenerators().empty())
  {
    return cone.getModuleGenerators();
  }
  return {std::vector<Integer>(dimension, Integer(0))};
}

/**
 * Emit the preamble of a self-contained SMT-LIB script on the
 * "liastar-ext-smt" channel: solver options plus a declaration for every star
 * variable in `variables`, and a non-negativity assertion for each of them
 * when `assumeNonnegative`, since Normaliz only assumes them to be nonnegative
 * with --arith-liastar-assume-nonnegative. The queries later emitted on the
 * same channel (see `LiaStarUtils::traceEquivalenceCheck`) then form a
 * replayable soundness check of the reduction: every (check-sat) must answer
 * unsat.
 */
void traceSmtPreamble(Node variables, bool assumeNonnegative)
{
  // `!TraceIsOn(...)` does not compile in non-tracing builds, so guard
  // positively.
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(set-logic ALL)" << std::endl;
    Trace("liastar-ext-smt") << "(set-option :incremental true)" << std::endl;
    Trace("liastar-ext-smt")
        << "(set-option :produce-models true)" << std::endl;
    for (Node var : variables)
    {
      Trace("liastar-ext-smt")
          << "(declare-const " << var << " Int)" << std::endl;
    }
    if (assumeNonnegative)
    {
      for (Node var : variables)
      {
        Trace("liastar-ext-smt")
            << "(assert (>= " << var << " 0))" << std::endl;
      }
    }
  }
}

/**
 * Emit, on the "liastar-ext-smt" channel, the queries validating the
 * membership encoding: one query per disjunct asserting it differs from the
 * predicate cell it encodes, and a final query asserting the whole predicate
 * (lambda[1]) differs from the disjunction of all membership formulas. All of
 * them must be unsat when the trace is replayed.
 */
void traceMembershipValidation(NodeManager* nm,
                               Node lambda,
                               const std::vector<std::pair<Node, Node>>& lia)
{
  for (size_t i = 0; i < lia.size(); i++)
  {
    LiaStarUtils::traceEquivalenceCheck(
        std::to_string(i).c_str(), lia[i].first, lia[i].second);
  }
  std::vector<Node> disjunctions;
  std::transform(
      lia.begin(), lia.end(), std::back_inserter(disjunctions), [](auto& p) {
        return p.second;
      });
  Node liaFormula;
  if (disjunctions.size() == 0)
  {
    liaFormula = nm->mkConst(false);
  }
  else if (disjunctions.size() == 1)
  {
    liaFormula = disjunctions[0];
  }
  else
  {
    liaFormula = nm->mkNode(Kind::OR, disjunctions);
  }
  LiaStarUtils::traceEquivalenceCheck("lia formula", lambda[1], liaFormula);
}

}  // namespace

LiaStarExtension::LiaStarExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_nm(nodeManager()),
      d_arith(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasAssertions(context(), false),
      d_negatedReductions(userContext()),
      d_negatedReductionsSent(userContext()),
      d_stats(statisticsRegistry()),
      d_lastGuard(userContext())
{
  d_extTheory.addFunctionKind(Kind::STAR_CONTAINS);
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
  d_zero = nodeManager()->mkConstInt(Rational(0));
  d_one = nodeManager()->mkConstInt(Rational(1));
}

LiaStarExtension::~LiaStarExtension() {}

void LiaStarExtension::preRegisterTerm(TNode n)
{
  // register terms with extended theory, to find extended terms that can be
  // eliminated by context-dependent simplification. n is, e.g.,
  // (int.star-contains (lambda ((x Int)) (= x 2)) a).
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_extTheory.registerTerm(n);
  }
}

bool LiaStarExtension::collectModelValues(TheoryModel* m)
{
  std::vector<Node> assertions;
  getAssertions(assertions);
  for (const Node& lit : assertions)
  {
    bool polarity = lit.getKind() != Kind::NOT;
    Node atom = polarity ? lit : lit[0];
    if (!m->assertPredicate(atom, polarity))
    {
      return false;
    }
  }
  return true;
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("liastar-ext") << "Getting assertions..." << std::endl;
  Trace("liastar-ext") << "---------------------" << std::endl;
  // of the facts L, (>= b 2) and (not (= b 1)), for L of checkFullEffort,
  // only the first is collected
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-ext") << lit << std::endl;
    Node atom = lit.getKind() == Kind::NOT ? lit[0] : lit;
    if (atom.getKind() == Kind::STAR_CONTAINS)
    {
      assertions.push_back(lit);
    }
  }
  Trace("liastar-ext") << "---------------------" << std::endl;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  Assert(hasAssertions());
  // Full-effort check: for each int.star-contains literal emit the necessary
  // lemmas and, if the current model does not already satisfy the literal,
  // refine via the eager or lazy star reduction. The steps 1-5 below are
  // those documented in liastar_extension.h.
  TimerStat::CodeTimer checkTimer(d_stats.d_checkFullEffortTime);
  ++d_stats.d_checkRuns;
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);
  d_stats.d_starContainsLiterals += assertions.size();

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const Node& literal : assertions)
  {
    // literal is L, or (not L) for a negative literal, and atom is L
    bool polarity = literal.getKind() != Kind::NOT;
    Node atom = polarity ? literal : literal[0];
    Assert(atom.getKind() == Kind::STAR_CONTAINS);
    // The first child is the lambda, unless the rewriter normalized a
    // constant lambda to a function array constant, or --no-uf-lazy-ll lifted
    // it to a skolem. getDefinition recovers the lambda in all three cases.
    Node lambda = uf::FunctionConst::getDefinition(atom[0]);
    Assert(!lambda.isNull())
        << "Expected a lambda as the first child of " << atom << std::endl;
    // vectorPredicate = p[v] (v satisfies p) and nonnegative = (and (>= v_i
    // 0)).
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(atom, nm);

    // (1) Under arithLiaStarAssumeNonnegative the summands -- and hence v --
    // are taken to lie in the non-negative orthant. That only holds where the
    // atom holds, so guard the lemma with it: an unguarded lemma would be
    // treated as globally valid by the SAT solver, forcing v >= 0 in branches
    // where the atom is false and corrupting unsat cores. Without the option
    // int.star-contains constrains the sign of its summands only through the
    // lambda, so no such lemma is emitted. The lemma is an assumption rather
    // than a valid fact, so like the split and the reduction below it needs
    // justification (see RelevanceManager): the model must satisfy it.
    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      Node nonnegativeLemma = atom.impNode(nonnegative);
      d_im.addPendingLemma(nonnegativeLemma,
                           InferenceId::ARITH_LIA_STAR_NONNEGATIVE,
                           nullptr,
                           false,
                           LemmaProperty::NEEDS_JUSTIFY);
    }

    // (2) Split on whether v itself satisfies p: if so, v is a single-summand
    // member of S* and the atom holds directly. The lemma cache holds
    // rewritten lemmas, and the rewriter keeps (or p(y) (not p(y))) as is, so
    // the split is sent once per user context. The asserted side of the split
    // certifies step 3 below, so the split needs justification (see
    // RelevanceManager): relevance filtering, e.g. --nl-rlv, must keep p(y)
    // in the nonlinear model check, or the model repair could change a
    // nonlinear coordinate of y after the literal was skipped.
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    d_im.addPendingLemma(split,
                         InferenceId::ARITH_LIA_STAR_SPLIT,
                         nullptr,
                         false,
                         LemmaProperty::NEEDS_JUSTIFY);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    // (3) Model-value shortcut, for a positive literal only: if the current
    // arithmetic model already satisfies the predicate p[v], or the last star
    // under-approximation computed for the atom by the lazy strategy, then v
    // is in S* and no further refinement is needed this round. A negative
    // literal cannot be certified this way: it needs the exact reduction.
    if (polarity && options().arith.arithLiaStarModelValue)
    {
      TimerStat::CodeTimer modelValueTimer(d_stats.d_modelValueTime);
      ++d_stats.d_modelValueChecks;
      std::vector<Node> keys;
      std::vector<Node> values;

      for (const auto& [key, value] : arithModel)
      {
        keys.push_back(key);
        values.push_back(value);
      }

      Node check = vectorPredicate;
      auto starIt = d_lastStarLia.find(atom);
      if (starIt != d_lastStarLia.end())
      {
        // A model satisfying the star constraints is a witness of v in S*
        // whether or not the lemma that introduced them is still asserted:
        // the constraints are self-contained.
        check = check.orNode(starIt->second);
      }

      Node value = check.substitute(
          keys.begin(), keys.end(), values.begin(), values.end());
      value = rewrite(value);

      Trace("liastar-ext-debug") << "value: " << value << std::endl;

      if (value == d_true)
      {
        ++d_stats.d_modelValueSolved;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        Trace("liastar-ext-debug")
            << atom << " is satisfied in the current model" << std::endl;
        Trace("liastar-ext-debug")
            << "----------------------------------------" << std::endl;
        // `continue`, not `return`: this literal needs no refinement, but the
        // remaining star literals still do. Returning here left every later
        // literal unreduced -- and hence unconstrained -- for the whole check,
        // which reports sat for unsatisfiable inputs with two or more star
        // literals (see regress1/arith/liastar/two-star-predicates.smt2).
        continue;
      }
    }
    // (4) An atom is in d_negatedReductions once its exact reduction lemma
    // (= L ...) was sent in this user context. Its negative literal may still
    // need the lemma (or L (forall ...)), e.g. if L was asserted positively
    // before.
    if (d_negatedReductions.find(atom) != d_negatedReductions.end())
    {
      if (!polarity && d_negatedReductionsSent.insert(atom))
      {
        sendNegatedReduction(atom);
        d_im.doPendingLemmas();
      }
      continue;
    }
    // (5) Refine: reduce the star atom to its cone/Hilbert-basis encoding.
    if (options().arith.arithLiaStarLazy)
    {
      lazyCheckStar(atom, lambda, polarity);
    }
    else
    {
      eagerCheckStar(atom, lambda, polarity);
    }
  }
}

void LiaStarExtension::recordReduction(Node atom,
                                       Node star,
                                       const std::vector<Node>& skolems,
                                       bool polarity)
{
  // The formula for a negated atom, see the class documentation. Without
  // skolems the reduction lemma is exact and it is not needed, e.g.
  // (= L (= a 0)) for (lambda ((x Int)) false). For the running example of
  // the class documentation the negation is star negated, with bound
  // variables u and v for mu and l:
  //   (forall ((u Int) (v Int))
  //     (not (and (>= u 0) (>= v 0) (=> (= u 0) (= v 0))
  //               (= a (+ (* 2 u) v)) (= b u))))
  Node negation;
  if (!skolems.empty())
  {
    std::vector<Node> boundVars;
    for (const Node& skolem : skolems)
    {
      boundVars.push_back(NodeManager::mkBoundVar(skolem.getType()));
    }
    Node notStar = star.notNode();
    Node body = notStar.substitute(
        skolems.begin(), skolems.end(), boundVars.begin(), boundVars.end());
    Node boundVarList = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVars);
    negation = d_nm->mkNode(Kind::FORALL, boundVarList, body);
  }
  d_negatedReductions.insert(atom, negation);
  if (!polarity)
  {
    d_negatedReductionsSent.insert(atom);
    sendNegatedReduction(atom);
  }
}

void LiaStarExtension::sendNegatedReduction(Node atom)
{
  Node negation = d_negatedReductions.find(atom)->second;
  if (negation.isNull())
  {
    return;
  }
  if (!logicInfo().isQuantified())
  {
    std::stringstream ss;
    ss << "A negated int.star-contains requires quantifiers in the background "
          "logic, found "
       << atom.notNode();
    throw LogicException(ss.str());
  }
  // (or L (forall ((u Int) (v Int)) (not (and (>= u 0) ...)))), see
  // recordReduction
  Node lemma = atom.orNode(negation);
  Trace("liastar-ext") << "negated star lemma: " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_NOT_EXISTS, nullptr);
}

void LiaStarExtension::eagerCheckStar(Node atom, Node lambda, bool polarity)
{
  // Eager reduction: compute every cone of p up front and emit the exact
  // equivalence `atom = star`. Normalize p to DNF and render each disjunct as
  // a Normaliz constraint matrix.
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      convertQFLIAToMatrices(lambda);

  // Build the cones and the star constraints over all of them.
  std::vector<Node> skolems;
  auto [cones, starConstraints] = getCones(atom, pairs, skolems);

  if (TraceIsOn("liastar-ext-smt"))
  {
    // Debug only: build the per-cone membership encoding (v in S, a single
    // element) and emit (check-sat) queries asserting it is equivalent to the
    // predicate, so a separate solver run can validate the cone decomposition.
    // The actual lemma below uses `starConstraints`, not `lia`.
    std::vector<std::pair<Node, Node>> lia =
        getMembershipDisjuncts(lambda, cones);
    Trace("liastar-ext") << "lia constraint: " << std::endl;
    traceMembershipValidation(d_nm, lambda, lia);
  }
  // starConstraints has a single element if S is empty and n is 1, e.g.
  // (= a 0) for (lambda ((x Int)) false), whose star S* is {0}.
  Node star = d_nm->mkAnd(starConstraints);
  Trace("liastar-ext") << "starConstraints: " << std::endl
                       << toString(starConstraints) << std::endl;
  star = rewrite(star);
  Node lemma = atom.eqNode(star);
  Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
  // With skolems the lemma skolemizes (= L (exists ((mu Int) (l Int)) star)),
  // so like other skolemization lemmas it needs justification (see
  // RelevanceManager): a model that makes L true must satisfy the
  // constraints on mu and l. Without skolems the lemma is exact, e.g.
  // (= L (= a 0)) for (lambda ((x Int)) false), but star is still the only
  // constraint that keeps y in S*, and L itself is not an arithmetic
  // constraint. So the lemma needs justification in both cases: otherwise
  // relevance filtering, e.g. --nl-rlv, could drop star and let the
  // nonlinear model repair move y out of S*.
  d_im.addPendingLemma(lemma,
                       InferenceId::ARITH_LIA_STAR_EXISTS,
                       nullptr,
                       false,
                       LemmaProperty::NEEDS_JUSTIFY);
  ++d_stats.d_starTermsReduced;
  recordReduction(atom, star, skolems, polarity);
  d_im.doPendingLemmas();
}

LiaStarExtension::Subsolver& LiaStarExtension::getSubsolver(Node lambda)
{
  // Return the persistent incremental subsolver for `lambda`, creating and
  // seeding it on first use. It is used by the lazy strategy to enumerate the
  // convex cells of the predicate's satisfying region.
  auto it = d_subsolvers.find(lambda);
  if (it != d_subsolvers.end())
  {
    return it->second;
  }
  Subsolver& sub = d_subsolvers[lambda];

  Options subOptions;
  // we read the model below to construct the disjunct.
  subOptions.write_smt().produceModels = true;
  sub.engine = std::make_unique<SolverEngine>(d_nm, &subOptions);
  sub.engine->setIsInternalSubsolver();
  LogicInfo info("QF_LIA");
  sub.engine->setLogic(info);
  sub.engine->setOption("incremental", "true");

  // The base assertion is the membership predicate (with ites and negations
  // eliminated). Under arithLiaStarAssumeNonnegative it is additionally
  // conjoined with the non-negativity of the lambda's variables; otherwise the
  // cells must be enumerated over all of Z^n, since int.star-contains
  // constrains its summands only through the lambda. Restricting the
  // enumeration unconditionally would under-approximate the star set by every
  // cell with a negative coordinate.
  Node base = LiaStarUtils::removeItesAndNots(lambda[1], d_env, &d_stats);
  std::vector<Node> conjuncts{base};
  if (options().arith.arithLiaStarAssumeNonnegative)
  {
    for (Node var : lambda[0])
    {
      conjuncts.push_back(d_nm->mkNode(Kind::GEQ, var, d_zero));
    }
  }
  base = d_nm->mkAnd(conjuncts);

  // The lambda's bound variables appear free in `base`. A formula with free
  // (bound) variables cannot be asserted to a subsolver, so we replace them
  // with fresh free constants and remember the mapping so the disjunct built
  // from the model can be substituted back into bound-variable space.
  for (Node var : lambda[0])
  {
    if (var.getKind() == Kind::BOUND_VARIABLE)
    {
      sub.from.push_back(var);
      sub.to.push_back(d_nm->mkDummySkolem("liastar", var.getType()));
    }
  }
  if (!sub.from.empty())
  {
    base = base.substitute(
        sub.from.begin(), sub.from.end(), sub.to.begin(), sub.to.end());
  }
  sub.base = base;
  sub.engine->assertFormula(base);
  return sub;
}

void LiaStarExtension::lazyCheckStar(Node atom, Node lambda, bool polarity)
{
  // Lazy reduction: drive one refinement round for `atom`.
  if (d_completeLambdas.find(lambda) != d_completeLambdas.end())
  {
    // Every cell of the predicate has a cone already, found through another
    // atom over the same lambda or in a user context that was popped since:
    // the star over the cones is exact, so send the exact reduction.
    processDisjunct(atom, lambda, d_false, /*complete=*/true, polarity);
    return;
  }

  // The persistent incremental subsolver for this lambda. On first use it is
  // seeded with the (nonnegative) predicate.
  Subsolver& sub = getSubsolver(lambda);

  // Refine the subsolver with the cone-disjuncts discovered since the previous
  // round: assert the negation of each new disjunct, so the next model lies
  // outside every cell covered so far. Each disjunct is asserted exactly once,
  // and the subsolver keeps everything it learned about the covered regions.
  // The disjuncts are stored in bound-variable space, so map them to skolem
  // space first.
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& pairs =
      d_lazyCones[lambda];
  for (size_t i = sub.negated; i < pairs.size(); i++)
  {
    Node disjunct = pairs[i].first;
    if (!sub.from.empty())
    {
      disjunct = disjunct.substitute(
          sub.from.begin(), sub.from.end(), sub.to.begin(), sub.to.end());
    }
    sub.engine->assertFormula(disjunct.notNode());
  }
  sub.negated = pairs.size();

  lazyHilbert(atom, lambda, sub, polarity);
}

std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
          std::vector<Node>>
LiaStarExtension::getCones(
    Node n,
    const std::vector<std::pair<std::vector<std::string>, Node>>& pairs,
    std::vector<Node>& skolems)
{
  TimerStat::CodeTimer conesTimer(d_stats.d_getConesTime);
  // Eager path: build a cone for every DNF disjunct (`pairs`) and accumulate
  // the star constraints over all of them. Returns (cones, starConstraints):
  // the cones (paired with their predicate node) are used to build the
  // membership encoding for the debug trace, and starConstraints is the star
  // encoding that becomes the reduction lemma.
  std::vector<std::pair<Node, Cone<Integer>>> cones;
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;

  for (size_t i = 0; i < pairs.size(); i++)
  {
    const std::pair<std::vector<std::string>, Node>& pair = pairs[i];
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << i << std::endl
                         << pair.second << std::endl;

    Cone<Integer> cone =
        LiaStarUtils::buildCone(dimension,
                                pair.first,
                                options().arith.arithLiaStarAssumeNonnegative,
                                &d_stats);
    if (LiaStarUtils::isEmptyCone(cone))
    {
      // a disjunct without integer points contributes nothing to the star
      Trace("liastar-ext") << "empty cone" << std::endl;
      ++d_stats.d_conesEmpty;
      continue;
    }
    ++d_stats.d_conesNonempty;

    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      // Build the star encoding of this generator over fresh skolems (the
      // constraints are asserted at the top level, not under a quantifier) and
      // accumulate its side constraints and its (point, rays) contribution.
      std::vector<Node> vars, constraints;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone,
                                     /*star=*/true,
                                     /*useSkolems=*/true,
                                     d_nm,
                                     vars,
                                     constraints,
                                     point,
                                     rays);
      skolems.insert(skolems.end(), vars.begin(), vars.end());
      starConstraints.insert(
          starConstraints.end(), constraints.begin(), constraints.end());
      lambdas.push_back({point, rays});
    }
    cones.push_back({pair.second, cone});
  }

  // The star vector equals the sum of every cone's contribution.
  std::vector<Node> sums = buildSumConstraints(d_nm, d_zero, vec, lambdas);
  starConstraints.insert(starConstraints.end(), sums.begin(), sums.end());

  return std::make_pair(cones, starConstraints);
}

void LiaStarExtension::addCone(
    Node lambda, const std::pair<std::vector<std::string>, Node>& pair)
{
  // Lazy path: build the cone for a single disjunct `pair` and append it to the
  // cones accumulated so far for this lambda. An empty (infeasible) cone is
  // dropped.
  size_t dimension = lambda[0].getNumChildren();
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[lambda];

  Trace("liastar-ext") << "---------------------------" << std::endl;
  Trace("liastar-ext") << "Cone for node " << std::endl
                       << pair.second << std::endl;

  Cone<Integer> cone =
      LiaStarUtils::buildCone(dimension,
                              pair.first,
                              options().arith.arithLiaStarAssumeNonnegative,
                              &d_stats);
  if (LiaStarUtils::isEmptyCone(cone))
  {
    Trace("liastar-ext") << "empty cone" << std::endl;
    ++d_stats.d_conesEmpty;
    return;
  }
  ++d_stats.d_conesNonempty;
  cones.push_back({pair.second, cone});
}

std::vector<Node> LiaStarExtension::getStarConstraints(Node atom, Node lambda)
{
  // Lazy path: return the star constraints over all cones accumulated so far in
  // `d_lazyCones[lambda]`. The cone list is shared by every star atom over the
  // same lambda (the cones depend only on the predicate), but the multiplier
  // skolems and the constraints built over them are per *atom*: two atoms over
  // one lambda constrain different vectors, and sharing their multipliers
  // would make the sum constraints `v1 = sum` and `v2 = sum` force `v1 = v2`.
  // The per-cone constraints (and their fresh skolems) are computed once per
  // cone per atom (so the skolems are stable across refinement rounds) and
  // cached in `d_starConstraints`/`d_lambdas`; the sum constraints, which
  // span all cones, are rebuilt on each call.
  std::vector<Node> vec(atom.begin() + 1, atom.end());
  size_t dimension = vec.size();

  // the cones accumulated so far for this lambda
  std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones =
      d_lazyCones[lambda];

  // The per-cone constraints and lambdas computed in previous calls. We only
  // compute new constraints (and fresh skolems) for cones that have not been
  // processed yet, and append them here.
  std::vector<Node>& starConstraints = d_starConstraints[atom];
  std::vector<std::pair<Vector, std::vector<Vector>>>& lambdas =
      d_lambdas[atom];
  std::vector<Node>& literalSkolems = d_literalSkolems[atom];
  size_t& processed = d_processedCones[atom];

  for (; processed < cones.size(); processed++)
  {
    Cone<Integer>& cone = cones[processed].second;
    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      // Build the generator's star encoding directly over skolems: the star
      // constraints are asserted at the top level (not under a quantifier).
      std::vector<Node> vars, constraints;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone,
                                     /*star=*/true,
                                     /*useSkolems=*/true,
                                     d_nm,
                                     vars,
                                     constraints,
                                     point,
                                     rays);
      literalSkolems.insert(literalSkolems.end(), vars.begin(), vars.end());
      starConstraints.insert(
          starConstraints.end(), constraints.begin(), constraints.end());
      lambdas.push_back({point, rays});
    }
  }

  // The sum constraints span the lambdas of all cones, so they are rebuilt
  // from the accumulated lambdas on each call. Start from the persisted
  // per-cone constraints and append the freshly built sum constraints,
  // leaving `d_starConstraints` holding only the per-cone constraints.
  std::vector<Node> result = starConstraints;
  std::vector<Node> sums = buildSumConstraints(d_nm, d_zero, vec, lambdas);
  result.insert(result.end(), sums.begin(), sums.end());
  return result;
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getMembershipDisjuncts(
    Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones)
{
  TimerStat::CodeTimer liaTimer(d_stats.d_getLiaTime);
  // Build the *membership* encoding (used only for the liastar-ext-smt debug
  // trace): one disjunct per (cone, module generator) stating that the vector
  // is a single element `g + sum_k l_k h_k` of that cone, with the multipliers
  // existentially bound. The disjunction over all of these is equivalent to
  // `v in S` (single membership, not the star). Returns each disjunct paired
  // with the predicate node it came from.
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;

  for (auto& pair : cones)
  {
    Node node = pair.first;
    libnormaliz::Cone<Integer>& cone = pair.second;
    for (const auto& generator : getConeGenerators(cone, dimension))
    {
      // Build the generator's membership encoding in terms of bound variables
      // and existentially bind them.
      std::vector<Node> boundVariables, conjunctions;
      Vector point;
      std::vector<Vector> rays;
      LiaStarUtils::getGeneratorBody(dimension,
                                     generator,
                                     cone,
                                     /*star=*/false,
                                     /*useSkolems=*/false,
                                     d_nm,
                                     boundVariables,
                                     conjunctions,
                                     point,
                                     rays);

      // the vector equals this single element: vec[i] = point[i] + sum rays
      Vector sums(dimension, d_zero);
      for (size_t i = 0; i < dimension; i++)
      {
        sums[i] = rewrite(d_nm->mkNode(Kind::ADD, sums[i], point[i]));
        for (const auto& ray : rays)
        {
          sums[i] = rewrite(d_nm->mkNode(Kind::ADD, sums[i], ray[i]));
        }
      }

      for (size_t i = 0; i < dimension; i++)
      {
        conjunctions.push_back(vec[i].eqNode(sums[i]));
      }
      Node conjunction = d_nm->mkAnd(conjunctions);
      if (boundVariables.size() > 0)
      {
        Node variables = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVariables);
        conjunction = d_nm->mkNode(Kind::EXISTS, variables, conjunction);
      }
      disjunctions.push_back({node, conjunction});
    }
  }

  return disjunctions;
}

const std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  // Normalize the lambda body `p` to DNF and render each disjunct as a Normaliz
  // constraint matrix (one cone per disjunct). `n` is the lambda
  // (lambda ((x_1 Int) ... (x_n Int)) p).
  Assert(n.getKind() == Kind::LAMBDA);

  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

  traceSmtPreamble(variables, options().arith.arithLiaStarAssumeNonnegative);

  // (and (>= x 2) (= y 1)) is in DNF already, while
  //   (and (>= x 2) (or (= y 1) (>= y 3)))
  //   --> (or (and (>= x 2) (= y 1)) (and (>= x 2) (>= y 3)))
  Node dnf = LiaStarUtils::toDNF(predicate, d_env, &d_stats);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  d_stats.d_getMatricesTime.start();
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      LiaStarUtils::getMatrices(variables, dnf);
  d_stats.d_getMatricesTime.stop();
  ++d_stats.d_dnfCalls;
  d_stats.d_dnfDisjuncts += pairs.size();
  d_stats.d_dnfDisjunctsMax.maxAssign(pairs.size());
  return pairs;
}

void LiaStarExtension::lazyHilbert(Node atom,
                                   Node lambda,
                                   Subsolver& sub,
                                   bool polarity)
{
  // One lazy refinement round for `atom`. Ask the subsolver for a model in a
  // region of p not yet covered by a cone, read off the convex cell containing
  // it, and hand it to `processDisjunct` for the cone and lemma generation.
  Node variables = lambda[0];
  Trace("liastar-lazy") << "lazyHilbert::variables:" << variables << std::endl;

  traceSmtPreamble(variables, options().arith.arithLiaStarAssumeNonnegative);

  // Check the subsolver and read off the disjunct (the cell of the predicate)
  // containing the model. The subsolver already has the predicate and the
  // negations of all previously discovered cone-disjuncts asserted, so the
  // model lies in a region of the predicate not yet covered by any cone.
  ++d_stats.d_lazyRounds;
  Node disjunct = LiaStarUtils::getDisjunct(
      sub.base, sub.from, sub.to, d_env, sub.engine.get());
  // `getDisjunct` returns false when no region of `formula` is left uncovered,
  // i.e. every disjunct of the predicate already has a cone. At that point the
  // cone encoding is exact and we can assert the full equivalence.
  bool complete = disjunct == d_false;
  processDisjunct(atom, lambda, disjunct, complete, polarity);
}

void LiaStarExtension::processDisjunct(
    Node atom, Node lambda, Node disjunct, bool complete, bool polarity)
{
  // Tail of one lazy refinement round: turn the freshly discovered
  // disjunct (a cell of the predicate, in bound-variable space) into a cone,
  // rebuild the star constraints over all cones found so far, and emit a
  // (tentative or final) reduction lemma.
  Node variables = lambda[0];
  if (complete)
  {
    // every cell of the predicate has a cone: the star over the cones is
    // exact, for this and every other atom over the lambda
    d_completeLambdas.insert(lambda);
  }
  else
  {
    // The disjunct is a conjunction of arithmetic facts in the solver's
    // normal form, which can represent strict inequalities as negations (e.g.
    // (not (>= a b))). Normalize away the negations before building the
    // matrix.
    disjunct = LiaStarUtils::removeItesAndNots(disjunct, d_env, &d_stats);

    Trace("liastar-ext") << "disjunct: " << disjunct << std::endl;

    std::pair<std::vector<std::string>, Node> pair =
        LiaStarUtils::getMatrix(variables, disjunct);

    // Add the cone for the current disjunct to `d_lazyCones`.
    addCone(lambda, pair);
  }
  // The starLia constraints over the whole list of cones so far.
  // `getStarConstraints` only computes the per-cone constraints (and fresh
  // skolems) for cones not yet processed, reusing the constraints computed in
  // previous calls.
  std::vector<Node> starConstraints = getStarConstraints(atom, lambda);
  Trace("liastar-ext") << "starConstraints: " << std::endl
                       << toString(starConstraints) << std::endl;

  // starConstraints has a single element if the predicate has no cell and n
  // is 1, e.g. (= a 0) for (lambda ((x Int)) false), whose star S* is {0}.
  Node star = d_nm->mkAnd(starConstraints);

  Trace("liastar-ext") << d_lazyCones[lambda].size()
                       << " cones for lambda:  " << lambda << std::endl;

  star = rewrite(star);
  // Remember the last computed starLia under-approximation for `atom`; the
  // model-value check in checkFullEffort uses it to skip refinement when the
  // current model already satisfies it.
  d_lastStarLia[atom] = star;

  // Deactivate the guard from the previous refinement round for this atom:
  // its under-approximation is a subset of the current `star`, so the
  // tentative equivalence it guarded is subsumed. Asserting `(not g_old)`
  // makes that guarded lemma vacuous, so the solver does not have to satisfy
  // several (mutually constraining) guarded equivalences at once. Sound
  // because `g_old` is fresh.
  auto guardIt = d_lastGuard.find(atom);
  if (guardIt != d_lastGuard.end() && !(*guardIt).second.isNull())
  {
    Node deactivate = (*guardIt).second.notNode();
    d_im.addPendingLemma(
        deactivate, InferenceId::ARITH_LIA_STAR_SPLIT, nullptr);
  }

  Node lemma;
  if (complete)
  {
    // The encoding is complete, so `star` captures the star set exactly and
    // the full equivalence holds. This is what allows refuting a (positively
    // asserted) star-contains, and, with the negated reduction lemma, a
    // negatively asserted one.
    lemma = atom.eqNode(star);
    d_lastGuard.insert(atom, Node::null());
  }
  else
  {
    // While cones are still being discovered, `star` is an under-approximation
    // of the star set, so the equivalence `atom = star` is not yet sound. We
    // assert it only tentatively, implied by a fresh boolean guard `g`. The
    // split makes `g` a genuine decision literal and `preferPhase` biases it
    // to true, so the SAT solver tries the equivalence first. If assuming it
    // leads to a conflict (the atom actually holds via a not-yet-discovered
    // cone), the solver flips `g` to false, retracting the equivalence, and
    // we refine. For a negative literal the tentative equivalence is
    // harmless: the solver falsifies `star` through the fresh skolems.
    Node g = d_nm->mkDummySkolem("liastarGuard", d_nm->booleanType());
    g = d_astate.getValuation().ensureLiteral(g);
    d_im.preferPhase(g, true);
    Node split = g.orNode(g.notNode());
    d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR_SPLIT, nullptr);
    lemma = g.impNode(atom.eqNode(star));
    // Remember this guard so it can be deactivated once a later, larger
    // under-approximation subsumes it. The entry is user-context dependent,
    // like the lemma.
    d_lastGuard.insert(atom, g);
  }
  Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
  // the reduction needs justification for the same reason as the eager one,
  // see eagerCheckStar
  d_im.addPendingLemma(lemma,
                       InferenceId::ARITH_LIA_STAR_EXISTS,
                       nullptr,
                       false,
                       LemmaProperty::NEEDS_JUSTIFY);
  if (complete)
  {
    ++d_stats.d_starTermsReduced;
    recordReduction(atom, star, d_literalSkolems[atom], polarity);
  }
  d_im.doPendingLemmas();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */
