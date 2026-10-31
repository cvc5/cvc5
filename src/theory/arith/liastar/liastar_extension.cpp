/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Extension to the theory of arithmetic handling lia star operator.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

#include "liastar_utils.h"
#include "libnormaliz/input.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "smt/logic_exception.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/evaluator.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
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

LiaStarExtension::LiaStarExtension(Env& env, TheoryArith& containing)
    : EnvObj(env),
      d_nm(nodeManager()),
      d_arith(containing),
      d_im(containing.getInferenceManager()),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasLiaStarTerms(context(), false),
      d_negatedReductions(userContext()),
      d_negatedReductionsSent(userContext()),
      d_stats(statisticsRegistry())
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
  // (int.star-contains k a b), where k is the skolem by which lambda lifting
  // replaced the lambda.
  if (d_extTheory.hasFunctionKind(n.getKind()))
  {
    d_hasLiaStarTerms = true;
    d_extTheory.registerTerm(n);
  }
}

void LiaStarExtension::getAssertions(std::vector<Node>& assertions)
{
  Trace("liastar-ext") << "Getting assertions..." << std::endl;
  Trace("liastar-ext") << "---------------------" << std::endl;
  // of the facts (int.star-contains k a b), (>= b 2) and (not (= b 1)) only
  // the first is collected
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
  d_stats.d_checkFullEffortTime.start();
  // The steps 1-4 below are those documented in liastar_extension.h. The
  // examples follow the literal of the class documentation
  //   L = (int.star-contains k a b)
  // where k is the skolem by which lambda lifting replaced the lambda
  //   (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
  // of S = {(x, y) | x >= 2 and y = 1}, asserted together with (>= b 2).
  // The first call sends the split of step 2, the second, with arithModel
  // {a -> 2, b -> 2}, the reduction lemma of step 4, and later calls find
  // that L was reduced already.
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  ++d_stats.d_checkRuns;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);
  d_stats.d_starContainsLiterals += assertions.size();

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    // literal is L, or (not L) for a negative literal, and atom is L
    bool polarity = literal.getKind() != Kind::NOT;
    Node atom = polarity ? literal : literal[0];
    Assert(atom.getKind() == Kind::STAR_CONTAINS);
    // The first child may have been purified into a skolem by lambda
    // lifting, and the rewriter may normalize a constant lambda to a
    // function array constant; recover the lambda from either form:
    // k --> (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
    Node lambda = uf::FunctionConst::getDefinition(atom[0]);
    Assert(!lambda.isNull())
        << "Expected a lambda as the first child of " << atom << std::endl;
    // vectorPredicate is p(y) = (and (>= a 2) (= b 1)), and nonnegative is
    // (and (and true (>= a 0)) (>= b 0))
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(atom, nm);

    // 1. y is nonnegative
    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      // assert that vector elements are non negative. The nonnegativity
      // only holds under the originating star-contains literal, so guard
      // the lemma with it: an unguarded lemma would be treated as valid
      // by the SAT solver, corrupting unsat cores and other contexts
      // where the literal does not hold.
      //   (=> L (and (and true (>= a 0)) (>= b 0)))
      Node lemma = atom.impNode(nonnegative);
      d_im.addPendingLemma(
          lemma, InferenceId::ARITH_LIA_STAR_NONNEGATIVE, nullptr);
    }
    // 2. split on p(y):
    //   (or (and (>= a 2) (= b 1)) (not (and (>= a 2) (= b 1))))
    // The lemma cache holds rewritten lemmas, and the rewriter keeps
    // (or p(y) (not p(y))) as is, so the split is sent once per user
    // context. It only rewrites to the cached true when p(y) is a constant,
    // e.g. for a constant y, which leaves nothing to split.
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR_SPLIT, nullptr);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
    // 3. skip a positive literal if p(y) holds in the model, since then y is
    // in S*. A negative literal is then false, which step 4 refutes. The
    // model {a -> 2, b -> 2} gives (and (>= 2 2) (= 2 1)), which rewrites to
    // false, so L goes on to step 4. The model {a -> 3, b -> 1} would give
    // true, since (3, 1) is in S.
    if (polarity && options().arith.arithLiaStarModelValue)
    {
      d_stats.d_modelValueTime.start();
      ++d_stats.d_modelValueChecks;
      std::vector<Node> keys;
      std::vector<Node> values;

      for (const auto& [key, value] : arithModel)
      {
        keys.push_back(key);
        values.push_back(value);
      }

      Node value = vectorPredicate.substitute(
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
        d_stats.d_modelValueTime.stop();
        continue;
      }
      d_stats.d_modelValueTime.stop();
    }

    // 4. the reduction lemmas, each sent once per atom. An atom is in
    // d_negatedReductions once its lemma (= L ...) was sent, as in the
    // calls after the second. Its negative literal may still need the lemma
    // (or L (forall ...)), e.g. if L was asserted positively before.
    if (d_negatedReductions.find(atom) != d_negatedReductions.end())
    {
      if (!polarity && d_negatedReductionsSent.insert(atom))
      {
        sendNegatedReduction(atom);
        d_im.doPendingLemmas();
      }
      continue;
    }
    // one pair per disjunct of p, here the single pair of
    // {"x[1] >= 2;", "x[2] = 1;"} and (and (>= x 2) (= y 1))
    std::vector<std::pair<std::vector<std::string>, Node>> pairs =
        convertQFLIAToMatrices(lambda);

    // Normaliz finds the module generator (2 1 1) and the Hilbert basis
    // {(1 0 0)} for the disjunct, so cones has its one cone, skolems becomes
    // {mu, l} and starConstraints
    //   (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
    //   (= a (+ (+ 0 (* 2 mu)) (* 1 l))) (= b (+ (+ 0 (* 1 mu)) (* 0 l)))
    std::vector<Node> skolems;
    auto [cones, starConstraints] = getCones(atom, pairs, skolems);

    Trace("liastar-ext") << "lia constraint: " << std::endl;
    // print SMT-LIB queries comparing each linear set with its disjunct
    // (equivalent when the disjunct has one module generator) and p with the
    // union of all linear sets, see LiaStarUtils::traceEquivalenceCheck. Here
    // lia has the single pair of (and (>= x 2) (= y 1)) and
    //   (exists ((l1 Int)) (and (>= l1 0) (= x (+ 2 l1)) (= y 1)))
    if (TraceIsOn("liastar-ext-smt"))
    {
      std::vector<std::pair<Node, Node>> lia = getLia(lambda, cones);
      for (size_t i = 0; i < lia.size(); i++)
      {
        LiaStarUtils::traceEquivalenceCheck(
            std::to_string(i).c_str(), lia[i].first, lia[i].second);
      }
      std::vector<Node> disjunctions;
      std::transform(lia.begin(),
                     lia.end(),
                     std::back_inserter(disjunctions),
                     [](auto& p) { return p.second; });
      Node liaFormula;
      if (disjunctions.size() == 0)
      {
        liaFormula = d_false;
      }
      else if (disjunctions.size() == 1)
      {
        liaFormula = disjunctions[0];
      }
      else
      {
        liaFormula = d_nm->mkNode(Kind::OR, disjunctions);
      }
      LiaStarUtils::traceEquivalenceCheck("lia formula", lambda[1], liaFormula);
    }
    // starConstraints has a single element if S is empty and n is 1, e.g.
    // (= a 0) for (lambda ((x Int)) false), whose star S* is {0}. Here star
    // rewrites to
    //   (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
    //        (= a (+ (* 2 mu) l)) (= b mu))
    // and the lemma is (= L star)
    Node star = d_nm->mkAnd(starConstraints);
    Trace("liastar-ext") << "starConstraints: " << std::endl
                         << toString(starConstraints) << std::endl;
    star = rewrite(star);
    Node lemma = atom.eqNode(star);
    Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
    d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_EXISTS, nullptr);
    ++d_stats.d_starTermsReduced;
    // the lemma for a negated atom, see the class documentation. Without
    // skolems the lemma above is exact and it is not needed, e.g.
    // (= L (= a 0)) for (lambda ((x Int)) false). Here negation is star
    // negated, with bound variables u and v for mu and l:
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
    d_im.doPendingLemmas();
  }
  d_stats.d_checkFullEffortTime.stop();
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
  // checkFullEffort
  Node lemma = atom.orNode(negation);
  Trace("liastar-ext") << "negated star lemma: " << lemma << std::endl;
  d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_NOT_EXISTS, nullptr);
}

std::vector<std::vector<Integer>>
LiaStarExtension::getHilbertBasisWithLineality(libnormaliz::Cone<Integer>& cone,
                                               size_t& numPointed)
{
  // For (and (>= x 2) (= y 1)) the Hilbert basis is {(1 0 0)} and the
  // maximal subspace is empty, so the result is {(1 0 0)} with numPointed 1.
  // For (= (+ x y) 2), whose integer points are (1, 1) + (1, -1)*Z, the
  // Hilbert basis is empty and the maximal subspace is {(1 -1 0)}, so the
  // result is {(1 -1 0)} with numPointed 0. The last coordinate of these
  // vectors is the homogenizing one, see getCones.
  std::vector<std::vector<Integer>> basis = cone.getHilbertBasis();
  numPointed = basis.size();
  for (const std::vector<Integer>& generator : cone.getMaximalSubspace())
  {
    basis.push_back(generator);
  }
  return basis;
}

std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
          std::vector<Node>>
LiaStarExtension::getCones(
    Node n,
    const std::vector<std::pair<std::vector<std::string>, Node>>& pairs,
    std::vector<Node>& skolems)
{
  d_stats.d_getConesTime.start();
  // The examples follow n = (int.star-contains k a b) for the lambda
  // (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1))), see checkFullEffort.
  std::vector<std::pair<Node, Cone<Integer>>> cones;
  // the vector y = (a b), so dimension is 2 and zeroVector is (0 0)
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  d_stats.d_dimensionMax.maxAssign(dimension);
  std::vector<Integer> zeroVector(dimension, Integer(0));
  // one pair per linear set: its module generator times mu, and each vector
  // of its Hilbert basis times its l, here the single pair of
  //   ((* 2 mu) (* 1 mu) (* 1 mu)) and {((* 1 l) (* 0 l) (* 0 l))}
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;
  const bool assumeNonnegative = options().arith.arithLiaStarAssumeNonnegative;

  for (size_t i = 0; i < pairs.size(); i++)
  {
    // the constraints of a disjunct and the disjunct, here
    // {"x[1] >= 2;", "x[2] = 1;"} and (and (>= x 2) (= y 1))
    const std::pair<std::vector<std::string>, Node>& pair = pairs[i];
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << i << std::endl
                         << pair.second << std::endl;

    libnormaliz::OptionsHandler options;

    std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
        poly_param_input;
    std::map<libnormaliz::NumParam::Param, long> num_param_input;
    std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

    libnormaliz::renf_class_ptr number_field_ref;

    // the input for the disjunct (and (>= x 2) (= y 1)) is
    //   amb_space 2
    //   constraints 2 symbolic
    //   x[1] >= 2;
    //   x[2] = 1;
    //   signs
    //   0 0
    //   HilbertBasis
    //   ModuleGenerators
    std::stringstream ss;
    ss << "amb_space " << dimension << std::endl;
    ss << "constraints " << pair.first.size() << " symbolic" << std::endl;
    for (auto constraint : pair.first)
    {
      ss << constraint << std::endl;
    }
    if (assumeNonnegative)
    {
      ss << "nonnegative" << std::endl;
    }
    else
    {
      // nonnegativity is not assumed so declare every coordinate
      // sign-unrestricted
      // signs is a vector with entries in {−1, 0, 1}.
      // The entry 1 at the i-th component means x_i >= 0,
      // and entry -1 at the i-th component means x_i <= 0
      // The entry 0 does not impose an inequality.
      ss << "signs" << std::endl;
      for (size_t sj = 0; sj < dimension; sj++)
      {
        ss << (sj == 0 ? "" : " ") << "0";
      }
      ss << std::endl;
    }
    ss << "HilbertBasis" << std::endl;
    ss << "ModuleGenerators" << std::endl;
    Trace("liastar-ext") << "normaliz input:" << std::endl;
    Trace("liastar-ext") << ss.str() << std::endl;

    // here we use mpq_class instead of Integer (or mpz_class)
    // because libnormaliz.so only has implementation for
    // readNormalizInput<mpq_class>
    std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
    d_stats.d_normalizInputTime.start();
    input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                      options,
                                                      num_param_input,
                                                      bool_param_input,
                                                      poly_param_input,
                                                      number_field_ref);
    d_stats.d_normalizInputTime.stop();
    ++d_stats.d_normalizCalls;
    d_stats.d_normalizComputeTime.start();
    Cone<Integer> cone(input);
    if (assumeNonnegative)
    {
      cone.setNonnegative(true);
    }
    else
    {
      cone.setNonnegative(false);
    }
    // always use infinite precision for integers
    cone.deactivateChangeOfPrecision();
    cone.compute(ConeProperty::HilbertBasis);
    cone.compute(ConeProperty::ModuleGenerators);
    // completes the Hilbert basis for a non-pointed cone
    cone.compute(ConeProperty::MaximalSubspace);
    d_stats.d_normalizComputeTime.stop();

    // A polyhedron has integer points exactly when it has module generators.
    // Its affine dimension does not tell: the polyhedron of
    // (and (= x (* 2 z)) (= x (+ (* 2 w) 1))) has rational points but no
    // integer points, so its affine dimension is not -1. The disjunct false,
    // with the constraint "1 = 0;", is skipped here too.
    if (cone.isInhomogeneous() && cone.getModuleGenerators().empty())
    {
      // the polyhedron has no integer points, skip it
      Trace("liastar-ext") << "empty cone" << std::endl;
      ++d_stats.d_conesEmpty;
      continue;
    }
    ++d_stats.d_conesNonempty;
    size_t numPointed = 0;
    const std::vector<std::vector<Integer>> hilbertBasis =
        getHilbertBasisWithLineality(cone, numPointed);
    d_stats.d_hilbertBasisTotal += hilbertBasis.size();
    d_stats.d_hilbertBasisMax.maxAssign(hilbertBasis.size());
    d_stats.d_moduleGeneratorsTotal += cone.getModuleGenerators().size();
    d_stats.d_moduleGeneratorsMax.maxAssign(cone.getModuleGenerators().size());

    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : hilbertBasis)
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }

    Trace("liastar-ext") << "Module generators:" << std::endl;
    // A cone has no module generators: its integer points are 0 + H*N + M*Z.
    // For a polyhedron, Normaliz appends a homogenizing coordinate to each
    // vector, e.g. the module generator 2 1 1 and the Hilbert basis element
    // 1 0 0 for (and (>= x 2) (= y 1)); the sums below ignore it. The cone
    // (and (>= x y) (>= y 0)) has the Hilbert basis {(1 0), (1 1)}, without
    // a homogenizing coordinate, and generators is {(0 0)}.
    std::vector<std::vector<Integer>> generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      generators = cone.getModuleGenerators();
    }
    for (const auto& generator : generators)
    {
      Trace("liastar-ext") << toString(generator) << std::endl;
      // the star of 0 + H*N + M*Z is itself, so mu is 1 for the zero
      // generator, and a fresh skolem mu otherwise, e.g. for (2 1 1)
      Node mu = d_one;
      if (generator != zeroVector)
      {
        mu = d_nm->mkDummySkolem("mu", d_nm->integerType());
        skolems.push_back(mu);
      }

      // (>= mu 0), which rewrites to true for mu = 1
      starConstraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
      // the generator times mu: ((* 2 mu) (* 1 mu) (* 1 mu)) for (2 1 1)
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element.get_str()));
        Node monomial = d_nm->mkNode(Kind::MULT, constant, mu);
        point.push_back(monomial);
      }
      std::vector<Vector> rays;
      for (size_t j = 0; j < hilbertBasis.size(); j++)
      {
        const std::vector<Integer>& basis = hilbertBasis[j];
        // the multiplier l of basis, e.g. of (1 0 0)
        Node lambda = d_nm->mkDummySkolem("l", d_nm->integerType());
        skolems.push_back(lambda);
        if (j < numPointed)
        {
          // (>= l 0), except for a direction of the maximal subspace, which
          // has any sign, e.g. (1 -1 0) for (= (+ x y) 2), see
          // getHilbertBasisWithLineality
          starConstraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }
        // (=> (= mu 0) (= l 0)), the rays of a linear set may only be used
        // together with its generator
        starConstraints.push_back(
            d_nm->mkNode(Kind::EQUAL, mu, d_zero)
                .impNode(d_nm->mkNode(Kind::EQUAL, lambda, d_zero)));

        // basis times l: ((* 1 l) (* 0 l) (* 0 l)) for (1 0 0)
        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element.get_str()));
          Node monomial = d_nm->mkNode(Kind::MULT, constant, lambda);
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }
      lambdas.push_back({point, rays});
    }
    cones.push_back({pair.second, cone});
  }

  // y_i is the sum of the i-th coordinates of all points and rays, here
  //   (= a (+ (+ 0 (* 2 mu)) (* 1 l))) and (= b (+ (+ 0 (* 1 mu)) (* 0 l)))
  // The homogenizing coordinate (* 1 mu) of the point is left out.
  Vector sums(dimension, d_zero);
  for (const std::pair<Vector, std::vector<Vector>>& pair : lambdas)
  {
    for (size_t i = 0; i < dimension; i++)
    {
      sums[i] = d_nm->mkNode(Kind::ADD, sums[i], pair.first[i]);
      for (const auto& ray : pair.second)
      {
        sums[i] = d_nm->mkNode(Kind::ADD, sums[i], ray[i]);
      }
    }
  }

  for (size_t i = 0; i < dimension; i++)
  {
    starConstraints.push_back(vec[i].eqNode(sums[i]));
  }

  d_stats.d_getConesTime.stop();
  return std::make_pair(cones, starConstraints);
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getLia(
    Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones)
{
  d_stats.d_getLiaTime.start();
  // The examples follow the lambda n of checkFullEffort, whose variables vec
  // are (x y), and its disjunct (and (>= x 2) (= y 1)) with the module
  // generator (2 1 1) and the Hilbert basis {(1 0 0)}.
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;
  std::vector<Integer> zeroVector(dimension, Integer(0));

  for (auto& pair : cones)
  {
    Node node = pair.first;
    libnormaliz::Cone<Integer> cone = pair.second;
    size_t numPointed = 0;
    const std::vector<std::vector<Integer>> hilbertBasis =
        getHilbertBasisWithLineality(cone, numPointed);
    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : hilbertBasis)
    {
      Trace("liastar-ext") << toString(basis) << std::endl;
    }

    Trace("liastar-ext") << "Module generators:" << std::endl;
    std::vector<std::vector<Integer>> generators = {zeroVector};
    if (cone.getModuleGenerators().size() > 0)
    {
      generators = cone.getModuleGenerators();
    }
    for (const auto& generator : generators)
    {
      std::vector<Node> conjunctions;
      // the generator as constants: (2 1 1)
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element.get_str()));
        point.push_back(constant);
      }

      std::vector<Vector> rays;
      // the bound variables l1, ..., lk, here l1 for (1 0 0)
      std::vector<Node> boundVariables;
      for (size_t index = 0; index < hilbertBasis.size(); index++)
      {
        const std::vector<Integer>& basis = hilbertBasis[index];
        std::string name = "l" + std::to_string(index + 1);
        Node lambda = d_nm->mkBoundVar(name, d_nm->integerType());
        boundVariables.push_back(lambda);
        if (index < numPointed)
        {
          // (>= l1 0), except for a direction of the maximal subspace, which
          // has any sign
          conjunctions.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        }

        // basis times l1, rewritten: (l1 0 0) for (1 0 0)
        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element.get_str()));
          Node monomial = rewrite(d_nm->mkNode(Kind::MULT, constant, lambda));
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }

      // x_i = g_i + h_1i * l1 + ... + h_ki * lk, here (+ 2 l1) for x and 1
      // for y
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
      // (and (>= l1 0) (= x (+ 2 l1)) (= y 1)), then
      // (exists ((l1 Int)) (and (>= l1 0) (= x (+ 2 l1)) (= y 1)))
      Node conjunction;
      if (conjunctions.size() == 1)
      {
        conjunction = conjunctions[0];
      }
      else
      {
        conjunction = d_nm->mkNode(Kind::AND, conjunctions);
      }
      if (boundVariables.size() > 0)
      {
        Node variables = d_nm->mkNode(Kind::BOUND_VAR_LIST, boundVariables);
        conjunction = d_nm->mkNode(Kind::EXISTS, variables, conjunction);
      }
      disjunctions.push_back({node, conjunction});
    }
  }

  d_stats.d_getLiaTime.stop();
  return disjunctions;
}

const std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  Assert(n.getKind() == Kind::LAMBDA);

  // for n = (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1))), variables is
  // ((x Int) (y Int)) and predicate is (and (>= x 2) (= y 1))
  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

  // print the preamble of the liastar-ext-smt queries, which declares the
  // variables of the lambda. Normaliz only assumes them to be nonnegative
  // with --arith-liastar-assume-nonnegative, and so do the queries.
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
    if (options().arith.arithLiaStarAssumeNonnegative)
    {
      for (Node var : variables)
      {
        Trace("liastar-ext-smt")
            << "(assert (>= " << var << " 0))" << std::endl;
      }
    }
  }

  // (and (>= x 2) (= y 1)) is in DNF already, while
  //   (and (>= x 2) (or (= y 1) (>= y 3)))
  //   --> (or (and (>= x 2) (= y 1)) (and (>= x 2) (>= y 3)))
  Node dnf = LiaStarUtils::toDNF(predicate, d_env, &d_stats);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  // the single pair of {"x[1] >= 2;", "x[2] = 1;"} and the disjunct
  // (and (>= x 2) (= y 1))
  d_stats.d_getMatricesTime.start();
  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      LiaStarUtils::getMatrices(variables, dnf);
  d_stats.d_getMatricesTime.stop();
  ++d_stats.d_dnfCalls;
  d_stats.d_dnfDisjuncts += pairs.size();
  d_stats.d_dnfDisjunctsMax.maxAssign(pairs.size());
  return pairs;
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */