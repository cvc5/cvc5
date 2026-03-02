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
 * Extension to the theory of arithmetic handling lia star operator.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_extension.h"

#include "liastar_utils.h"
#include "libnormaliz/input.h"
#include "options/arith_options.h"
#include "options/smt_options.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/bound_inference.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/arith/theory_arith.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/evaluator.h"
#include "theory/ext_theory.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

using namespace libnormaliz;

using libnormaliz::operator<<;

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
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_checkCounter(0),
      d_extTheoryCb(),
      d_extTheory(env, d_extTheoryCb, d_im),
      d_hasLiaStarTerms(context(), false)
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
  // eliminated by context-dependent simplification.
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
  for (auto it = d_arith.facts_begin(); it != d_arith.facts_end(); ++it)
  {
    Node lit = (*it).d_assertion;
    Trace("liastar-ext") << lit << std::endl;
    if (lit.getKind() == Kind::STAR_CONTAINS)
    {
      // positive polarity of star-contains
      assertions.push_back(lit);
    }
    if (lit.getKind() == Kind::NOT && lit[0].getKind() == Kind::STAR_CONTAINS)
    {
      // negative polarity of star-contains
      assertions.push_back(lit[0]);
    }
  }
  Trace("liastar-ext") << "---------------------" << std::endl;
}

void LiaStarExtension::checkFullEffort(std::map<Node, Node>& arithModel,
                                       const std::set<Node>& termSet)
{
  // run a last call effort check
  Trace("liastar-ext") << "interceptModel: do model-based refinement"
                       << std::endl;
  Trace("liastar-ext") << " model is : " << arithModel << std::endl;
  Trace("liastar-ext") << " termSet is: " << termSet << std::endl;
  d_checkCounter++;

  // get the assertions
  std::vector<Node> assertions;
  getAssertions(assertions);

  Trace("liastar-ext") << "liastar assertions: " << assertions << std::endl;
  NodeManager* nm = nodeManager();
  for (const auto& literal : assertions)
  {
    Node lambda = literal[0];
    Assert(literal.getKind() == Kind::STAR_CONTAINS);
    auto [vectorPredicate, nonnegative] =
        LiaStarUtils::getVectorPredicate(literal, nm);
    // assert that vector elements are non negative
    d_im.addPendingLemma(nonnegative, InferenceId::ARITH_LIA_STAR_NONNEGATIVE);
    // add a spliting lemma for vector predicate
    Node split = vectorPredicate.orNode(vectorPredicate.notNode());
    d_im.addPendingLemma(split, InferenceId::ARITH_LIA_STAR_SPLIT);
    d_im.doPendingLemmas();
    if (d_im.hasSentLemma())
    {
      Trace("liastar-ext") << "Sending lemma: " << split << std::endl;
      continue;
    }
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
      Trace("liastar-ext-debug")
          << "----------------------------------------" << std::endl;
      Trace("liastar-ext-debug")
          << literal << " is satisfied in the current model" << std::endl;
      Trace("liastar-ext-debug")
          << "----------------------------------------" << std::endl;
      return;
    }
    else  //(value == d_false)
    {
      if (std::find(
              d_processedStarTerms.begin(), d_processedStarTerms.end(), literal)
          != d_processedStarTerms.end())
      {
        continue;
      }
      // more work need to be done
      std::vector<std::pair<std::vector<std::string>, Node>> pairs =
          convertQFLIAToMatrices(lambda);

      auto [cones, starConstraints] = getCones(literal, pairs);
      std::vector<std::pair<Node, Node>> lia = getLia(lambda, cones);

      Trace("liastar-ext") << "lia constraint: " << std::endl;
      if (TraceIsOn("liastar-ext-smt"))
      {
        for (size_t i = 0; i < lia.size(); i++)
        {
          Trace("liastar-ext-smt") << "(push 1)" << std::endl;
          Trace("liastar-ext-smt") << "(echo \"" << i << "\")" << std::endl;
          Trace("liastar-ext-smt") << "(assert " << std::endl
                                   << "  (distinct" << std::endl
                                   << "    ";
          Trace("liastar-ext-smt") << lia[i].first << std::endl << "    ";
          Trace("liastar-ext-smt") << lia[i].second << std::endl
                                   << "  )" << std::endl
                                   << ")" << std::endl;
          Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
          Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
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
        Trace("liastar-ext-smt") << "(push 1)" << std::endl;
        Trace("liastar-ext-smt") << "(echo \"lia formula: \")" << std::endl;
        Trace("liastar-ext-smt") << "(assert " << std::endl
                                 << "  (distinct" << std::endl
                                 << "    ";
        Trace("liastar-ext-smt") << lambda[1] << std::endl << "    ";
        Trace("liastar-ext-smt") << liaFormula << std::endl
                                 << "  )" << std::endl
                                 << ")" << std::endl;
        Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
        Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
      }
      Node star = d_nm->mkNode(Kind::AND, starConstraints);
      Trace("liastar-ext") << "starConstraints: " << std::endl
                           << toString(starConstraints) << std::endl;
      star = rewrite(star);
      Node lemma = literal.eqNode(star);
      Trace("liastar-ext") << "star lemma: " << lemma << std::endl;
      d_im.addPendingLemma(lemma, InferenceId::ARITH_LIA_STAR_EXISTS);
      d_processedStarTerms.push_back(literal);
      d_im.doPendingLemmas();
    }
  }
}

std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
          std::vector<Node>>
LiaStarExtension::getCones(
    Node n, const std::vector<std::pair<std::vector<std::string>, Node>>& pairs)
{
  std::vector<std::pair<Node, Cone<Integer>>> cones;
  std::vector<Node> vec(n.begin() + 1, n.end());
  size_t dimension = vec.size();
  std::vector<Integer> zeroVector(dimension, Integer(0));
  std::vector<std::pair<Vector, std::vector<Vector>>> lambdas;
  std::vector<Node> starConstraints;

  for (const std::pair<std::vector<std::string>, Node>& pair : pairs)
  {
    Trace("liastar-ext") << "---------------------------" << std::endl;
    Trace("liastar-ext") << "Cone for node " << std::endl
                         << pair.second << std::endl;

    libnormaliz::OptionsHandler options;

    std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
        poly_param_input;
    std::map<libnormaliz::NumParam::Param, long> num_param_input;
    std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

    libnormaliz::renf_class_ptr number_field_ref;

    std::stringstream ss;
    ss << "amb_space " << dimension << std::endl;
    ss << "constraints " << pair.first.size() << " symbolic" << std::endl;
    for (auto constraint : pair.first)
    {
      ss << constraint << std::endl;
    }
    ss << "nonnegative" << std::endl;
    ss << "HilbertBasis" << std::endl;
    ss << "ModuleGenerators" << std::endl;
    Trace("liastar-ext") << "normaliz input:" << std::endl;
    Trace("liastar-ext") << ss.str() << std::endl;

    // here we use mpq_class instead of Integer (or mpz_class)
    // because libnormaliz.so only has implementation for
    // readNormalizInput<mpq_class>
    std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
    input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                      options,
                                                      num_param_input,
                                                      bool_param_input,
                                                      poly_param_input,
                                                      number_field_ref);
    Cone<Integer> cone(input);
    cone.setNonnegative(true);
    // always use infinite precision for integers
    cone.deactivateChangeOfPrecision();
    cone.compute(ConeProperty::HilbertBasis);
    cone.compute(ConeProperty::ModuleGenerators);

    if (cone.isInhomogeneous())
    {
      // AffineDim is only computed for inhomogeneous cones
      if (cone.getAffineDim() == -1)
      {
        // the cone is empty skip.
        Trace("liastar-ext") << "empty cone" << std::endl;
        continue;
      }
    }

    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : cone.getHilbertBasis())
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
      Trace("liastar-ext") << toString(generator) << std::endl;
      Node mu = d_one;
      if (generator != zeroVector)
      {
        mu = d_nm->mkDummySkolem("mu", d_nm->integerType());
      }

      starConstraints.push_back(d_nm->mkNode(Kind::GEQ, mu, d_zero));
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        Node monomial = d_nm->mkNode(Kind::MULT, constant, mu);
        point.push_back(monomial);
      }
      std::vector<Vector> rays;
      for (const auto& basis : cone.getHilbertBasis())
      {
        Node lambda = d_nm->mkDummySkolem("l", d_nm->integerType());
        // (>= l 0)
        starConstraints.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));
        // (=> (= mu 0) (= l 0))
        starConstraints.push_back(
            d_nm->mkNode(Kind::EQUAL, mu, d_zero)
                .impNode(d_nm->mkNode(Kind::EQUAL, lambda, d_zero)));

        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = d_nm->mkNode(Kind::MULT, constant, lambda);
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }
      lambdas.push_back({point, rays});
    }
    cones.push_back({pair.second, cone});
  }

  // sum constraints
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

  return std::make_pair(cones, starConstraints);
}

std::vector<std::pair<Node, Node>> LiaStarExtension::getLia(
    Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones)
{
  Node vec = n[0];
  size_t dimension = vec.getNumChildren();
  std::vector<std::pair<Node, Node>> disjunctions;
  std::vector<Integer> zeroVector(dimension, Integer(0));

  for (auto& pair : cones)
  {
    Node node = pair.first;
    libnormaliz::Cone<Integer> cone = pair.second;
    Trace("liastar-ext") << "Hilbert basis:" << std::endl;
    for (const auto& basis : cone.getHilbertBasis())
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
      Vector point;
      for (const auto& element : generator)
      {
        Node constant = d_nm->mkConstInt(Rational(element));
        point.push_back(constant);
      }

      std::vector<Vector> rays;
      std::vector<Node> boundVariables;
      auto bases = cone.getHilbertBasis();
      for (size_t index = 0; index < bases.size(); index++)
      {
        auto basis = bases[index];
        std::string name = "l" + std::to_string(index + 1);
        Node lambda = d_nm->mkBoundVar(name, d_nm->integerType());
        boundVariables.push_back(lambda);
        // (>= l 0)
        conjunctions.push_back(d_nm->mkNode(Kind::GEQ, lambda, d_zero));

        Vector ray;
        for (const auto& element : basis)
        {
          Node constant = d_nm->mkConstInt(Rational(element));
          Node monomial = rewrite(d_nm->mkNode(Kind::MULT, constant, lambda));
          ray.push_back(monomial);
        }
        rays.push_back(ray);
      }

      // sum constraints
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
      Node conjunction = d_nm->mkNode(Kind::AND, conjunctions);
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

Node LiaStarExtension::isNotZeroVector(Node v)
{
  std::vector<Node> elements = datatypes::TupleUtils::getTupleElements(v);
  Node notZero = d_false;
  for (Node element : elements)
  {
    notZero = notZero.orNode(element.eqNode(d_zero).notNode());
  }
  Trace("liastar-ext") << v << " is not zero: " << notZero << std::endl;
  return notZero;
}

const std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarExtension::convertQFLIAToMatrices(Node n)
{
  Assert(n.getKind() == Kind::LAMBDA);

  Node variables = n[0];
  Node predicate = n[1];
  Trace("liastar-ext") << "convertQFLIAToMatrices::n: " << n << std::endl;
  Trace("liastar-ext") << "variables: " << variables << std::endl;

  Trace("liastar-ext") << "predicate: " << predicate << std::endl;

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
  }

  Node dnf = LiaStarUtils::toDNF(predicate, &d_env);

  Trace("liastar-ext") << "predicate in dnf: " << dnf << std::endl;
  Trace("liastar-ext") << "lia constraint: " << std::endl;

  std::vector<std::pair<std::vector<std::string>, Node>> pairs =
      getMatrices(variables, dnf);
  return pairs;
}

std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarExtension::getMatrices(Node variables, Node n)
{
  Assert(n.getType().isBoolean()) << "n: " << n << std::endl;
  std::vector<std::pair<std::vector<std::string>, Node>> pairs;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      //
      linear::Polynomial l = linear::Polynomial::parsePolynomial(n[0]);
      linear::Polynomial r = linear::Polynomial::parsePolynomial(n[1]);
      std::string lTerm = getString(variables, l);
      std::string rTerm = getString(variables, r);
      std::string kString = k == Kind::LT    ? " < "
                            : k == Kind::GT  ? " > "
                            : k == Kind::LEQ ? " <= "
                            : k == Kind::GEQ ? " >= "
                                             : " = ";
      std::string constraint = lTerm + kString + rTerm + ";";
      std::vector<std::string> constraints;
      constraints.push_back(constraint);
      pairs.push_back({constraints, n});
      return pairs;
    }
    case Kind::AND:
    {
      std::vector<std::string> constraints;
      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        std::vector<std::pair<std::vector<std::string>, Node>> m =
            getMatrices(variables, n[i]);
        constraints.push_back(m[0].first[0]);
      }
      pairs.push_back({constraints, n});
      return pairs;
    }
    case Kind::OR:
    {
      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        std::vector<std::pair<std::vector<std::string>, Node>> m =
            getMatrices(variables, n[i]);
        pairs.push_back(m[0]);
        Trace("liastar-ext")
            << "Disjunction " << i << ": " << n[i] << std::endl;
      }
      return pairs;
    }

    default: break;
  }
  return pairs;
}

std::string LiaStarExtension::getString(Node variables, linear::Polynomial& p)
{
  Assert(variables.getKind() == Kind::BOUND_VAR_LIST)
      << "variables: " << variables << std::endl;

  size_t size = variables.getNumChildren();
  Assert(p.isIntegral()) << p.getNode() << " is expected to be linear"
                         << std::endl;
  std::stringstream ss;
  int index = 0;
  for (const linear::Monomial& monomial : p)
  {
    Trace("liastar-ext-debug")
        << "monomial: " << monomial.getNode() << std::endl;
    linear::Constant c = monomial.getConstant();
    Trace("liastar-ext-debug") << "c: " << c.getNode() << std::endl;
    Rational r = c.getValue().abs();

    // print the sign
    if (c.isNegative())
    {
      ss << " - ";
    }
    else if (index > 0)
    {
      ss << " + ";
    }
    index++;

    if (monomial.isConstant())
    {
      ss << r;
      continue;
    }
    if (r != Rational(1))
    {
      ss << r;
    }
    // find the variable
    for (size_t i = 0; i < size; i++)
    {
      linear::VarList varList = monomial.getVarList();
      for (const auto& var : varList)
      {
        if (var.getNode() == variables[i])
        {
          ss << "x[" << i + 1 << "]";
        }
      }
    }
  }
  Trace("liastar-ext-debug") << "polynomial  : " << p.getNode() << std::endl;
  Trace("liastar-ext-debug") << "string : " << ss.str() << std::endl;
  return ss.str();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */