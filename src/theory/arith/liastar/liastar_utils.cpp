/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for liastar extension.
 */

#ifdef CVC5_USE_NORMALIZ

#include "liastar_utils.h"

#include "expr/algorithm/flatten.h"
#include "expr/node_algorithm.h"
#include "libnormaliz/input.h"
#include "libnormaliz/libnormaliz.h"
#include "options/arith_options.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/rewriter.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

using namespace libnormaliz;

// prints a std::vector<std::string>, see normalizCheckSat
using libnormaliz::operator<<;

std::pair<Node, Node> LiaStarUtils::getVectorPredicate(Node n, NodeManager* nm)
{
  Assert(n.getKind() == Kind::STAR_CONTAINS);
  // The first child may have been purified into a skolem by lambda
  // lifting, and the rewriter may normalize a constant lambda to a
  // function array constant; recover the lambda from either form.
  Node lambda = uf::FunctionConst::getDefinition(n[0]);
  Assert(!lambda.isNull()) << "Expected a lambda as the first child of " << n
                           << std::endl;
  // n = (int.star-contains (lambda ((u Int) (v Int)) (>= u v)) x y)
  // vars = (u v), vecElements = (x y)
  std::vector<Node> vars(lambda[0].begin(), lambda[0].end());
  std::vector<Node> vecElements(n.begin() + 1, n.end());

  // substitute = (>= x y)
  Node substitute = lambda[1].substitute(
      vars.begin(), vars.end(), vecElements.begin(), vecElements.end());

  Trace("liastar-ext-debug") << "n: " << n << std::endl;
  Trace("liastar-ext-debug") << "predicate : " << lambda[1] << std::endl;
  // nonnegativeConstraints = (and (and true (>= x 0)) (>= y 0))
  Node nonnegativeConstraints = nm->mkConst<bool>(true);
  for (const auto& v : vecElements)
  {
    Node nonnegative = nm->mkNode(Kind::GEQ, v, nm->mkConstInt(Rational(0)));
    nonnegativeConstraints = nonnegativeConstraints.andNode(nonnegative);
  }
  Trace("liastar-ext-debug") << "substitute: " << substitute << std::endl;
  return std::make_pair(substitute, nonnegativeConstraints);
}

Result LiaStarUtils::areAssertionsUnsat(const std::vector<Node>& assertions,
                                        Env* e,
                                        LiaStarStatistics* stats)
{
  // pruning is disabled: report "not known to be unsat"
  if (!e->getOptions().arith.arithLiaStarSubSolver)
  {
    return Result();
  }
  if (stats)
  {
    ++stats->d_subSolverCalls;
    stats->d_subSolverTime.start();
  }
  NodeManager* nm = e->getNodeManager();
  // {(>= x 1), (<= x 0)} --> (and (>= x 1) (<= x 0))
  Node assertion;
  if (assertions.size() == 1)
  {
    assertion = assertions[0];
  }
  else
  {
    assertion = nm->mkNode(Kind::AND, assertions);
  }
  // the unknowns of the check, here {x}
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(assertion, fvs);
  std::vector<Node> freeVariables(fvs.begin(), fvs.end());
  Result result;
  // Normaliz needs at least one coordinate, so ground assertions go to cvc5
  if (fvs.size() > 0 && e->getOptions().arith.arithLiaStarNormalizAsSubSolver)
  {
    // the coordinates of the Normaliz space: x is x[1]
    Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, freeVariables);
    // one atom per conjunct, as getMatrices expects:
    // (and a (and b c)) --> (and a b c)
    assertion = expr::algorithm::flatten(nm, assertion);
    result =
        normalizCheckSat(variables,
                         assertion,
                         e->getOptions().arith.arithLiaStarAssumeNonnegative,
                         stats);
  }
  else
  {
    result = cvc5CheckSat(freeVariables, assertion, e, stats);
  }
  if (stats)
  {
    switch (result.getStatus())
    {
      case Result::Status::SAT: ++stats->d_subSolverSat; break;
      case Result::Status::UNSAT: ++stats->d_subSolverUnsat; break;
      default: ++stats->d_subSolverUnknown; break;
    }
    stats->d_subSolverTime.stop();
  }
  return result;
}

Result LiaStarUtils::cvc5CheckSat(const std::vector<Node>& freeVariables,
                                  Node assertion,
                                  Env* e,
                                  LiaStarStatistics* stats)
{
  if (stats) stats->d_cvc5SubSolverTime.start();
  // default options rather than e's; the logic is still e's
  Options subOptions;
  SubsolverSetupInfo ssi(*e, subOptions);

  Result result;
  if (freeVariables.size() == 0)
  {
    result = checkWithSubsolver(assertion, ssi);
  }
  else
  {
    NodeManager* nm = e->getNodeManager();
    // by default nonnegativity is not assumed: the star-contains lambda
    // body (part of `assertion`) carries the user's constraints.
    // With the option: (and (and A (>= x 0)) (>= y 0)).
    if (e->getOptions().arith.arithLiaStarAssumeNonnegative)
    {
      Node zero = nm->mkConstInt(Rational(0));
      for (Node var : freeVariables)
      {
        assertion = assertion.andNode(nm->mkNode(Kind::GEQ, var, zero));
      }
    }
    // the unknowns are bound variables, which cannot occur free in an
    // assertion: check (exists ((x Int)) (and (>= x 1) (<= x 0)))
    Node boundVariables = nm->mkNode(Kind::BOUND_VAR_LIST, freeVariables);
    Node exists = nm->mkNode(Kind::EXISTS, boundVariables, assertion);
    result = checkWithSubsolver(exists, ssi);
  }
  Trace("liastar-ext-cvc5CheckSat")
      << "Conjunction: " << assertion << " is " << result << std::endl;
  if (stats) stats->d_cvc5SubSolverTime.stop();
  return result;
}

Result LiaStarUtils::normalizCheckSat(Node variables,
                                      Node assertion,
                                      bool assumeNonnegative,
                                      LiaStarStatistics* stats)
{
  if (stats) stats->d_normalizSubSolverTime.start();
  Trace("liastar-normalizCheckSat")
      << "---------------------------" << std::endl;
  Trace("liastar-normalizCheckSat")
      << "Cone for node: " << assertion << std::endl;

  // required by readNormalizInput, unused otherwise
  libnormaliz::OptionsHandler options;

  std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
      poly_param_input;
  std::map<libnormaliz::NumParam::Param, long> num_param_input;
  std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

  libnormaliz::renf_class_ptr number_field_ref;

  // Normaliz input for (and (>= x 1) (<= x 0)) over (x):
  //   amb_space 1
  //   constraints 2 symbolic
  //   x[1] >= 1; x[1] <= 0;
  //   signs
  //   0
  //   HilbertBasis
  //   ModuleGenerators
  std::stringstream ss;
  ss << "amb_space " << variables.getNumChildren() << std::endl;
  // one constraint per conjunct
  ss << "constraints "
     << (assertion.getKind() == Kind::AND ? assertion.getNumChildren() : 1)
     << " symbolic" << std::endl;
  if (stats) stats->d_getMatricesTime.start();
  const std::vector<std::pair<std::vector<std::string>, Node>> matrices =
      getMatrices(variables, assertion);
  if (stats) stats->d_getMatricesTime.stop();

  // assertion is a conjunction, so getMatrices returns a single matrix
  ss << matrices[0].first << std::endl;

  if (assumeNonnegative)
  {
    ss << "nonnegative" << std::endl;
  }
  else
  {
    // Normaliz restricts constraint-only input to the nonnegative orthant
    // by default. Sign 0 makes a coordinate unrestricted: "0 0" for (x y).
    ss << "signs" << std::endl;
    for (size_t sj = 0; sj < variables.getNumChildren(); sj++)
    {
      ss << (sj == 0 ? "" : " ") << "0";
    }
    ss << std::endl;
  }
  // the integer solutions are the module generators plus nonnegative
  // integer combinations of the Hilbert basis
  ss << "HilbertBasis" << std::endl;
  ss << "ModuleGenerators" << std::endl;
  Trace("liastar-normalizCheckSat") << "normaliz input:" << std::endl;
  Trace("liastar-normalizCheckSat") << ss.str() << std::endl;

  // here we use mpq_class instead of Integer (or mpz_class)
  // because libnormaliz.so only has implementation for
  // readNormalizInput<mpq_class>
  std::map<Type::InputType, libnormaliz::Matrix<mpq_class>> input;
  if (stats) stats->d_normalizInputTime.start();
  input = libnormaliz::readNormalizInput<mpq_class>(ss,
                                                    options,
                                                    num_param_input,
                                                    bool_param_input,
                                                    poly_param_input,
                                                    number_field_ref);
  if (stats) stats->d_normalizInputTime.stop();
  if (stats)
  {
    ++stats->d_normalizCalls;
    stats->d_normalizComputeTime.start();
  }
  // Integer is mpz_class, see liastar_utils.h
  Cone<Integer> cone(input);
  if (assumeNonnegative)
  {
    cone.setNonnegative(true);
  }
  // always use infinite precision for integers
  cone.deactivateChangeOfPrecision();
  cone.compute(ConeProperty::HilbertBasis);
  cone.compute(ConeProperty::ModuleGenerators);
  if (stats) stats->d_normalizComputeTime.stop();

  Result result;
  // Constants make a system inhomogeneous, e.g. x[1] >= 1. A homogeneous
  // one, e.g. x[1] >= x[2], has the solution 0, so it is never unsat.
  if (cone.isInhomogeneous())
  {
    // AffineDim is only computed for inhomogeneous cones
    if (cone.getAffineDim() == -1)
    {
      // no integer solution, e.g. x[1] >= 1; x[1] <= 0;
      Trace("liastar-ext") << "empty cone" << std::endl;

      result = Result(Result::Status::UNSAT);
    }
  }
  Trace("liastar-ext-normalizCheckSat")
      << "Constraints are " << result << std::endl;
  if (stats) stats->d_normalizSubSolverTime.stop();
  return result;
}

std::vector<std::pair<std::vector<std::string>, Node>>
LiaStarUtils::getMatrices(Node variables, Node n)
{
  Assert(n.getType().isBoolean()) << "n: " << n << std::endl;
  // one matrix per disjunct, e.g. over (x y):
  //   (>= x 1)               --> {["x[1] >= 1;"]}
  //   (and (>= x 1) (= y 0)) --> {["x[1] >= 1;", "x[2] = 0;"]}
  //   (or (>= x 1) (>= y 2)) --> {["x[1] >= 1;"], ["x[2] >= 2;"]}
  std::vector<std::pair<std::vector<std::string>, Node>> pairs;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::CONST_BOOLEAN:
    {
      bool value = n.getConst<bool>();
      std::string constraint;
      if (value)
      {
        // true has no constraints, but Normaliz needs one: a tautology
        constraint = "x[1] = x[1];";
      }
      else
      {
        constraint = "1 = 0;";
      }
      std::vector<std::string> constraints;
      constraints.push_back(constraint);
      pairs.push_back({constraints, n});
      return pairs;
    }
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      // (>= (+ (* 2 x) (* (- 1) z)) (- 5)) over (x y z)
      // --> "2x[1] - x[3] >=  - 5;"
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
      // the children are atoms (n is in DNF), each giving one constraint
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
      // each disjunct is a conjunction or an atom, giving one matrix
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

    // other kinds are not expected in DNF: no matrix
    default: break;
  }
  return pairs;
}

std::string LiaStarUtils::getString(Node variables, linear::Polynomial& p)
{
  Assert(variables.getKind() == Kind::BOUND_VAR_LIST)
      << "variables: " << variables << std::endl;

  size_t size = variables.getNumChildren();
  Assert(p.isIntegral()) << p.getNode() << " is expected to be linear"
                         << std::endl;
  // (+ (* 2 x) (* (- 1) z)) over (x y z) --> "2x[1] - x[3]"
  // (- 5)                                --> " - 5"
  std::stringstream ss;
  int index = 0;
  for (const linear::Monomial& monomial : p)
  {
    Trace("liastar-ext-debug")
        << "monomial: " << monomial.getNode() << std::endl;
    linear::Constant c = monomial.getConstant();
    Trace("liastar-ext-debug") << "c: " << c.getNode() << std::endl;
    Rational r = c.getValue().abs();

    // print the sign: " - " for a negative coefficient, " + " between terms
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
    // x[1] rather than 1x[1]
    if (r != Rational(1))
    {
      ss << r;
    }
    // find the variable: p is linear, so the monomial has a single one, and
    // the i-th variable of `variables` is x[i + 1]
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