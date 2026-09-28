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
#include "expr/skolem_manager.h"
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

using libnormaliz::operator<<;

std::pair<Node, Node> LiaStarUtils::getVectorPredicate(Node n, NodeManager* nm)
{
  Assert(n.getKind() == Kind::STAR_CONTAINS);
  // The first child may have been purified into a skolem by lambda
  // lifting, and the rewriter may normalize a constant lambda to a
  // function array constant; recover the lambda from either form.
  Node lambda =
      uf::FunctionConst::toLambda(SkolemManager::getOriginalForm(n[0]));
  Assert(!lambda.isNull() && lambda.getKind() == Kind::LAMBDA)
      << "Expected a lambda as the first child of " << n << std::endl;
  std::vector<Node> vars(lambda[0].begin(), lambda[0].end());
  std::vector<Node> vecElements(n.begin() + 1, n.end());

  Node substitute = lambda[1].substitute(
      vars.begin(), vars.end(), vecElements.begin(), vecElements.end());

  Trace("liastar-ext-debug") << "n: " << n << std::endl;
  Trace("liastar-ext-debug") << "predicate : " << lambda[1] << std::endl;
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
  Node assertion;
  if (assertions.size() == 1)
  {
    assertion = assertions[0];
  }
  else
  {
    assertion = nm->mkNode(Kind::AND, assertions);
  }
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(assertion, fvs);
  std::vector<Node> freeVariables(fvs.begin(), fvs.end());
  Result result;
  if (fvs.size() > 0 && e->getOptions().arith.arithLiaStarNormalizAsSubSolver)
  {
    Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, freeVariables);
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
    // body (part of `assertion`) carries the user's constraints
    if (e->getOptions().arith.arithLiaStarAssumeNonnegative)
    {
      Node zero = nm->mkConstInt(Rational(0));
      for (Node var : freeVariables)
      {
        assertion = assertion.andNode(nm->mkNode(Kind::GEQ, var, zero));
      }
    }
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

  libnormaliz::OptionsHandler options;

  std::map<libnormaliz::PolyParam::Param, std::vector<std::string>>
      poly_param_input;
  std::map<libnormaliz::NumParam::Param, long> num_param_input;
  std::map<libnormaliz::BoolParam::Param, bool> bool_param_input;

  libnormaliz::renf_class_ptr number_field_ref;

  std::stringstream ss;
  ss << "amb_space " << variables.getNumChildren() << std::endl;
  ss << "constraints "
     << (assertion.getKind() == Kind::AND ? assertion.getNumChildren() : 1)
     << " symbolic" << std::endl;
  if (stats) stats->d_getMatricesTime.start();
  const std::vector<std::pair<std::vector<std::string>, Node>> matrices =
      getMatrices(variables, assertion);
  if (stats) stats->d_getMatricesTime.stop();

  ss << matrices[0].first << std::endl;

  if (assumeNonnegative)
  {
    ss << "nonnegative" << std::endl;
  }
  else
  {
    // nonnegativity is not assumed -- the star-contains lambda carries
    // the user's constraints -- so declare every coordinate
    // sign-unrestricted: normaliz's constraint-only input defaults to
    // the nonnegative orthant
    ss << "signs" << std::endl;
    for (size_t sj = 0; sj < variables.getNumChildren(); sj++)
    {
      ss << (sj == 0 ? "" : " ") << "0";
    }
    ss << std::endl;
  }
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
  if (cone.isInhomogeneous())
  {
    // AffineDim is only computed for inhomogeneous cones
    if (cone.getAffineDim() == -1)
    {
      // the cone is empty skip.
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

std::string LiaStarUtils::getString(Node variables, linear::Polynomial& p)
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