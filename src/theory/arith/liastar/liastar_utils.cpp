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

Node LiaStarUtils::toDNF(Node n, Env* e, LiaStarStatistics* stats)
{
  if (stats) stats->d_toDnfTime.start();
  // eliminate ites
  if (stats) stats->d_removeItesTime.start();
  Node noItes = removeItes(n, e, stats);
  if (stats) stats->d_removeItesTime.stop();
  Trace("liastar-ext-debug") << "noItes: " << noItes << std::endl;
  // eliminate negation
  if (stats) stats->d_removeNotTime.start();
  Node nnf = removeNot(noItes, e);
  if (stats) stats->d_removeNotTime.stop();
  Trace("liastar-ext-debug") << "nnf: " << nnf << std::endl;
  if (TraceIsOn("liastar-ext-smt"))
  {
    // noItes
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"noItes\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << n << std::endl << "    ";
    Trace("liastar-ext-smt") << noItes << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    // nnf
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"nnf\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << noItes << std::endl << "    ";
    Trace("liastar-ext-smt") << nnf << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
  // distributes conjunctions over disjunctions
  if (stats) stats->d_distributeTime.start();
  Node dnf = distribute(nnf, e, stats);
  Trace("liastar-ext-debug") << "dnf: " << dnf << std::endl;
  dnf = recursiveFlatten(e->getNodeManager(), dnf);
  if (stats) stats->d_distributeTime.stop();
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"dnf\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    ";
    Trace("liastar-ext-smt") << nnf << std::endl << "    ";
    Trace("liastar-ext-smt") << dnf << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
  if (stats) stats->d_toDnfTime.stop();
  return dnf;
}

Node LiaStarUtils::recursiveFlatten(NodeManager* nm, Node n)
{
  Trace("liastar-ext-dnf") << "recursiveFlatten::n: " << n << std::endl;
  if (n.getNumChildren() == 0)
  {
    return n;
  }
  Node flat = expr::algorithm::flatten(nm, n);
  std::vector<Node> children;
  for (const auto& child : flat)
  {
    children.push_back(expr::algorithm::flatten(nm, child));
  }
  return nm->mkNode(flat.getKind(), children);
}

Node LiaStarUtils::distribute(Node n,
                              Env* e,
                              LiaStarStatistics* stats,
                              const std::vector<Node>& context)
{
  Assert(n.getType().isBoolean())
      << "Expected " << n << " to be boolean" << std::endl;
  Trace("liastar-ext-dnf") << "distribute::n: " << n << std::endl;
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);

  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      return n;
    }
    case Kind::AND:
    {
      // the non-OR conjuncts of this conjunction hold in every branch
      // below it: make them part of the pruning context up front
      std::vector<Node> childContext = context;
      for (Node child : n)
      {
        if (child.getKind() != Kind::OR && child.getKind() != Kind::AND
            && child.getKind() != Kind::ITE)
        {
          childContext.push_back(child);
        }
      }
      std::vector<Node> conjunctions;
      for (Node child : n)
      {
        Node childDnf = distribute(child, e, stats, childContext);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        conjunctions.push_back(childDnf);
      }

      if (conjunctions.size() == 1)
      {
        return conjunctions[0];
      }
      // basically we compute the cartesian product
      std::vector<std::vector<Node>> disjunctions;
      disjunctions.push_back({});
      // {a, b}
      // {c}
      // {d, e}
      // ****
      // disjunctions: {}
      // disjunctions: {a}, {b}
      // disjunctions: {a, c}, {b, c}
      // disjunctions: {a,c, d},{b, d, d},{a, c, e},{b, c, e}
      for (const Node& conjunct : conjunctions)
      {
        if (conjunct.getKind() != Kind::OR)
        {
          disjunctions[0].push_back(conjunct);
        }
      }
      for (const Node& conjunct : conjunctions)
      {
        if (conjunct.getKind() == Kind::OR)
        {
          std::vector<std::vector<Node>> tmp;
          for (const Node& disjunct : conjunct)
          {
            auto copy = disjunctions;
            for (std::vector<Node>& v : copy)
            {
              v.push_back(disjunct);
              std::vector<Node> query = v;
              query.insert(query.end(), context.begin(), context.end());
              Result r = areAssertionsUnsat(query, e, stats);
              if (r.getStatus() == Result::Status::UNSAT)
              {
                // we can discard unsat conjunctions
                if (stats) ++stats->d_disjunctsPrunedUnsat;
                continue;
              }
              else
              {
                tmp.push_back(v);
              }
            }
          }
          disjunctions = std::move(tmp);
        }
      }
      std::vector<Node> final_disjuncts;
      for (std::vector<Node>& v : disjunctions)
      {
        std::vector<Node> query = v;
        query.insert(query.end(), context.begin(), context.end());
        Result r = areAssertionsUnsat(query, e, stats);
        if (r.getStatus() == Result::Status::UNSAT)
        {
          // we can discard unsat conjunctions
          if (stats) ++stats->d_disjunctsPrunedUnsat;
          continue;
        }
        if (v.size() == 1)
        {
          final_disjuncts.push_back(v[0]);
        }
        else
        {
          final_disjuncts.push_back(nm->mkNode(Kind::AND, v));
        }
      }
      if (final_disjuncts.size() == 0)
      {
        return nm->mkConst<bool>(false);
      }
      if (final_disjuncts.size() == 1)
      {
        return final_disjuncts[0];
      }
      return nm->mkNode(Kind::OR, final_disjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;

      for (size_t i = 0; i < n.getNumChildren(); i++)
      {
        Node childDnf = distribute(n[i], e, stats, context);
        childDnf = expr::algorithm::flatten(nm, childDnf);
        disjuncts.push_back(childDnf);
      }

      return nm->mkNode(Kind::OR, disjuncts);
    }

    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeItes(Node n, Env* e, LiaStarStatistics* stats)
{
  NodeManager* nm = e->getNodeManager();
  Node falseConst = nm->mkConst<bool>(false);
  Node trueConst = nm->mkConst<bool>(true);
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN: return n;
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL:
    {
      std::vector<std::pair<Node, Node>> left =
          removeIntegerItes(n[0], e, stats);
      std::vector<std::pair<Node, Node>> right =
          removeIntegerItes(n[1], e, stats);
      if (left.size() == 1 && right.size() == 1)
      {
        return n;
      }

      // combine the conditions of left and right
      std::vector<Node> disjunctions;
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node result = nm->mkNode(k, l.second, r.second);
          Node combined = result;
          if (r.first != trueConst)
          {
            combined = combined.andNode(r.first);
          }
          else if (l.first != trueConst)
          {
            combined = combined.andNode(l.first);
          }
          disjunctions.push_back(combined);
        }
      }
      return nm->mkNode(Kind::OR, disjunctions);
    }
    case Kind::ITE:
    {
      if (stats) ++stats->d_itesRemoved;
      Node l = removeItes(n[0].andNode(n[1]), e, stats);
      Node r = removeItes(n[0].notNode().andNode(n[2]), e, stats);
      return l.orNode(r);
    }
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : n)
      {
        conjuncts.push_back(removeItes(child, e, stats));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : n)
      {
        disjuncts.push_back(removeItes(child, e, stats));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      return removeItes(n[0], e, stats).notNode();
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

Node LiaStarUtils::removeNot(Node n, Env* e)
{
  NodeManager* nm = e->getNodeManager();
  // eliminate negation nodes of the form (not (or ...)), (not (and ...))
  Node nnf = booleans::TheoryBoolRewriter::computeNnfNorm(nm, n);
  Kind k = nnf.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::CONST_BOOLEAN:
    case Kind::LT:
    case Kind::GT:
    case Kind::LEQ:
    case Kind::GEQ:
    case Kind::EQUAL: return nnf;
    case Kind::AND:
    {
      std::vector<Node> conjuncts;
      for (Node child : nnf)
      {
        conjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::AND, conjuncts);
    }
    case Kind::OR:
    {
      std::vector<Node> disjuncts;
      for (Node child : nnf)
      {
        disjuncts.push_back(removeNot(child, e));
      }
      return nm->mkNode(Kind::OR, disjuncts);
    }
    case Kind::NOT:
    {
      Kind kind = nnf[0].getKind();
      switch (kind)
      {
        case Kind::LT:
        {
          //(not (< a b)) is rewritten as (>= a b)
          return nm->mkNode(Kind::GEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::GT:
        {
          //(not (> a b)) is rewritten as (<= a b)
          return nm->mkNode(Kind::LEQ, nnf[0][0], nnf[0][1]);
        }
        case Kind::LEQ:
        {
          //(not (<= a b)) is rewritten as (> a b)
          return nm->mkNode(Kind::GT, nnf[0][0], nnf[0][1]);
        }
        case Kind::GEQ:
        {
          //(not (>= a b)) is rewritten as (< a b)
          return nm->mkNode(Kind::LT, nnf[0][0], nnf[0][1]);
        }
        case Kind::EQUAL:
        {
          // (not (= a b)) is rewritten as (or (> a b) (< a b))
          Node a = nnf[0][0];
          Node b = nnf[0][1];
          Node gt = nm->mkNode(Kind::GT, a, b);
          Node lt = nm->mkNode(Kind::LT, a, b);
          return gt.orNode(lt);
        }
        default:
          InternalError() << "Unexpected negated kind. Node " << n
                          << " has kind: " << n.getKind() << std::endl;
      }
      break;
    }
    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
}

std::vector<std::pair<Node, Node>> LiaStarUtils::removeIntegerItes(
    Node n, Env* e, LiaStarStatistics* stats)
{
  Assert(n.getType().isInteger());
  // (+
  //    (ite c1 a b)
  //    (ite c2 c d))
  // should return 4 pairs:
  // <(and c1 c2)           ,(+ a c)>
  // <(and c1 (not c2)      ,(+ a d)>
  // <(and (not c1) c2)     ,(+ b c)>
  // <(and (not c1) (not c2),(+ b d)>
  NodeManager* nm = e->getNodeManager();
  Node trueConst = nm->mkConst<bool>(true);
  auto rw = e->getRewriter();
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::VARIABLE:
    case Kind::BOUND_VARIABLE:
    case Kind::NEG:
    case Kind::CONST_INTEGER: return {{trueConst, n}};
    case Kind::ADD:
    case Kind::SUB:
    case Kind::MULT:
    {
      std::vector<std::pair<Node, Node>> left =
          removeIntegerItes(n[0], e, stats);
      std::vector<std::pair<Node, Node>> right =
          removeIntegerItes(n[1], e, stats);
      std::vector<std::pair<Node, Node>> combined;
      // combine the conditions of left and right
      for (const auto& l : left)
      {
        for (const auto& r : right)
        {
          Node condition = rw->rewrite(l.first.andNode(r.first));
          Node result = rw->rewrite(nm->mkNode(k, l.second, r.second));
          combined.push_back({condition, result});
        }
      }
      return combined;
    }
    case Kind::ITE:
    {
      if (stats) ++stats->d_itesRemoved;
      std::vector<std::pair<Node, Node>> iteResult;
      Node condition = removeItes(n[0], e, stats);
      std::vector<std::pair<Node, Node>> thenPart =
          removeIntegerItes(n[1], e, stats);
      for (const auto& pair : thenPart)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = condition;
        }
        else
        {
          newCondition = pair.first.andNode(condition);
        }
        iteResult.push_back({newCondition, pair.second});
      }

      // todo: restore this line Node notCondition =
      // rw->rewrite(condition.notNode());
      Node notCondition = condition.notNode();
      std::vector<std::pair<Node, Node>> elsePart =
          removeIntegerItes(n[2], e, stats);
      for (const auto& pair : elsePart)
      {
        Node newCondition;
        if (pair.first == trueConst)
        {
          newCondition = notCondition;
        }
        else
        {
          newCondition = pair.first.andNode(notCondition);
        }
        iteResult.push_back({newCondition, pair.second});
      }
      return iteResult;
    }

    default:
    {
      break;
    }
  }
  InternalError() << "Unexpected kind. Node " << n
                  << " has kind: " << n.getKind() << std::endl;
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