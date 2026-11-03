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
#include "smt/logic_exception.h"
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

void LiaStarUtils::traceEquivalenceCheck(const char* step,
                                         Node before,
                                         Node after)
{
  // TraceIsOn cannot be negated in builds without tracing
  if (TraceIsOn("liastar-ext-smt"))
  {
    Trace("liastar-ext-smt") << "(push 1)" << std::endl;
    Trace("liastar-ext-smt") << "(echo \"" << step << "\")" << std::endl;
    Trace("liastar-ext-smt") << "(assert " << std::endl
                             << "  (distinct" << std::endl
                             << "    " << before << std::endl
                             << "    " << after << std::endl
                             << "  )" << std::endl
                             << ")" << std::endl;
    Trace("liastar-ext-smt") << "(check-sat)" << std::endl;
    Trace("liastar-ext-smt") << "(pop 1)" << std::endl;
  }
}

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

Node LiaStarUtils::toDNF(Node n, Env& e, LiaStarStatistics* stats)
{
  if (stats)
  {
    stats->d_toDnfTime.start();
  }
  // eliminate ites
  if (stats)
  {
    stats->d_removeItesTime.start();
  }
  Node noItes = removeItes(n, e, stats);
  if (stats)
  {
    stats->d_removeItesTime.stop();
  }
  Trace("liastar-ext-debug") << "noItes: " << noItes << std::endl;
  // each step prints a query that is unsat iff it preserved equivalence,
  // e.g. (assert (distinct (not (>= x 1)) (< x 1))) for the nnf step, see
  // traceEquivalenceCheck
  traceEquivalenceCheck("noItes", n, noItes);
  // negation normal form with negated atoms flipped
  if (stats)
  {
    stats->d_removeNotTime.start();
  }
  Node nnf = removeNot(noItes, e);
  if (stats)
  {
    stats->d_removeNotTime.stop();
  }
  Trace("liastar-ext-debug") << "nnf: " << nnf << std::endl;
  traceEquivalenceCheck("nnf", noItes, nnf);
  // distribute conjunctions over disjunctions, then flatten the and/or
  // nesting the distribution leaves behind
  if (stats)
  {
    stats->d_distributeTime.start();
  }
  Node dnf = distribute(nnf, e, stats);
  Trace("liastar-ext-debug") << "dnf: " << dnf << std::endl;
  dnf = recursiveFlatten(e.getNodeManager(), dnf);
  if (stats)
  {
    stats->d_distributeTime.stop();
  }
  traceEquivalenceCheck("dnf", nnf, dnf);
  if (stats)
  {
    stats->d_toDnfTime.stop();
  }
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
                              Env& e,
                              LiaStarStatistics* stats,
                              const std::vector<Node>& context)
{
  Assert(n.getType().isBoolean())
      << "Expected " << n << " to be boolean" << std::endl;
  Trace("liastar-ext-dnf") << "distribute::n: " << n << std::endl;
  NodeManager* nm = e.getNodeManager();

  Kind k = n.getKind();
  switch (k)
  {
    case Kind::AND:
    {
      // the atoms of this conjunction hold in every branch below it, so
      // they strengthen the pruning checks of the recursive calls
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
      // The DNF of a conjunction is the cartesian product of the disjuncts
      // of its conjuncts. For the conjuncts {(or a b), c, (or d e)},
      // `disjunctions` holds one partial conjunction per future disjunct
      // and grows as follows:
      //   {c}                                   the non-OR conjuncts
      //   {c a}, {c b}                          times (or a b)
      //   {c a d}, {c b d}, {c a e}, {c b e}    times (or d e)
      // Every extension is checked with the subsolver, so an unsat partial
      // conjunction is dropped before it is multiplied further.
      std::vector<std::vector<Node>> disjunctions;
      disjunctions.push_back({});
      for (const Node& conjunct : conjunctions)
      {
        if (conjunct.getKind() != Kind::OR)
        {
          disjunctions[0].push_back(conjunct);
        }
      }
      // whether a disjunction extended the conjunctions, in which case each
      // of them was checked by its last extension
      bool extended = false;
      for (const Node& conjunct : conjunctions)
      {
        if (conjunct.getKind() == Kind::OR)
        {
          extended = true;
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
                // unsat under the context: no disjunct can come from it
                if (stats)
                {
                  ++stats->d_disjunctsPrunedUnsat;
                }
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
        // Extended conjunctions were checked above, so they are not checked
        // again. For (and (>= x 1) (or (<= x 0) (>= y 0))) the extensions
        // check (and (>= x 1) (<= x 0)), which is dropped, and
        // (and (>= x 1) (>= y 0)), which is kept. Without a disjunction
        // among the conjuncts this is the only check:
        //   (and (>= x 1) (<= x 0)) --> false
        if (!extended)
        {
          std::vector<Node> query = v;
          query.insert(query.end(), context.begin(), context.end());
          Result r = areAssertionsUnsat(query, e, stats);
          if (r.getStatus() == Result::Status::UNSAT)
          {
            if (stats)
            {
              ++stats->d_disjunctsPrunedUnsat;
            }
            continue;
          }
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
      // anything but and and or is an atom, e.g. a constraint or a negated
      // Boolean variable that removeNot keeps:
      //   (and (not p) (or (>= x 1) (<= x 0)))
      //   --> (or (and (not p) (>= x 1)) (and (not p) (<= x 0)))
      return n;
    }
  }
}

IteEliminationConverter::IteEliminationConverter(Env& e,
                                                 LiaStarStatistics* stats)
    : NodeConverter(e.getNodeManager()),
      d_rewriter(e.getRewriter()),
      d_stats(stats)
{
}

Node IteEliminationConverter::postConvert(Node n)
{
  if (!n.getType().isBoolean())
  {
    // an integer ite is eliminated when the atom containing it is split
    return n;
  }
  if (n.getKind() == Kind::ITE)
  {
    // (ite c p q) --> (or (and p c) (and q (not c))). The nodes are created
    // one per statement: the evaluation order of function arguments is
    // unspecified, and node ids follow the creation order.
    countEliminated(n);
    Node thenCase = d_nm->mkNode(Kind::AND, n[1], n[0]);
    Node notCondition = n[0].notNode();
    Node elseCase = d_nm->mkNode(Kind::AND, n[2], notCondition);
    return d_nm->mkNode(Kind::OR, thenCase, elseCase);
  }
  // An atom such as (>= t 0) has a non-Boolean child. The children of any
  // other Boolean term are converted already, hence ite-free.
  bool isAtom = std::any_of(
      n.begin(), n.end(), [](TNode c) { return !c.getType().isBoolean(); });
  if (!isAtom || !expr::hasSubtermKind(Kind::ITE, n))
  {
    return n;
  }
  return splitAtom(n);
}

Node IteEliminationConverter::splitAtom(Node atom)
{
  // Depth first over the splits, each a pair of an atom and its guards. The
  // then-branch is split first so that the disjuncts follow the branches:
  //   (>= (ite c1 x y) (ite c2 1 2))
  //   --> (or (and (>= x 1) c1 c2) (and (>= x 2) c1 (not c2))
  //           (and (>= y 1) (not c1) c2) (and (>= y 2) (not c1) (not c2)))
  std::vector<Node> disjuncts;
  std::vector<std::pair<Node, std::vector<Node>>> splits{{atom, {}}};
  while (!splits.empty())
  {
    auto [current, guards] = std::move(splits.back());
    splits.pop_back();
    std::unordered_set<Node> ites;
    expr::getKindSubterms(current, Kind::ITE, true, ites);
    if (ites.empty())
    {
      // getMatrices expects integer terms in arithmetic normal form, so the
      // changed ones are rewritten: (+ x x) --> (* 2 x)
      std::vector<Node> children;
      if (current.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(current.getOperator());
      }
      for (size_t i = 0; i < current.getNumChildren(); i++)
      {
        Node child = current[i];
        if (child != atom[i] && !child.getType().isBoolean())
        {
          child = d_rewriter->rewrite(child);
        }
        children.push_back(child);
      }
      std::vector<Node> conjuncts{d_nm->mkNode(current.getKind(), children)};
      conjuncts.insert(conjuncts.end(), guards.begin(), guards.end());
      disjuncts.push_back(d_nm->mkAnd(conjuncts));
      continue;
    }
    // split on the ite with the smallest id, which keeps the result
    // independent of the order of the set
    Node ite = *std::min_element(
        ites.begin(), ites.end(), [](const Node& a, const Node& b) {
          return a.getId() < b.getId();
        });
    countEliminated(ite);
    // Substitution replaces every occurrence of the ite, so a repeated ite
    // is split once: (>= (+ (ite c x y) (ite c x y)) 0) has two disjuncts.
    // The else-branch is pushed first so that the then-branch is split first.
    for (size_t branch : {2, 1})
    {
      std::vector<Node> branchGuards = guards;
      branchGuards.push_back(branch == 1 ? ite[0] : ite[0].notNode());
      splits.push_back(
          {current.substitute(TNode(ite), TNode(ite[branch])), branchGuards});
    }
  }
  return d_nm->mkOr(disjuncts);
}

void IteEliminationConverter::countEliminated(Node ite)
{
  if (d_stats && d_eliminated.insert(ite).second)
  {
    ++d_stats->d_itesRemoved;
  }
}

Node LiaStarUtils::removeItes(Node n, Env& e, LiaStarStatistics* stats)
{
  Assert(n.getType().isBoolean())
      << "Expected " << n << " to be boolean" << std::endl;
  Assert(!expr::hasClosure(n))
      << "Expected " << n << " to have no binders" << std::endl;
  IteEliminationConverter converter(e, stats);
  return converter.convert(n);
}

NegatedConstraintConverter::NegatedConstraintConverter(NodeManager* nm)
    : NodeConverter(nm)
{
}

Node NegatedConstraintConverter::postConvert(Node n)
{
  if (n.getKind() != Kind::NOT)
  {
    return n;
  }
  Node atom = n[0];
  switch (atom.getKind())
  {
    // (not (< a b)) --> (>= a b)
    case Kind::LT: return d_nm->mkNode(Kind::GEQ, atom[0], atom[1]);
    // (not (> a b)) --> (<= a b)
    case Kind::GT: return d_nm->mkNode(Kind::LEQ, atom[0], atom[1]);
    // (not (<= a b)) --> (> a b)
    case Kind::LEQ: return d_nm->mkNode(Kind::GT, atom[0], atom[1]);
    // (not (>= a b)) --> (< a b)
    case Kind::GEQ: return d_nm->mkNode(Kind::LT, atom[0], atom[1]);
    case Kind::EQUAL:
    {
      // (not (= a b)) --> (or (> a b) (< a b)): a disequality is not a
      // single constraint. Only arithmetic equalities have an order.
      if (atom[0].getType().isRealOrInt())
      {
        // one node per statement, since the evaluation order of function
        // arguments is unspecified
        Node gt = d_nm->mkNode(Kind::GT, atom[0], atom[1]);
        Node lt = d_nm->mkNode(Kind::LT, atom[0], atom[1]);
        return d_nm->mkNode(Kind::OR, gt, lt);
      }
      return n;
    }
    // any other negation, e.g. (not p) for a Boolean variable p, is kept
    default: return n;
  }
}

BooleanEqualityConverter::BooleanEqualityConverter(NodeManager* nm)
    : NodeConverter(nm)
{
}

Node BooleanEqualityConverter::postConvert(Node n)
{
  bool isXor = n.getKind() == Kind::XOR;
  if (!isXor && (n.getKind() != Kind::EQUAL || !n[0].getType().isBoolean()))
  {
    return n;
  }
  // (= p q)   --> (or (and p q) (and (not p) (not q)))
  // (xor p q) --> (or (and p (not q)) (and (not p) q))
  // The nodes are created one per statement: the evaluation order of
  // function arguments is unspecified, and node ids follow the creation
  // order.
  Node notP = n[0].notNode();
  Node notQ = n[1].notNode();
  Node first = d_nm->mkNode(Kind::AND, n[0], isXor ? notQ : n[1]);
  Node second = d_nm->mkNode(Kind::AND, notP, isXor ? n[1] : notQ);
  return d_nm->mkNode(Kind::OR, first, second);
}

Node LiaStarUtils::removeNot(Node n, Env& e)
{
  NodeManager* nm = e.getNodeManager();
  // expand the equalities of Booleans and the xors, which computeNnfNorm
  // keeps:
  //   (= p (>= x 1)) --> (or (and p (>= x 1)) (and (not p) (not (>= x 1))))
  BooleanEqualityConverter equalityConverter(nm);
  Node expanded = equalityConverter.convert(n);
  // push negations down to the atoms:
  //   (not (or p (>= x 1))) --> (and (not p) (not (>= x 1)))
  Node nnf = booleans::TheoryBoolRewriter::computeNnfNorm(nm, expanded);
  // then flip the negated constraints:
  //   (and (not p) (not (>= x 1))) --> (and (not p) (< x 1))
  NegatedConstraintConverter converter(nm);
  return converter.convert(nnf);
}

Result LiaStarUtils::areAssertionsUnsat(const std::vector<Node>& assertions,
                                        Env& e,
                                        LiaStarStatistics* stats)
{
  // pruning is disabled: report "not known to be unsat"
  if (!e.getOptions().arith.arithLiaStarSubSolver)
  {
    return Result();
  }
  if (stats)
  {
    ++stats->d_subSolverCalls;
    stats->d_subSolverTime.start();
  }
  NodeManager* nm = e.getNodeManager();
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
  if (fvs.size() > 0 && e.getOptions().arith.arithLiaStarNormalizAsSubSolver)
  {
    // the coordinates of the Normaliz space: x is x[1]
    Node variables = nm->mkNode(Kind::BOUND_VAR_LIST, freeVariables);
    // one atom per conjunct, as getMatrices expects:
    // (and a (and b c)) --> (and a b c)
    assertion = expr::algorithm::flatten(nm, assertion);
    result =
        normalizCheckSat(variables,
                         assertion,
                         e.getOptions().arith.arithLiaStarAssumeNonnegative,
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
                                  Env& e,
                                  LiaStarStatistics* stats)
{
  if (stats) stats->d_cvc5SubSolverTime.start();
  // default options rather than e's; the logic is still e's
  Options subOptions;
  SubsolverSetupInfo ssi(e, subOptions);

  Result result;
  if (freeVariables.size() == 0)
  {
    result = checkWithSubsolver(assertion, ssi);
  }
  else
  {
    NodeManager* nm = e.getNodeManager();
    // by default nonnegativity is not assumed: the star-contains lambda
    // body (part of `assertion`) carries the user's constraints.
    // With the option: (and (and A (>= x 0)) (>= y 0)).
    if (e.getOptions().arith.arithLiaStarAssumeNonnegative)
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
      // an equality of non-arithmetic terms is no constraint, e.g. of the
      // bit-vectors in (= b #x00), or of the Booleans in (= p (>= x 1)),
      // which toDNF expands
      if (!n[0].getType().isRealOrInt())
      {
        break;
      }
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

    default: break;
  }
  // Any other atom, e.g. a Boolean variable p, has no constraint. Dropping it
  // would change the set: (lambda ((x Int)) p) would give no disjunct, as if
  // p were false.
  std::stringstream ss;
  ss << "int.star-contains expects a predicate of linear integer "
        "constraints over the variables of its lambda, found the atom "
     << n;
  throw LogicException(ss.str());
}

std::string LiaStarUtils::getString(Node variables, linear::Polynomial& p)
{
  Assert(variables.getKind() == Kind::BOUND_VAR_LIST)
      << "variables: " << variables << std::endl;

  size_t size = variables.getNumChildren();
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
    // the i-th variable of `variables` is x[i + 1]. Any other term has no
    // coordinate, e.g. a constant a that the lambda captures, or a product
    // (* x y), whose var list is the product itself. Dropping it would change
    // the constraint: (= x (* 2 a)) would become x[1] = 2.
    Node var = monomial.getVarList().getNode();
    size_t i = 0;
    while (i < size && variables[i] != var)
    {
      i++;
    }
    if (i == size)
    {
      std::stringstream error;
      error << "int.star-contains expects a predicate of linear integer "
               "constraints over the variables of its lambda, found the term "
            << var;
      throw LogicException(error.str());
    }
    ss << "x[" << i + 1 << "]";
  }
  // checked only now: a term of another type, e.g. a real r, makes p
  // nonintegral, and it is rejected above. The integer variables left have
  // integral coefficients in the arithmetic normal form.
  Assert(p.isIntegral()) << p.getNode() << " is expected to be integral"
                         << std::endl;
  Trace("liastar-ext-debug") << "polynomial  : " << p.getNode() << std::endl;
  Trace("liastar-ext-debug") << "string : " << ss.str() << std::endl;
  return ss.str();
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */