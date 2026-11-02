/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags theory rewriter.
 */

#include "theory/bags/bags_rewriter.h"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <unordered_set>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/emptybag.h"
#include "expr/node_algorithm.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/project_op.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/rewriter.h"
#include "theory/uf/function_const.h"
#include "util/rational.h"
#include "util/statistics_registry.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

/*
 * Notation. The comments of this file write terms in SMT-LIB, with cvc5's
 * operators for tuples, nullables, bags and tables:
 *
 *   (tuple a b)                     a row of sort (Tuple Int Int)
 *   ((_ tuple.select 1) t)          column 1 of the row t
 *   ((_ tuple.project 0 2) t)       the row of columns 0 and 2 of t
 *   (nullable.some 5)               a value of sort (Nullable Int)
 *   (as nullable.null (Nullable Int))
 *   (nullable.is_some x), (nullable.val x)
 *   (bag e 2)                       the bag with e twice (Kind::BAG_MAKE)
 *   (as bag.empty (Bag Int))
 *   (bag.count e X)                 the multiplicity of e in X
 *   (bag.union_disjoint X Y)        multiplicities added
 *   (bag.inter_min X Y)             the smaller multiplicity of the two
 *   (bag.difference_subtract X Y)   multiplicities subtracted, down to 0
 *   (bag.setof X)                   X with every multiplicity cut to 1
 *   (bag.map f X)                   (f t) for every row t of X,
 *                                   multiplicities of equal images added
 *   (bag.filter p X)                the rows t of X with (p t)
 *   (bag.fold f i X)                f folded over the rows of X, from i
 *   (table.product X Y)             the rows of X followed by those of Y
 *   ((_ table.project 0 2) X)       the map of X by tuple.project 0 2
 *   ((_ table.aggr 0) f i X)        X split into the groups of its rows
 *                                   with the same column 0, each group
 *                                   folded as by bag.fold from i
 *
 * X, Y and Z are tables (bags of tuples), t and s rows bound by a lambda, acc
 * an accumulator, and a, b, c terms. The examples of the rules, with the sorts
 * of their symbols, are at their Rewrite ids in rewrites.h; the comments here
 * say how a rule is implemented. The rewriter makes its own bound variables,
 * named row_N, t_N and acc_N. SQL's three-valued logic is encoded with
 * (Nullable Bool): a predicate p holds of a row when p is (nullable.some true),
 * see truthOf.
 */

/**
 * The keys of a table constant X: an SEXPR of SEXPRs of column indices, one per
 * key, recorded by recordKey from the key's assertion. For
 * X : (Bag (Tuple Int Int Int)), the assertion that columns 0 and 2 are a key
 * is
 *   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
 * and X then gets the attribute (SEXPR (SEXPR 0 2)).
 *
 * A key of a table is a set of columns that no two rows of the table agree
 * on, a row that occurs twice counting as two rows; so a table with a key has
 * no row twice. A table constant is a free constant of a table sort, as
 * X above, declared by (declare-const X (Bag (Tuple Int Int Int))); the code
 * tests for one with isVar(). The attribute is stored on the node X, and
 * keysOf reads it back, as {{0, 2}} for the example above.
 */
struct BagsKeysAttributeId
{
};
typedef expr::Attribute<BagsKeysAttributeId, Node> BagsKeysAttribute;
/**
 * A term of an assertion that the rewriter reads a fact from: the bag.setof of
 * a key assertion, or the bag.filter of a NOT NULL assertion (see recordFacts).
 * Such a term is never rewritten: the fact it states would justify rewriting it
 * away (the set of the projection onto a key is the projection itself), and the
 * assertion would become true and the fact lost.
 *
 * For instance, once column 1 of X is known never null, NOT_NULL_COLUMNS
 * would rewrite the predicate of the NOT NULL assertion below,
 * (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))), to false,
 * the filter to the empty bag, and the assertion to true: the solver would
 * no longer be told the fact that the rewrites rely on. The attribute is true
 * on such a term; rewriteSetof and postRewriteFilter return a term that has
 * it unchanged.
 */
struct BagsKeyTermAttributeId
{
};
typedef expr::Attribute<BagsKeyTermAttributeId, bool> BagsKeyTermAttribute;
/**
 * The columns of a table constant X that hold no null: an SEXPR of column
 * indices, recorded by recordNotNull. For X : (Bag (Tuple Int (Nullable Int))),
 * the assertion that column 1 is NOT NULL is
 *   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
 *                    (= ((_ tuple.select 1) t)
 *                       (as nullable.null (Nullable Int))))
 *                  X)
 *      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
 * and X then gets the attribute (SEXPR 1).
 *
 * nonNullColumns reads it, for a table constant and for the terms built
 * over one.
 */
struct BagsNotNullAttributeId
{
};
typedef expr::Attribute<BagsNotNullAttributeId, Node> BagsNotNullAttribute;

namespace {
/**
 * Whether n is the null of a nullable sort, e.g.
 * (as nullable.null (Nullable Int)), the constructor of no argument.
 *
 * The test is on the shape of the node, not on its value: true for
 * (as nullable.null (Nullable Int)), and false for (nullable.some 5), whose
 * constructor has an argument, and for a free constant y : (Nullable Int),
 * which may or may not be null. The sort test rules out the constructors of
 * no argument of other datatypes, as the empty tuple.
 */
bool isNullConstant(const Node& n)
{
  return n.getKind() == Kind::APPLY_CONSTRUCTOR && n.getNumChildren() == 0
         && n.getType().isNullable();
}

/**
 * Whether t is a tuple term, (tuple a b): the rules read columns only of the
 * rows and the accumulators that are tuples, not of another datatype, as the
 * (nullable.some a) of an accumulator of sort (Nullable Int).
 *
 * That is, whether t is built by the tuple constructor, so that its child j
 * is its column j. For instance, true for (tuple 1 (nullable.some 2)) of sort
 * (Tuple Int (Nullable Int)); false for (nullable.some 2), also a constructor
 * term but of the datatype (Nullable Int); and false for a row variable t or
 * ((_ tuple.project 0 1) t), which have a tuple sort but are not built by the
 * constructor. The rules test it before they read the columns of a lambda's
 * body or of an initial value child by child.
 */
bool isTupleTerm(const Node& t)
{
  return t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getType().isTuple();
}

/**
 * The bound variable of type tn that the rewriter uses for role and key n,
 * one per (role, n, tn): the variable of id BAGS_FIRST_INDEX cached on
 * (SEXPR role n), role a string constant. The reductions of bags, the other
 * users of that id, cache on the bag terms they reduce, never on an SEXPR.
 *
 * The BoundVarManager returns the same variable for the same id, cache node
 * and sort, so every call with the same role, n and tn returns the same
 * variable. Rewriting the same term twice then builds the same lambda node,
 * which a fresh variable at each call would not. The role keeps apart
 * variables of different uses that share n: for instance, with n the integer
 * constant 0 and tn the sort Int, the roles "alpha-free" and "alpha-bound"
 * give two different variables, cached on (SEXPR "alpha-free" 0) and
 * (SEXPR "alpha-bound" 0), and each call returns its variable again.
 */
Node mkRewriterVar(NodeManager* nm, const char* role, Node n, TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, tn);
}

/**
 * The same, named name.
 *
 * The same variable as the overload above, which also gets the printed name
 * name. For instance, rowVariable calls it with the role "row", n the empty
 * bag (as bag.empty (Bag (Tuple Int Int))), the name "row_N", N the node id
 * of that empty bag, and tn the sort (Tuple Int Int), for the variable row_N
 * of that sort. The name is not part of the cache: a call with the same
 * role, n and tn but another name returns the same variable, renamed. The
 * callers derive the name from n, so this does not happen.
 */
Node mkRewriterVar(NodeManager* nm,
                   const char* role,
                   Node n,
                   const std::string& name,
                   TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, name, tn);
}
}  // namespace

BagsRewriteResponse::BagsRewriteResponse()
    : d_node(Node::null()), d_rewrite(Rewrite::NONE)
{
}

BagsRewriteResponse::BagsRewriteResponse(Node n, Rewrite rewrite)
    : d_node(n), d_rewrite(rewrite)
{
}

// Makes the rewriter. r is the solver's rewriter, which some rules call on the
// terms they build; statistics, when not null, counts the Rewrite id of every
// step. higherOrder says whether the logic has higher-order terms. When it is
// false, the rules that put a lambda into a term that had none do not apply,
// since the theory of uninterpreted functions rejects lambdas in such a logic:
// FILTER_MAP, MAP_MAP and PROJECT_TO_MAP each return their input unchanged
// unless d_higherOrder holds. For X : (Bag (Tuple Int Int)), with higherOrder
// true,
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t)) X)
// by PROJECT_TO_MAP, and with higherOrder false the projection stays as it is.
// d_zero and d_one, the integer constants 0 and 1, are made once here, since
// many rules build them.
BagsRewriter::BagsRewriter(NodeManager* nm,
                           Rewriter* r,
                           HistogramStat<Rewrite>* statistics,
                           bool higherOrder)
    : TheoryRewriter(nm),
      d_rewriter(r),
      d_statistics(statistics),
      d_higherOrder(higherOrder)
{
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

// The rewrite of a node n after its children are rewritten. The cases, in
// order: a constant is a normal form and stays as it is; an equality goes to
// postRewriteEqual and a bag.choose to rewriteChoose; any other node whose
// children are all constants is evaluated (CONSTANT_EVALUATION); every other
// node goes to the function of its kind, which returns n with Rewrite::NONE
// when no rule applies. Since evaluation comes first, only the projection of
// a table that is not a constant goes to postRewriteProject. For
// X : (Bag (Tuple Int Int)),
//   ((_ table.project 1 0) (bag (tuple 1 2) 3))
//   ---> (bag (tuple 2 1) 3)                          (CONSTANT_EVALUATION)
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.project 1 0) t)) X)
// the latter by PROJECT_TO_MAP, with the higher-order flag (see the
// constructor). A result other than n is rewritten again, children included
// (REWRITE_AGAIN_FULL), so each rule may leave the rest to the other rules.
RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  BagsRewriteResponse response;
  if (n.isConst())
  {
    // no need to rewrite n if it is already in a normal form
    response = BagsRewriteResponse(n, Rewrite::NONE);
  }
  else if (n.getKind() == Kind::EQUAL)
  {
    response = postRewriteEqual(n);
  }
  else if (n.getKind() == Kind::BAG_CHOOSE)
  {
    response = rewriteChoose(n);
  }
  else if (BagsUtils::areChildrenConstants(n))
  {
    Node value = BagsUtils::evaluate(d_rewriter, n);
    response = BagsRewriteResponse(value, Rewrite::CONSTANT_EVALUATION);
  }
  else
  {
    Kind k = n.getKind();
    switch (k)
    {
      case Kind::BAG_MAKE: response = rewriteMakeBag(n); break;
      case Kind::BAG_COUNT: response = rewriteBagCount(n); break;
      case Kind::BAG_SETOF: response = rewriteSetof(n); break;
      case Kind::BAG_UNION_MAX: response = rewriteUnionMax(n); break;
      case Kind::BAG_UNION_DISJOINT: response = rewriteUnionDisjoint(n); break;
      case Kind::BAG_INTER_MIN: response = rewriteIntersectionMin(n); break;
      case Kind::BAG_DIFFERENCE_SUBTRACT:
        response = rewriteDifferenceSubtract(n);
        break;
      case Kind::BAG_DIFFERENCE_REMOVE:
        response = rewriteDifferenceRemove(n);
        break;
      case Kind::BAG_CARD: response = rewriteCard(n); break;
      case Kind::BAG_MAP: response = postRewriteMap(n); break;
      case Kind::BAG_FILTER: response = postRewriteFilter(n); break;
      case Kind::BAG_ALL: response = postRewriteAll(n); break;
      case Kind::BAG_SOME: response = postRewriteSome(n); break;
      case Kind::BAG_FOLD: response = postRewriteFold(n); break;
      case Kind::BAG_PARTITION: response = postRewritePartition(n); break;
      case Kind::TABLE_PRODUCT: response = postRewriteProduct(n); break;
      // a projection of a table that is not a constant, see postRewriteProject
      case Kind::TABLE_PROJECT: response = postRewriteProject(n); break;
      case Kind::TABLE_AGGREGATE: response = postRewriteAggregate(n); break;
      default: response = BagsRewriteResponse(n, Rewrite::NONE); break;
    }
  }

  Trace("bags-rewrite") << "postRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

// The rewrite of a node n before its children are rewritten, for three kinds:
// an equality of a term with itself is true (IDENTICAL_NODES, see
// preRewriteEqual), and bag.subbag and bag.member become terms of the other
// bag operators (SUB_BAG, MEMBER). Every other node is left to postRewrite.
// For A : (Bag Int), B : (Bag Int) and x : Int,
//   (bag.subbag A B)
//   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag Int)))
//   (bag.member x A)
//   ---> (>= (bag.count x A) 1)
// As in postRewrite, a result other than n is rewritten again.
RewriteResponse BagsRewriter::preRewrite(TNode n)
{
  BagsRewriteResponse response;
  Kind k = n.getKind();
  switch (k)
  {
    case Kind::EQUAL: response = preRewriteEqual(n); break;
    case Kind::BAG_SUBBAG: response = rewriteSubBag(n); break;
    case Kind::BAG_MEMBER: response = rewriteMember(n); break;
    default: response = BagsRewriteResponse(n, Rewrite::NONE);
  }

  Trace("bags-rewrite") << "preRewrite " << n << " to " << response.d_node
                        << " by " << response.d_rewrite << "." << std::endl;

  if (d_statistics != nullptr)
  {
    (*d_statistics) << response.d_rewrite;
  }
  if (response.d_node != n)
  {
    return RewriteResponse(RewriteStatus::REWRITE_AGAIN_FULL, response.d_node);
  }
  return RewriteResponse(RewriteStatus::REWRITE_DONE, n);
}

BagsRewriteResponse BagsRewriter::preRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // (= A A) = true where A is a bag
    return BagsRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSubBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SUBBAG);

  // (bag.subbag A B) = ((bag.difference_subtract A B) == bag.empty)
  Node emptybag = d_nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = d_nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return BagsRewriteResponse(equal, Rewrite::SUB_BAG);
}

BagsRewriteResponse BagsRewriter::rewriteMember(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MEMBER);

  // - (bag.member x A) = (>= (bag.count x A) 1)
  Node count = d_nm->mkNode(Kind::BAG_COUNT, n[0], n[1]);
  Node geq = d_nm->mkNode(Kind::GEQ, count, d_one);
  return BagsRewriteResponse(geq, Rewrite::MEMBER);
}

BagsRewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  // return bag.empty for negative or zero multiplicity
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // (bag x c) = bag.empty where c <= 0
    Node emptybag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptybag, Rewrite::BAG_MAKE_COUNT_NEGATIVE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteBagCount(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_COUNT);
  if (n[1].isConst() && n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.count x bag.empty) = 0
    return BagsRewriteResponse(d_zero, Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == Kind::BAG_MAKE && n[0] == n[1][0] && n[1][1].isConst()
      && n[1][1].getConst<Rational>() > Rational(0))
  {
    // (bag.count x (bag x c)) = c, c > 0 is a constant
    Node c = n[1][1];
    return BagsRewriteResponse(c, Rewrite::COUNT_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.setof X), the elements of X each once, tried in this
// order:
// - none for the bag.setof of a key assertion, which stays as it is (see
//   BagsKeyTermAttribute);
// - SETOF_BAG_MAKE, for X = (bag x c): (bag x 1) when c is a positive
//   constant, and (bag x (ite (>= c 1) 1 0)) when c is not a constant. A
//   constant c <= 0 does not reach here, since rewriteMakeBag has already
//   made such a (bag x c) empty;
// - SETOF_PROJECTION_SORT, for X a map (rewriteSetofOfMap).
// For x : Int and c : Int,
//   (bag.setof (bag x c))
//   ---> (bag x (ite (>= c 1) 1 0))                           (SETOF_BAG_MAKE)
BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // The bag.setof of a key assertion, which states that columns of a table
    // are a key of it, as
    //   (= (bag.setof ((_ table.project 0 2) X)) ((_ table.project 0 2) X))
    // recordKey read the key off it and marked it. Rewriting it by the key
    // would make the assertion true and lose the fact, so it stays as it is.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // (bag.setof (bag x n)) = (bag x 1)
    //  where n is a positive constant
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], d_one);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  if (n[0].getKind() == Kind::BAG_MAKE && !n[0][1].isConst())
  {
    // SETOF_BAG_MAKE for a count c that is not a constant: x is in the set
    // once when c is positive, and (bag x c) is empty otherwise, as is
    // (bag x 0), so
    //   (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
    Node count = d_nm->mkNode(
        Kind::ITE, d_nm->mkNode(Kind::GEQ, n[0][1], d_one), d_one, d_zero);
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], count);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  if (n[0].getKind() == Kind::BAG_MAP)
  {
    // SETOF_PROJECTION_SORT: the set of a projection onto columns out of
    // their order is the set of the projection onto the sorted columns, under
    // a map that puts them back in their order (see rewriteSetofOfMap)
    return rewriteSetofOfMap(n);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  if (n[1].getKind() == Kind::BAG_EMPTY || n[0] == n[1])
  {
    // (bag.union_max A A) = A
    // (bag.union_max A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_max bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == Kind::BAG_UNION_MAX
       || n[1].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
    // (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
    // (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
    // (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       || n[0].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // (bag.union_max (bag.union_max A B) A)) = (bag.union_max A B)
    // (bag.union_max (bag.union_max B A) A)) = (bag.union_max B A)
    // (bag.union_max (bag.union_disjoint A B) A)) = (bag.union_disjoint A B)
    // (bag.union_max (bag.union_disjoint B A) A)) = (bag.union_disjoint B A)
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint A bag.empty) = A
    return BagsRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.union_disjoint bag.empty A) = A
    return BagsRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       && n[1].getKind() == Kind::BAG_INTER_MIN)
      || (n[1].getKind() == Kind::BAG_UNION_MAX
          && n[0].getKind() == Kind::BAG_INTER_MIN))

  {
    // (bag.union_disjoint (bag.union_max A B) (bag.inter_min A B)) =
    //         (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    // check if the operands of bag.union_max and bag.inter_min are the
    // same
    std::set<Node> left(n[0].begin(), n[0].end());
    std::set<Node> right(n[1].begin(), n[1].end());
    if (left == right)
    {
      Node rewritten = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, n[0][0], n[0][1]);
      return BagsRewriteResponse(rewritten, Rewrite::UNION_DISJOINT_MAX_MIN);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteIntersectionMin(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_INTER_MIN);
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.inter_min A bag.empty) = bag.empty
    return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // (bag.inter_min A A) = A
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.inter_min A (bag.union_disjoint A B)) = A
      // (bag.inter_min A (bag.union_disjoint B A)) = A
      // (bag.inter_min A (bag.union_max A B)) = A
      // (bag.inter_min A (bag.union_max B A)) = A
      return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT
      || n[0].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.inter_min (bag.union_disjoint A B) A) = A
      // (bag.inter_min (bag.union_disjoint B A) A) = A
      // (bag.inter_min (bag.union_max A B) A) = A
      // (bag.inter_min (bag.union_max B A) A) = A
      return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_SHARED_RIGHT);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceSubtract(
    const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_SUBTRACT);
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_subtract A bag.empty) = A
    // (bag.difference_subtract bag.empty A) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // (bag.difference_subtract A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // (bag.difference_subtract (bag.union_disjoint A B) A) = B
      return BagsRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.union_disjoint B A) A) = B
      return BagsRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_subtract A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_subtract A (bag.union_max A B)) = bag.empty
      // (bag.difference_subtract A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_subtract (bag.inter_min A B) A) = bag.empty
      // (bag.difference_subtract (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteDifferenceRemove(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_DIFFERENCE_REMOVE);

  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // (bag.difference_remove A bag.empty) = A
    // (bag.difference_remove bag.empty B) = bag.empty
    return BagsRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // (bag.difference_remove A A) = bag.empty
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // (bag.difference_remove A (bag.union_disjoint A B)) = bag.empty
      // (bag.difference_remove A (bag.union_disjoint B A)) = bag.empty
      // (bag.difference_remove A (bag.union_max A B)) = bag.empty
      // (bag.difference_remove A (bag.union_max B A)) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // (bag.difference_remove (bag.inter_min A B) A) = bag.empty
      // (bag.difference_remove (bag.inter_min B A) A) = bag.empty
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_MIN);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteChoose(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CHOOSE);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>() > 0)
  {
    // (bag.choose (bag x c)) = x where c is a constant > 0
    return BagsRewriteResponse(n[0][0], Rewrite::CHOOSE_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CARD);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst())
  {
    // (bag.card (bag x c)) = c where c is a constant > 0
    return BagsRewriteResponse(n[0][1], Rewrite::CARD_BAG_MAKE);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// Records the keys and NOT NULL columns of table constants that a top-level
// assertion states, for the rules that read them (see the header). For
// X : (Bag (Tuple Int (Nullable Int))), the assertion
//   (and (= (bag.setof ((_ table.project 0) X)) ((_ table.project 0) X))
//        (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
//                         (= ((_ tuple.select 1) t)
//                            (as nullable.null (Nullable Int))))
//                       X)
//           (as bag.empty (Bag (Tuple Int (Nullable Int))))))
// records the key {0} of X (see recordKey) and that column 1 of X is never
// null (see recordNotNull). An assertion of any other shape records nothing.
void BagsRewriter::recordFacts(TNode assertion) const
{
  // Walk down the conjunctions of the assertion: a conjunct of a top-level
  // assertion holds whenever the assertion does, so it is a top-level fact
  // too. Only AND is entered, so an equality under a negation or a
  // disjunction, which need not hold, is never read.
  std::vector<TNode> todo{assertion};
  while (!todo.empty())
  {
    TNode a = todo.back();
    todo.pop_back();
    if (a.getKind() == Kind::AND)
    {
      todo.insert(todo.end(), a.begin(), a.end());
    }
    else if (a.getKind() == Kind::EQUAL && a[0].getType().isBag())
    {
      // An equality of bags may be a key assertion or a NOT NULL assertion.
      // Each of the two calls checks for its own shape and does nothing on
      // an equality of another shape.
      recordKey(a);
      recordNotNull(a);
    }
  }
}

// Records the key that n states, when n is a key assertion; does nothing
// otherwise. A key is a set of columns that no two rows of a table agree on.
// For X : (Bag (Tuple Int Int Int)),
//   (= (bag.setof ((_ table.project 2 0) X)) ((_ table.project 2 0) X))
// says that the projection of X onto columns 2 and 0 has no row twice, so no
// two rows of X agree on both columns: {0, 2} is a key of X. X gets the key
// (SEXPR 0 2) added to its BagsKeysAttribute, and the bag.setof of n gets
// BagsKeyTermAttribute, so that the rewriter leaves it as it is.
void BagsRewriter::recordKey(const TNode& n) const
{
  // n is a key assertion when one side is (bag.setof M) and the other side is
  // M itself, either way round, where M is the projection of a table constant
  // X onto columns K. M may be written as the input states a projection,
  // ((_ table.project 0 2) X), or as the map the rewriter turns a projection
  // into, (bag.map (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 0 2) t))
  // X). Then no two rows of X agree on K: K is a key of X. The loop tries
  // the bag.setof on side i = 0 and on side i = 1.
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() != Kind::BAG_SETOF || n[i][0] != n[1 - i])
    {
      continue;
    }
    Node M = n[1 - i];
    std::vector<uint32_t> K;
    Node T;
    // T is the table constant X; the fact is stored on it, so it must be a
    // free constant (isVar), not a term.
    if (M.getKind() == Kind::TABLE_PROJECT && M[0].isVar())
    {
      // M = ((_ table.project 0 2) X): K is the projection's indices.
      K = M.getOperator().getConst<ProjectOp>().getIndices();
      T = M[0];
    }
    else if (M.getKind() == Kind::BAG_MAP && M[1].isVar())
    {
      // M = (bag.map g X), with g a projection lambda, of body
      // ((_ tuple.project 0 2) t) or
      // (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)): K is the
      // columns that g selects (see projectionIndices), empty for another g.
      K = projectionIndices(asLambda(M[0]));
      T = M[1];
    }
    // K is empty when M has neither shape, or projects onto no column:
    // nothing is recorded then.
    if (K.empty())
    {
      continue;
    }
    // A key is a set of columns: sort K and drop repeats, so that
    // ((_ table.project 2 0) X) and ((_ table.project 0 2 0) X) give the same
    // key (SEXPR 0 2).
    std::sort(K.begin(), K.end());
    K.erase(std::unique(K.begin(), K.end()), K.end());
    std::vector<Node> cols;
    for (uint32_t k : K)
    {
      cols.push_back(d_nm->mkConstInt(Rational(k)));
    }
    // The key as a node, (SEXPR 0 2) for K = {0, 2}, to be added below to the
    // keys that X already has, such as (SEXPR (SEXPR 1)).
    Node key = d_nm->mkNode(Kind::SEXPR, cols);
    // Mark the bag.setof of n, so that the rewriter does not rewrite it away
    // with the very fact it states (see BagsKeyTermAttribute). The rewriter
    // rewrites the argument M before the bag.setof above it (PROJECT_TO_MAP,
    // for one, turns a projection into a map), and then meets
    // (bag.setof M'), with M' the rewritten M, a new node: mark that one too.
    // This needs the rewriter, so it is skipped when d_rewriter is null.
    Node keyTerm = n[i];
    keyTerm.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal = d_nm->mkNode(Kind::BAG_SETOF, d_rewriter->rewrite(M));
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
    // X's keys so far, then the new key unless X has it already; the
    // attribute is replaced by the SEXPR of them all.
    std::vector<Node> keys;
    if (T.hasAttribute(BagsKeysAttribute()))
    {
      Node old = T.getAttribute(BagsKeysAttribute());
      keys.insert(keys.end(), old.begin(), old.end());
    }
    if (std::find(keys.begin(), keys.end(), key) == keys.end())
    {
      keys.push_back(key);
      Node table = T;
      table.setAttribute(BagsKeysAttribute(), d_nm->mkNode(Kind::SEXPR, keys));
    }
  }
}

// Records the never-null column that n states, when n is a NOT NULL
// assertion; does nothing otherwise. For X : (Bag (Tuple Int (Nullable Int))),
// with both equalities the other way round from the header's example,
//   (= (as bag.empty (Bag (Tuple Int (Nullable Int))))
//      (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
//                    (= (as nullable.null (Nullable Int))
//                       ((_ tuple.select 1) t)))
//                  X))
// says that no row of X has null in column 1. X gets 1 added to its
// BagsNotNullAttribute, and the bag.filter of n gets BagsKeyTermAttribute,
// so that the rewriter leaves it as it is.
void BagsRewriter::recordNotNull(const TNode& n) const
{
  // n is a NOT NULL assertion when one side is the empty bag and the other is
  // the filter of a table constant X by a predicate that holds of the rows
  // with null in some column k: no row of X has null in column k. Both n and
  // the equality in the predicate may be either way round (see recordNotNull
  // in the header):
  //   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
  //                    (= ((_ tuple.select k) t)
  //                       (as nullable.null (Nullable Int))))
  //                  X)
  //      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
  // The loop tries the empty bag on side i = 0 and on side i = 1.
  for (size_t i = 0; i < 2; i++)
  {
    if (n[i].getKind() != Kind::BAG_EMPTY
        || n[1 - i].getKind() != Kind::BAG_FILTER)
    {
      continue;
    }
    Node F = n[1 - i];
    Node T = F[1];
    Node p = asLambda(F[0]);
    // F = (bag.filter p X): X must be a free constant (isVar), as the fact is
    // stored on it, and p a lambda of one variable whose body is an equality.
    // asLambda reads p as a lambda also when it is a function array constant.
    if (!T.isVar() || p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1
        || p[1].getKind() != Kind::EQUAL)
    {
      continue;
    }
    Node v = p[0][0];
    Node col;
    // One side of the equality must be the null constant, and the other a
    // selector applied to the lambda's variable, ((_ tuple.select k) t);
    // col is that selector term.
    for (size_t sd = 0; sd < 2; sd++)
    {
      if (isNullConstant(p[1][sd])
          && p[1][1 - sd].getKind() == Kind::APPLY_SELECTOR
          && p[1][1 - sd][0] == v)
      {
        col = p[1][1 - sd];
      }
    }
    if (col.isNull())
    {
      continue;
    }
    // Mark the filter of n, so that the rewriter does not rewrite it away
    // with the very fact it states (see BagsKeyTermAttribute). The rewriter
    // rewrites the predicate p before the filter above it, and then meets
    // (bag.filter p' X), with p' the rewritten p, a new node when p changes:
    // mark that one too. This needs the rewriter, so it is skipped when
    // d_rewriter is null.
    F.setAttribute(BagsKeyTermAttribute(), true);
    if (d_rewriter != nullptr)
    {
      Node normal =
          d_nm->mkNode(Kind::BAG_FILTER, d_rewriter->rewrite(F[0]), T);
      normal.setAttribute(BagsKeyTermAttribute(), true);
    }
    // k, the index of the column that col selects, as an integer constant.
    // It is added to the never-null columns (SEXPR ..) that X already has,
    // unless it is among them; the attribute is replaced by the new SEXPR.
    Node k = d_nm->mkConstInt(
        Rational(datatypes::utils::indexOf(col.getOperator())));
    std::vector<Node> cols;
    if (T.hasAttribute(BagsNotNullAttribute()))
    {
      Node old = T.getAttribute(BagsNotNullAttribute());
      cols.insert(cols.end(), old.begin(), old.end());
    }
    if (std::find(cols.begin(), cols.end(), k) == cols.end())
    {
      cols.push_back(k);
      Node table = T;
      table.setAttribute(BagsNotNullAttribute(),
                         d_nm->mkNode(Kind::SEXPR, cols));
      // The results that nonNullColumns cached were computed without this
      // column and could miss it: drop them all.
      d_nonNull.clear();
    }
  }
}

// Whether the term t is never null, in every row x and accumulator acc whose
// columns nx of x and nacc of acc are never null. x and acc are variables of
// the lambda that t is the body of, or a part of the body of; either may be
// null when there is none, and then none of its columns counts. The test is
// by the shape of t and is conservative: false means only that no reason was
// found.
// For x : (Tuple Int (Nullable Int)) and nx = {1},
//   (ite (> ((_ tuple.select 0) x) 3)
//        ((_ tuple.select 1) x)
//        (nullable.some 0))
// is never null; so is any term of a sort that is not nullable, such as
// ((_ tuple.select 0) x) : Int; but a free constant y : (Nullable Int) is not.
bool BagsRewriter::nonNullTerm(const Node& t,
                               const Node& x,
                               const std::set<uint32_t>& nx,
                               const Node& acc,
                               const std::set<uint32_t>& nacc) const
{
  // Only a term of a nullable sort can be null: any other term is never null.
  if (!t.getType().isNullable())
  {
    return true;
  }
  if (t.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // t has a nullable sort, so it is built by one of the two constructors:
    // (nullable.some a), of one argument, is never null, and
    // (as nullable.null (Nullable Int)), of none, is null.
    return t.getNumChildren() == 1;
  }
  if (t.getKind() == Kind::APPLY_SELECTOR && t[0].getType().isTuple())
  {
    // ((_ tuple.select k) x) or ((_ tuple.select k) acc): column k of the row
    // or of the accumulator, never null when k is among the never-null
    // columns given for it. A column of any other tuple, e.g. of a row bound
    // by an inner lambda, is not known.
    uint32_t k = datatypes::utils::indexOf(t.getOperator());
    return (!x.isNull() && t[0] == x && nx.count(k) > 0)
           || (!acc.isNull() && t[0] == acc && nacc.count(k) > 0);
  }
  if (t.getKind() == Kind::BAG_FOLD)
  {
    // (bag.fold l i X) of a nullable sort is never null when its initial value
    // i is (nullable.some a), and each value that the step l can return is
    // either the accumulator itself or a (nullable.some b): by induction on
    // the rows folded, the accumulator is never null. For instance
    //   (bag.fold (lambda ((t (Tuple Int Int)) (acc (Nullable Int)))
    //               (ite p (nullable.some ((_ tuple.select 0) t)) acc))
    //             (nullable.some 0)
    //             X)
    // is never null. Here i is t[1], and l is read as a lambda also when it
    // is a function array constant.
    Node l = asLambda(t[0]);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2
        && t[1].getKind() == Kind::APPLY_CONSTRUCTOR
        && t[1].getNumChildren() == 1)
    {
      // keeps(e): whether the step's body e, of the accumulator's nullable
      // sort, returns the accumulator variable l[0][1] or a constructor of
      // one argument, (nullable.some b), in each branch of its ites. Any
      // other term, even one that nonNullTerm would accept, is rejected.
      std::function<bool(const Node&)> keeps = [&](const Node& e) {
        if (e == l[0][1])
        {
          return true;
        }
        if (e.getKind() == Kind::APPLY_CONSTRUCTOR)
        {
          return e.getNumChildren() == 1;
        }
        if (e.getKind() == Kind::ITE)
        {
          return keeps(e[1]) && keeps(e[2]);
        }
        return false;
      };
      return keeps(l[1]);
    }
    // a fold of another shape is not known to be never null
    return false;
  }
  if (t.getKind() == Kind::ITE)
  {
    // (ite (= (as nullable.null (Nullable Int)) a) b c), with the equality
    // either way round and a never null: the condition is false, so the ite
    // is c, and it is never null when c is. Any other ite is never null when
    // both of its branches are.
    const Node& c = t[0];
    if (c.getKind() == Kind::EQUAL)
    {
      for (size_t sd = 0; sd < 2; sd++)
      {
        if (isNullConstant(c[sd]) && nonNullTerm(c[1 - sd], x, nx, acc, nacc))
        {
          return nonNullTerm(t[2], x, nx, acc, nacc);
        }
      }
    }
    return nonNullTerm(t[1], x, nx, acc, nacc)
           && nonNullTerm(t[2], x, nx, acc, nacc);
  }
  // Any other term, e.g. a free constant y : (Nullable Int), or an
  // application of an uninterpreted function, is not known to be never null.
  return false;
}

// The columns of the rows of the aggregate B = ((_ table.aggr K) f i X) that
// are never null. Each row of B is a group of rows of X folded by the step f
// from the initial value i; for an empty X, B is the one row i. A column is
// never null when it is never null in i and f keeps it so. A reached group
// is one that holds a row of X, so that f ran on it at least once; with
// reached true, the caller asks only about the rows of reached groups, and a
// column is then also never null when f's result for it is never null given
// the columns of the accumulator found never null before. For
// X : (Bag (Tuple Int Int)),
//   f = (lambda ((t (Tuple Int Int))
//                (acc (Tuple (Nullable Int) (Nullable Int))))
//         (tuple ((_ tuple.select 0) acc) (nullable.some 1)))
//   i = (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
// give {0}, and {0, 1} with reached: the first step makes column 1
// (nullable.some 1).
std::set<uint32_t> BagsRewriter::aggregateNonNull(const Node& B,
                                                  bool reached) const
{
  std::set<uint32_t> out;
  Node f = asLambda(B[0]);
  Node init = B[1];
  // Only an f of two variables, the row x and the accumulator acc, whose body
  // is a tuple term, and an i that is a tuple term of the same width: column
  // j of a row of B is then child j of f's body or of i. Otherwise no column
  // is known.
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(init)
      || init.getNumChildren() != f[1].getNumChildren())
  {
    return out;
  }
  // the never-null columns of X, which hold of f's row x
  std::set<uint32_t> nx = nonNullColumns(B[2]);
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  // inv starts as the columns of i that are never null. A column j then
  // leaves inv when f's result for it might be null, even with the columns
  // in inv of acc never null, until no column leaves. What is left is the
  // largest set of columns that are never null in i and that every step
  // keeps never null when they are never null before it: by induction on the
  // steps, they are never null in every accumulator, so in every row of B.
  std::set<uint32_t> inv;
  for (size_t j = 0; j < w; j++)
  {
    if (nonNullTerm(init[j], Node::null(), {}, Node::null(), {}))
    {
      inv.insert(j);
    }
  }
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (uint32_t j : std::set<uint32_t>(inv))
    {
      if (!nonNullTerm(f[1][j], x, nx, acc, inv))
      {
        inv.erase(j);
        changed = true;
      }
    }
  }
  out = inv;
  if (reached)
  {
    // The row of a reached group is the result of a step, run on an
    // accumulator whose columns in inv are never null: each column for
    // which f's result is then never null is never null in that row.
    for (size_t j = 0; j < w; j++)
    {
      if (nonNullTerm(f[1][j], x, nx, acc, inv))
      {
        out.insert(j);
      }
    }
  }
  return out;
}

// The columns of the rows of B that are never null, read off B's structure:
// the NOT NULL columns recorded for a table constant (see recordNotNull),
// the columns that each operator keeps never null from its arguments, and
// those that a filter makes never null by testing them. For instance, with
// column 0 of X : (Bag (Tuple (Nullable Int) (Nullable Int))) recorded never
// null,
//   (bag.filter
//     (lambda ((t (Tuple (Nullable Int) (Nullable Int))))
//       (nullable.is_some ((_ tuple.select 1) t)))
//     X)
// has the never-null columns {0, 1}. The result is conservative, a column
// missing from it may still be never null, and is cached in d_nonNull.
std::set<uint32_t> BagsRewriter::nonNullColumns(const Node& B) const
{
  // the cached result, which recordNotNull clears when it records a column
  auto it = d_nonNull.find(B);
  if (it != d_nonNull.end())
  {
    return it->second;
  }
  std::set<uint32_t> out;
  TypeNode et = B.getType().getBagElementType();
  // Only a table, a bag of tuples, has columns; for another bag, such as a
  // (Bag Int), the result is empty.
  if (et.isTuple())
  {
    switch (B.getKind())
    {
      case Kind::BAG_FILTER:
      {
        // B = (bag.filter p Y): the rows of B are rows of Y, so Y's
        // never-null columns stay never null. More are added below from what
        // p requires of the rows it keeps.
        out = nonNullColumns(B[1]);
        Node p = asLambda(B[0]);
        if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1)
        {
          // the conjuncts of the body of p over its row x, each of which
          // holds of every row kept
          Node x = p[0][0];
          std::vector<Node> conjuncts;
          if (p[1].getKind() == Kind::AND)
          {
            conjuncts.insert(conjuncts.end(), p[1].begin(), p[1].end());
          }
          else
          {
            conjuncts.push_back(p[1]);
          }
          for (const Node& c : conjuncts)
          {
            // A conjunct (nullable.is_some ((_ tuple.select k) x)) makes
            // column k never null in the rows kept. isTester gives the index
            // ci of the constructor that c tests, and nullable.is_some is
            // the test of the constructor of one argument.
            Node a;
            int ci = datatypes::utils::isTester(c, a);
            if (ci >= 0 && a.getKind() == Kind::APPLY_SELECTOR && a[0] == x
                && a.getType().isNullable()
                && a.getType().getDType()[ci].getNumArgs() == 1)
            {
              out.insert(datatypes::utils::indexOf(a.getOperator()));
            }
            // So does a conjunct (= ((_ tuple.select k) x) a), either way
            // round, with a never null by its own shape, such as
            // (nullable.some 5); a column of x does not count for a. For a
            // column of a sort that is not nullable, which nonNullTerm finds
            // never null, this adds a column that is never null anyway.
            if (c.getKind() == Kind::EQUAL)
            {
              for (size_t sd = 0; sd < 2; sd++)
              {
                if (c[sd].getKind() == Kind::APPLY_SELECTOR && c[sd][0] == x
                    && nonNullTerm(
                        c[1 - sd], Node::null(), {}, Node::null(), {}))
                {
                  out.insert(datatypes::utils::indexOf(c[sd].getOperator()));
                }
              }
            }
          }
        }
        if (B[1].getKind() == Kind::TABLE_AGGREGATE
            && counterColumn(B[0], asLambda(B[1][0]), B[1][1]) >= 0)
        {
          // B = (bag.filter p ((_ table.aggr K) f i Y)), with p requiring
          // (>= ((_ tuple.select c) r) 1) of a counter column c, which f
          // increments by 1 from 0 (see counterColumn). A row that p keeps
          // has a positive count, so it comes from a group that a row of Y
          // reached, folded at least once by f: aggregateNonNull, with
          // reached true, gives the columns never null in such rows.
          std::set<uint32_t> more = aggregateNonNull(B[1], true);
          out.insert(more.begin(), more.end());
        }
        if (B[1].getKind() == Kind::TABLE_PRODUCT && p.getKind() == Kind::LAMBDA
            && p[0].getNumChildren() == 1)
        {
          // B = (bag.filter p (table.product X (table.product Y Z))), whose
          // components are X, Y and Z. For a component that is an aggregate,
          // p may keep only the rows of B whose part from that component
          // comes from a reached group: when p tests its counter positive,
          // or joins it on all its group columns to such a component (see
          // reachedComponents). Its never-null columns in reached groups
          // are then never null in B, shifted by the column at which the
          // component starts in B's rows.
          //
          // First split the product along its right operands: comps2 gets
          // the components X, Y and Z, and starts2 the column at which each
          // starts. A left operand that is itself a product counts as one
          // component.
          std::vector<Node> comps2;
          std::vector<size_t> starts2;
          Node rest2 = B[1];
          size_t at2 = 0;
          while (true)
          {
            Node c = rest2.getKind() == Kind::TABLE_PRODUCT ? rest2[0] : rest2;
            comps2.push_back(c);
            starts2.push_back(at2);
            at2 += c.getType().getBagElementType().getTupleLength();
            if (rest2.getKind() != Kind::TABLE_PRODUCT)
            {
              break;
            }
            rest2 = rest2[1];
          }
          // reached2[i] is nonzero when p keeps only reached groups of
          // component i; test2, the conjuncts that test the counters, is not
          // used here.
          std::vector<int> test2;
          std::vector<int> reached2 =
              reachedComponents(B[0], comps2, starts2, test2);
          for (size_t i = 0; i < comps2.size(); i++)
          {
            if (reached2[i] && comps2[i].getKind() == Kind::TABLE_AGGREGATE)
            {
              for (uint32_t m : aggregateNonNull(comps2[i], true))
              {
                out.insert(m + starts2[i]);
              }
            }
          }
        }
        break;
      }
      // (bag.setof Y), (bag.difference_subtract Y Z) and
      // (bag.difference_remove Y Z): every row of B is a row of Y, so the
      // never-null columns of Y.
      case Kind::BAG_SETOF:
      case Kind::BAG_DIFFERENCE_SUBTRACT:
      case Kind::BAG_DIFFERENCE_REMOVE: out = nonNullColumns(B[0]); break;
      case Kind::BAG_INTER_MIN:
      {
        // every row of (bag.inter_min Y Z) is a row of both Y and Z, so a
        // column never null in either is never null in B
        out = nonNullColumns(B[0]);
        std::set<uint32_t> more = nonNullColumns(B[1]);
        out.insert(more.begin(), more.end());
        break;
      }
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      {
        // a row of (bag.union_disjoint Y Z) or (bag.union_max Y Z) may come
        // from either side, so only the columns never null on both sides
        std::set<uint32_t> a = nonNullColumns(B[0]);
        std::set<uint32_t> b = nonNullColumns(B[1]);
        for (uint32_t c : a)
        {
          if (b.count(c))
          {
            out.insert(c);
          }
        }
        break;
      }
      case Kind::TABLE_PRODUCT:
      {
        // a row of (table.product Y Z) is a row of Y followed by a row of Z:
        // the never-null columns of Y, and those of Z shifted by the width wl
        // of Y's rows
        out = nonNullColumns(B[0]);
        size_t wl = B[0].getType().getBagElementType().getTupleLength();
        for (uint32_t c : nonNullColumns(B[1]))
        {
          out.insert(c + wl);
        }
        break;
      }
      case Kind::BAG_MAP:
      {
        // A row of (bag.map (lambda ((t ..)) (tuple a0 .. am)) Y) is
        // (tuple a0 .. am) for a row t of Y: column j is never null when aj
        // is, given the never-null columns of Y for t. The body must be
        // built by the tuple constructor for its columns to be read; for
        // another body, such as ((_ tuple.project 1 0) t), none is found.
        Node g = asLambda(B[0]);
        if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
            && g[1].getKind() == Kind::APPLY_CONSTRUCTOR)
        {
          std::set<uint32_t> nx = nonNullColumns(B[1]);
          for (size_t j = 0; j < g[1].getNumChildren(); j++)
          {
            if (nonNullTerm(g[1][j], g[0][0], nx, Node::null(), {}))
            {
              out.insert(j);
            }
          }
        }
        break;
      }
      // ((_ table.aggr K) f i Y), see aggregateNonNull; whether its groups
      // were reached is not known here, so reached is false
      case Kind::TABLE_AGGREGATE: out = aggregateNonNull(B, false); break;
      default:
        // A table constant: the NOT NULL columns recorded for it, as the
        // SEXPR of integer constants that recordNotNull built. Any other
        // node, such as (bag (tuple ..) 1) or a projection, gets none.
        if (B.isVar() && B.hasAttribute(BagsNotNullAttribute()))
        {
          for (const Node& c : B.getAttribute(BagsNotNullAttribute()))
          {
            out.insert(c.getConst<Rational>().getNumerator().toUnsignedInt());
          }
        }
        break;
    }
  }
  d_nonNull[B] = out;
  return out;
}

// body, the body of a lambda over the row x, with the null tests that the
// never-null columns cols of x decide replaced by their values. A test
// (nullable.is_some a) or (nullable.is_null a) of a term a that is never null
// given cols (see nonNullTerm) becomes true or false, and an equality of such
// an a with the null constant becomes false. The rule NOT_NULL_COLUMNS uses
// it, with the never-null columns of the bag that x ranges over. For
// x : (Tuple Int (Nullable Int)) and cols = {1},
//   (and (nullable.is_some ((_ tuple.select 1) x))
//        (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
//        p)
// becomes (and true false p), which the rewriter then simplifies. The result
// is body itself when no test is decided.
Node BagsRewriter::assumeNonNull(const Node& body,
                                 const Node& x,
                                 const std::set<uint32_t>& cols) const
{
  // with no never-null column, no test is decided
  if (cols.empty())
  {
    return body;
  }
  // decided(n): the value of n when n is a null test that cols decide, null
  // otherwise. (= (as nullable.null (Nullable Int)) a), either way round,
  // with a never null, is false. A tester of a nullable a that is never null
  // is true when it tests the constructor of one argument, nullable.is_some,
  // and false for nullable.is_null.
  auto decided = [&](const Node& n) -> Node {
    if (n.getKind() == Kind::EQUAL)
    {
      for (size_t sd = 0; sd < 2; sd++)
      {
        if (isNullConstant(n[sd])
            && nonNullTerm(n[1 - sd], x, cols, Node::null(), {}))
        {
          return d_nm->mkConst(false);
        }
      }
    }
    Node a;
    int ci = datatypes::utils::isTester(n, a);
    if (ci >= 0 && a.getType().isNullable()
        && nonNullTerm(a, x, cols, Node::null(), {}))
    {
      return d_nm->mkConst(a.getType().getDType()[ci].getNumArgs() == 1);
    }
    return Node::null();
  };
  // Rebuild body bottom up, without recursion: cache maps each node done to
  // its replacement. A decided node is replaced by its value, and its
  // children are not visited; a leaf stays as it is; any other node is
  // rebuilt from the replacements of its children, once they are all done.
  // The walk also enters the lambdas nested in body, and does not check
  // whether one of them binds x again.
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{body};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      // already done, e.g. a child shared by two parents
      todo.pop_back();
      continue;
    }
    Node d = decided(n);
    if (!d.isNull())
    {
      cache[n] = d;
      todo.pop_back();
      continue;
    }
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    // push the children not done yet, and come back to n after them
    bool ready = true;
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // n from the replacements of its children, with the operator first for a
    // parameterized kind, such as the selector of ((_ tuple.select 1) x); n
    // itself when no child changed
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      changed = changed || cache[c] != c;
      children.push_back(cache[c]);
    }
    cache[n] = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
  }
  return cache[body];
}

// The keys recorded for a table constant (see recordKey), each as a set of
// column indices; a key is a set of columns that no two rows of the table
// agree on. B is the table constant X or a filter of it, possibly nested,
// as (bag.filter p (bag.filter q X)): a filter keeps some of the rows of X,
// so the keys of X still hold. For X with the attribute
// (SEXPR (SEXPR 0 2) (SEXPR 1)), the result is {{0, 2}, {1}}. It is empty
// for any other B, and for a table constant with no key recorded.
std::vector<std::set<uint32_t>> BagsRewriter::keysOf(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  // strip the filters above the table
  Node T = B;
  while (T.getKind() == Kind::BAG_FILTER)
  {
    T = T[1];
  }
  if (!T.isVar() || !T.hasAttribute(BagsKeysAttribute()))
  {
    return keys;
  }
  // each key (SEXPR 0 2), of integer constants, as the set {0, 2}
  for (const Node& key : T.getAttribute(BagsKeysAttribute()))
  {
    std::set<uint32_t> cols;
    for (const Node& c : key)
    {
      cols.insert(c.getConst<Rational>().getNumerator().toUnsignedInt());
    }
    keys.push_back(cols);
  }
  return keys;
}

// The keys of B, read off its structure. A key is a set of columns that no
// two rows of B agree on, a row that occurs twice counting as two rows, so
// every key found means that B has no row twice; the empty key means that B
// has at most one row. The keys found are a table constant's recorded keys
// (see keysOf), kept by filters, intersections and differences and by maps
// that copy their columns, and combined by products; all the columns of a
// bag.setof; and the columns of an aggregate's rows that copy its group
// columns. Keys may be missed, and the same key may occur twice. With X and
// Y of two columns, each with the key {0}:
//   (table.product X Y) has the key {0, 2}, Y's column 0 being column 2
//     of the product;
//   (bag.map (lambda ((t (Tuple Int Int)))
//              (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
//            X) has the key {1};
//   ((_ table.aggr 0) f i X) has the key {k} when column k of f's result
//     is ((_ tuple.select 0) t), the group column.
std::vector<std::set<uint32_t>> BagsRewriter::rowKeys(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  TypeNode et = B.getType().getBagElementType();
  // only a table, a bag of tuples, has columns
  if (!et.isTuple())
  {
    return keys;
  }
  size_t width = et.getTupleLength();
  switch (B.getKind())
  {
    case Kind::BAG_FILTER:
    {
      // B = (bag.filter P Y) keeps some of the rows of Y, so the keys of Y
      // hold, and P can make them smaller. A key column that P fixes to a
      // constant has the same value in all the rows kept, so it is dropped
      // from the key; a key column that P sets equal to another column is
      // replaced by that column. For X : (Bag (Tuple Int Int Int)) with the
      // key {0, 1},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 1) t) 5))
      //               X)
      // has the key {0}; and with the key {1, 2},
      //   (bag.filter (lambda ((t (Tuple Int Int Int)))
      //                 (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
      //               X)
      // has the key {0, 1}, column 2 being equal to column 0.
      keys = rowKeys(B[1]);
      // the columns fixed by conjuncts (= ((_ tuple.select k) t) c), with c
      // a constant (see fixedColumns)
      std::map<uint32_t, Node> fixed = fixedColumns(B[0]);
      Node P = asLambda(B[0]);
      // rep is a union-find over the columns, joined by the equalities of P
      // between two columns; find(k) is the smallest column known equal to
      // column k, with path compression.
      std::vector<uint32_t> rep(width);
      for (uint32_t k = 0; k < width; k++)
      {
        rep[k] = k;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t k) {
        return rep[k] == k ? k : (rep[k] = find(rep[k]));
      };
      if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
      {
        // the conjuncts of P's body, each of which holds of every row kept;
        // a conjunct (= ((_ tuple.select j) t) ((_ tuple.select k) t)), with
        // t the row, joins the classes of columns j and k
        std::vector<Node> conjuncts;
        if (P[1].getKind() == Kind::AND)
        {
          conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
        }
        else
        {
          conjuncts.push_back(P[1]);
        }
        for (const Node& c : conjuncts)
        {
          if (c.getKind() == Kind::EQUAL
              && c[0].getKind() == Kind::APPLY_SELECTOR
              && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == P[0][0]
              && c[1][0] == P[0][0])
          {
            uint32_t a = find(datatypes::utils::indexOf(c[0].getOperator()));
            uint32_t b = find(datatypes::utils::indexOf(c[1].getOperator()));
            if (a != b && a < width && b < width)
            {
              rep[std::max(a, b)] = std::min(a, b);
            }
          }
        }
      }
      // Each key of Y without its fixed columns, and with each other column
      // replaced by the smallest column equal to it. This is a key of B: two
      // rows kept that agree on it agree on the fixed columns (both have the
      // constant) and on the replaced ones (equal to their replacements), so
      // on the whole key of Y. A key may become empty, as {1} with column 1
      // fixed: B then has at most one row.
      std::vector<std::set<uint32_t>> out;
      for (const std::set<uint32_t>& K : keys)
      {
        std::set<uint32_t> k2;
        for (uint32_t c : K)
        {
          if (!fixed.count(c))
          {
            k2.insert(find(c));
          }
        }
        out.push_back(k2);
      }
      return out;
    }
    // (bag.difference_subtract Y Z) and (bag.difference_remove Y Z) keep some
    // of the rows of Y, so the keys of Y
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE: return rowKeys(B[0]);
    case Kind::BAG_INTER_MIN:
    {
      // (bag.inter_min Y Z) is contained in both Y and Z, so the keys of each
      keys = rowKeys(B[0]);
      std::vector<std::set<uint32_t>> more = rowKeys(B[1]);
      keys.insert(keys.end(), more.begin(), more.end());
      return keys;
    }
    case Kind::BAG_SETOF:
    {
      // (bag.setof Y) has the rows of Y, so the keys of Y hold; and it has no
      // row twice, so all of its columns are a key too.
      keys = rowKeys(B[0]);
      // For (bag.setof (bag.map g Z)) with g's body (tuple a0 .. am), that
      // key leaves out a column j whose aj is a constant, the same in every
      // row, and a column j whose aj is the same term as that of an earlier
      // column, so equal to it; the first of equal columns stays. For
      // instance, for (tuple ((_ tuple.select 0) t) 5 ((_ tuple.select 0) t))
      // the key is {0}. For any other Y, it is all the columns.
      std::set<uint32_t> all;
      Node g =
          B[0].getKind() == Kind::BAG_MAP ? asLambda(B[0][0]) : Node::null();
      std::set<Node> seen;
      for (size_t k = 0; k < width; k++)
      {
        if (!g.isNull() && g.getKind() == Kind::LAMBDA && isTupleTerm(g[1])
            && g[1].getNumChildren() == width)
        {
          if (g[1][k].isConst() || !seen.insert(g[1][k]).second)
          {
            continue;
          }
        }
        all.insert(k);
      }
      keys.push_back(all);
      return keys;
    }
    case Kind::BAG_MAP:
    {
      // B = (bag.map g Y), with g = (lambda ((t ..)) (tuple a0 .. am)); for
      // another g no key is known.
      Node g = asLambda(B[0]);
      if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
          || !isTupleTerm(g[1]) || g[1].getNumChildren() != width)
      {
        return keys;
      }
      // carried maps each column c of Y that g copies, as some
      // aj = ((_ tuple.select c) t), to the first such column j of B
      Node x = g[0][0];
      std::map<uint32_t, uint32_t> carried;
      for (size_t k = 0; k < width; k++)
      {
        const Node& c = g[1][k];
        if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == x)
        {
          uint32_t col = datatypes::utils::indexOf(c.getOperator());
          if (!carried.count(col))
          {
            carried[col] = k;
          }
        }
      }
      // A key K of Y all of whose columns g copies gives the key of their
      // copies in B: two rows of Y differ on K, so their images differ on
      // the copies, and as Y has no row twice, no image occurs twice. A key
      // with a column that g does not copy is lost.
      for (const std::set<uint32_t>& K : rowKeys(B[1]))
      {
        std::set<uint32_t> out;
        bool kept = true;
        for (uint32_t c : K)
        {
          kept = kept && carried.count(c) > 0;
          if (kept)
          {
            out.insert(carried[c]);
          }
        }
        if (kept)
        {
          keys.push_back(out);
        }
      }
      return keys;
    }
    case Kind::TABLE_PRODUCT:
    {
      // B = (table.product Y Z): each key K1 of Y with each key K2 of Z gives
      // the key of K1 and of K2 shifted by the width wl of Y's rows. Two rows
      // of B that agree on it come from the same row of Y and the same row
      // of Z, and neither Y nor Z has a row twice.
      size_t wl = B[0].getType().getBagElementType().getTupleLength();
      for (const std::set<uint32_t>& K1 : rowKeys(B[0]))
      {
        for (const std::set<uint32_t>& K2 : rowKeys(B[1]))
        {
          std::set<uint32_t> out = K1;
          for (uint32_t c : K2)
          {
            out.insert(c + wl);
          }
          keys.push_back(out);
        }
      }
      return keys;
    }
    case Kind::TABLE_AGGREGATE:
    {
      // B = ((_ table.aggr K) f i Y), with
      // f = (lambda ((t ..) (acc ..)) (tuple e0 .. em)): B has one row per
      // group, and the rows of a group agree on the group columns K. When,
      // for each group column c, some ek is ((_ tuple.select c) t), column k
      // of a group's row is column c of the last row folded, the group's
      // value of c. Those columns k are a key of B, since two groups differ
      // on some group column; an empty Y gives B the one row i, and a table
      // of one row has every key. With no group columns, B has one row and
      // the key is empty. If a group column is not copied, no key is known.
      Node f = asLambda(B[0]);
      if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
          || !isTupleTerm(f[1]))
      {
        return keys;
      }
      Node x = f[0][0];
      std::set<uint32_t> out;
      for (uint32_t c : B.getOperator().getConst<ProjectOp>().getIndices())
      {
        // the first column k of f's result that copies group column c
        bool found = false;
        for (size_t k = 0; k < f[1].getNumChildren() && !found; k++)
        {
          const Node& e = f[1][k];
          if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == x
              && datatypes::utils::indexOf(e.getOperator()) == c)
          {
            out.insert(k);
            found = true;
          }
        }
        if (!found)
        {
          return keys;
        }
      }
      keys.push_back(out);
      return keys;
    }
    default: break;
  }
  // a table constant: its recorded keys (see keysOf); any other node, such as
  // (bag (tuple ..) 1) or a projection, has no key found
  if (B.isVar())
  {
    return keysOf(B);
  }
  return keys;
}

// The rules for an equality (= A B) of two bags, after A and B are rewritten,
// tried in this order:
// - EQ_REFL: sides that rewrote to one term make true;
// - EQ_CONST_FALSE: two constants make false. Bag constants are in a normal
//   form, so two constants that are not one node are distinct bags; this is
//   why EQ_REFL must come first;
// - EQ_SYM: the sides in one order, the smaller node first, so that (= A B)
//   and (= B A) become one node.
// For A : (Bag Int),
//   (= (bag.union_disjoint A (as bag.empty (Bag Int))) A)
//   ---> true                                                     (EQ_REFL)
//   (= (bag 1 2) (bag 1 3))
//   ---> false                                             (EQ_CONST_FALSE)
BagsRewriteResponse BagsRewriter::postRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    Node ret = d_nm->mkConst(true);
    return BagsRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    Node ret = d_nm->mkConst(false);
    return BagsRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // standard ordering
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return BagsRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.map f X), the bag of (f t) for the rows t of X, tried in
// this order; the first that changes the term returns it:
// - MAP_IDENTITY: a map that copies every column of X, in order, is X;
// - NOT_NULL_COLUMNS: the null tests in f's body of the columns that are
//   never null in the rows of X are decided (assumeNonNull);
// - MAP_CONST, MAP_BAG_MAKE and MAP_UNION_DISJOINT, for X a constant, a
//   (bag x c) or a bag.union_disjoint;
// - MAP_MAP, for X a map (rewriteMapOfMap);
// - AGGREGATE_DEAD_COLUMNS, for X an aggregate, possibly under a filter
//   (rewriteAggregateDeadColumns);
// - MAP_EQUAL_COLUMNS, then MAP_FIXED_COLUMNS, for X a filter;
// - CANONICAL_VARIABLE (canonicalLambda), last, so that f's variable is
//   renamed only once no other rule changes the term.
// For X : (Bag (Tuple Int Int)),
//   (bag.map
//     (lambda ((t (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
//     X)
//   ---> X                                                    (MAP_IDENTITY)
BagsRewriteResponse BagsRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAP);
  TypeNode mapType = n.getType();
  TypeNode argType = n[1].getType();
  if (mapType == argType && argType.getBagElementType().isTuple())
  {
    // MAP_IDENTITY, for a map whose result has the sort of X: J lists the
    // columns of t that f's tuple copies, {0, 1} for
    //   (lambda ((t (Tuple Int Int)))
    //     (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
    // or for (lambda ((t (Tuple Int Int))) ((_ tuple.project 0 1) t)), and is
    // empty when f is no such projection (see projectionIndices). f is the
    // identity when J is 0, 1, ..., w - 1 for the w columns of X.
    std::vector<uint32_t> J = projectionIndices(asLambda(n[0]));
    bool identity =
        J.size() == n[1].getType().getBagElementType().getTupleLength();
    for (size_t k = 0; k < J.size() && identity; k++)
    {
      identity = J[k] == k;
    }
    if (identity)
    {
      return BagsRewriteResponse(n[1], Rewrite::MAP_IDENTITY);
    }
  }
  {
    // NOT_NULL_COLUMNS: nonNullColumns reads off the shape of X the columns
    // that no row of X has null in, as column 1 of
    // X : (Bag (Tuple Int (Nullable Int))) given an assertion that it is NOT
    // NULL. In the body of g, f as a lambda (see asLambda), assumeNonNull
    // decides the null tests of these columns of g's variable t:
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true. The map by the
    // new body is the same bag, as the tests had these values on every row.
    Node g = asLambda(n[0]);
    if (g.getKind() == Kind::LAMBDA && g[0].getNumChildren() == 1
        && n[1].getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(g[1], g[0][0], nonNullColumns(n[1]));
      if (b != g[1])
      {
        Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(g[0][0], b), n[1]);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  if (n[1].isConst())
  {
    // (bag.map f (as bag.empty (Bag T1)) = (as bag.empty (Bag T2))
    // (bag.map f (bag "a" 3)) = (bag (f "a") 3)
    std::map<Node, Rational> elements = BagsUtils::getBagElements(n[1]);
    std::map<Node, Rational> mappedElements;
    std::map<Node, Rational>::iterator it = elements.begin();
    while (it != elements.end())
    {
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], it->first);
      mappedElements[mappedElement] = it->second;
      ++it;
    }
    TypeNode t = d_nm->mkBagType(n[0].getType().getRangeType());
    Node ret = BagsUtils::constructConstantBagFromElements(t, mappedElements);
    return BagsRewriteResponse(ret, Rewrite::MAP_CONST);
  }
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // (bag.map f (bag x y)) = (bag (apply f x) y)
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, mappedElement, n[1][1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.map f (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.map f A) (bag.map f B))
      Node a = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::MAP_UNION_DISJOINT);
    }

    case Kind::BAG_MAP:
    {
      // MAP_MAP: for X = (bag.map g Y), one map of Y by f composed with g,
      // when both are lambdas and with the higher-order flag (see
      // rewriteMapOfMap). When it does not apply, the rules below are tried.
      BagsRewriteResponse r = rewriteMapOfMap(n);
      if (r.d_node != n)
      {
        return r;
      }
      break;
    }
    // any other X goes on to the rules below
    default: break;
  }
  // The rules for a map of an aggregate, each implemented and documented in a
  // function of its own.
  {
    // AGGREGATE_DEAD_COLUMNS: for X an aggregate, or a filter of one, the
    // columns of the aggregate's rows that neither f nor the filter reads,
    // and that no other column's step reads, are not computed (see
    // rewriteAggregateDeadColumns, which returns n when the rule does not
    // apply)
    BagsRewriteResponse r = rewriteAggregateDeadColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // MAP_EQUAL_COLUMNS, for X = (bag.filter P Y): a row of Y that passes P
    // has equal values in two columns that a conjunct of P equates, as
    // (= ((_ tuple.select 0) r) ((_ tuple.select 2) r)), so f may read the
    // smallest column of each class of equated columns in place of the
    // others. Two maps that read different columns of a class then become one
    // term. f (as h) and P must be lambdas of one variable, over tuples.
    Node h = asLambda(n[0]);
    Node P = asLambda(n[1][0]);
    if (h.getKind() == Kind::LAMBDA && h[0].getNumChildren() == 1
        && P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1
        && n[1][1].getType().getBagElementType().isTuple())
    {
      Node r = P[0][0];
      size_t w = n[1][1].getType().getBagElementType().getTupleLength();
      // rep is a union-find over the w columns of Y: each column points to a
      // column it equals, the roots are the smallest of their classes, and
      // find returns the root of a column's class, shortening the path
      std::vector<uint32_t> rep(w);
      for (uint32_t col = 0; col < w; col++)
      {
        rep[col] = col;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t col) {
        return rep[col] == col ? col : (rep[col] = find(rep[col]));
      };
      // the conjuncts of P's body, or the body itself when it is not an and
      std::vector<Node> conjuncts;
      if (P[1].getKind() == Kind::AND)
      {
        conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
      }
      else
      {
        conjuncts.push_back(P[1]);
      }
      // a conjunct (= ((_ tuple.select a) r) ((_ tuple.select b) r)) over P's
      // own variable r merges the classes of a and b, under the smaller root
      for (const Node& c : conjuncts)
      {
        if (c.getKind() == Kind::EQUAL && c[0].getKind() == Kind::APPLY_SELECTOR
            && c[1].getKind() == Kind::APPLY_SELECTOR && c[0][0] == r
            && c[1][0] == r)
        {
          uint32_t a = find(datatypes::utils::indexOf(c[0].getOperator()));
          uint32_t b = find(datatypes::utils::indexOf(c[1].getOperator()));
          if (a != b)
          {
            rep[std::max(a, b)] = std::min(a, b);
          }
        }
      }
      // in f's body, over f's own variable v, each ((_ tuple.select col) v)
      // of a column that is not the root of its class is replaced by the read
      // of the root; the rule applies only when the body has such a read
      std::vector<Node> from, to;
      Node v = h[0][0];
      for (uint32_t col = 0; col < w; col++)
      {
        if (find(col) != col)
        {
          from.push_back(datatypes::TupleUtils::nthElementOfTuple(v, col));
          to.push_back(datatypes::TupleUtils::nthElementOfTuple(v, find(col)));
        }
      }
      if (!from.empty())
      {
        Node body =
            h[1].substitute(from.begin(), from.end(), to.begin(), to.end());
        if (body != h[1])
        {
          Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(v, body), n[1]);
          return BagsRewriteResponse(ret, Rewrite::MAP_EQUAL_COLUMNS);
        }
      }
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER && n[0].getKind() == Kind::LAMBDA
      && n[0][0].getNumChildren() == 1)
  {
    // MAP_FIXED_COLUMNS, for X = (bag.filter P Y) and f a lambda node: a row
    // that passes P has in column k the constant c of a conjunct
    // (= ((_ tuple.select k) r) c) of P, so f's body may read c in place of
    // ((_ tuple.select k) t). fixed maps each such k to its c (see
    // fixedColumns), and readFixed makes the replacements.
    std::map<uint32_t, Node> fixed = fixedColumns(n[1][0]);
    if (n[1][1].getKind() == Kind::TABLE_AGGREGATE)
    {
      // For Y an aggregate and P a test that its counter column, the count of
      // rows of each group, is at least 1, P keeps only the groups that some
      // row of the aggregate's input made. In each of them, a column that the
      // step sets to a constant, or keeps at a constant initial value, has
      // that constant (see reachedGroupConstants). Where P also fixes the
      // column, insert keeps P's constant.
      std::map<uint32_t, Node> constant = reachedGroupConstants(n[1]);
      fixed.insert(constant.begin(), constant.end());
    }
    Node var = n[0][0][0];
    Node body = readFixed(n[0][1], var, fixed);
    if (body != n[0][1])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(var, body), n[1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_FIXED_COLUMNS);
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 1)
  {
    // CANONICAL_VARIABLE: f with its variable renamed to t_N, N the id of f's
    // alpha key, a node that is the same for lambdas that differ only in the
    // names of their variables (see canonicalLambda). Such lambdas then become
    // one node, which the solver treats as one function.
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, canonical, n[1]);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for (bag.filter P A), the rows t of A with (P t), tried in this
// order; the first that changes the term returns it:
// - none for the filter of a NOT NULL assertion (see BagsKeyTermAttribute);
// - NOT_NULL_COLUMNS: the null tests in P's body of the columns that are
//   never null in the rows of A are decided (assumeNonNull);
// - FILTER_TRUE and FILTER_FALSE, for a body that is a constant;
// - FILTER_NULLABLE_TRUTH (normalizeTruth);
// - FILTER_CONFLICTING_CONSTANTS: empty when conjuncts fix one term to two
//   constants, and otherwise the conjuncts that other conjuncts imply go;
// - FILTER_FALSE, for a conjunct next to its negation;
// - CANONICAL_VARIABLE (canonicalLambda);
// - FILTER_CONST, FILTER_BAG_MAKE and FILTER_UNION_DISJOINT, for A a
//   constant, a (bag x c) or a bag.union_disjoint;
// - FILTER_MAP, for A a map (rewriteFilterOfMap);
// - AGGREGATE_KEYED, for A an aggregate, or a product with aggregates among
//   its components (keyedAggregateRows, reachedComponents).
// The rules that simplify P come before those that read the shape of A, so
// the latter see only a P that the former leave as it is.
// For X : (Bag (Tuple Int Int)),
//   (bag.filter
//     (lambda ((t (Tuple Int Int)))
//       (and (= ((_ tuple.select 0) t) 1) (= ((_ tuple.select 0) t) 2)))
//     X)
//   ---> (as bag.empty (Bag (Tuple Int Int)))  (FILTER_CONFLICTING_CONSTANTS)
BagsRewriteResponse BagsRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  Node P = n[0];
  Node A = n[1];
  if (n.getAttribute(BagsKeyTermAttribute()))
  {
    // The filter of a NOT NULL assertion, which states that a column of a
    // table X is never null, as
    //   (= (bag.filter (lambda ((t (Tuple Int (Nullable Int))))
    //                    (= ((_ tuple.select 1) t)
    //                       (as nullable.null (Nullable Int))))
    //                  X)
    //      (as bag.empty (Bag (Tuple Int (Nullable Int)))))
    // recordNotNull read the fact off it and marked it. Rewriting it by the
    // fact would make the assertion true and lose the fact, so it stays.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  TypeNode t = A.getType();
  {
    // NOT_NULL_COLUMNS: nonNullColumns reads off the shape of A the columns
    // that no row of A has null in, as column 1 of
    // A : (Bag (Tuple Int (Nullable Int))) given an assertion that it is NOT
    // NULL. In the body of p, P as a lambda (see asLambda), assumeNonNull
    // decides the null tests of these columns of p's variable t:
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true. The filter by
    // the new body keeps the same rows, as the tests had these values on all.
    Node p = asLambda(P);
    if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1
        && A.getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(p[1], p[0][0], nonNullColumns(A));
      if (b != p[1])
      {
        Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(p[0][0], b), A);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  {
    Node lambda = asLambda(P);
    if (lambda.getKind() == Kind::LAMBDA && lambda[1].isConst())
    {
      // FILTER_TRUE and FILTER_FALSE: a predicate whose body is true keeps
      // every row, and one whose body is false keeps none. The rewriter turns
      // a lambda with a constant body into a function array constant, which
      // asLambda turns back into the lambda; P may also be a lambda node.
      if (lambda[1].getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
  }
  if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
  {
    // FILTER_NULLABLE_TRUTH: SQL's three-valued truth value is a
    // (Nullable Bool) b, and a row passes when b is (nullable.some true),
    // not when it is (nullable.some false) or null. The body may say so by
    // the two conjuncts (nullable.is_some b) and (nullable.val b);
    // normalizeTruth replaces them by the one formula they state, so that
    // predicates that say the same in either way become one term.
    Node truth = normalizeTruth(P[1]);
    if (truth != P[1])
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], truth), A);
      return BagsRewriteResponse(ret, Rewrite::FILTER_NULLABLE_TRUTH);
    }
  }
  if (P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1)
  {
    Node body = P[1];
    if (body.isConst())
    {
      // FILTER_TRUE and FILTER_FALSE again. The test above already returns
      // for a lambda node with a constant body (asLambda leaves a lambda as
      // it is), so this branch is not reached.
      if (body.getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
    {
      // cs: the conjuncts of the body, or the body itself when it is not an
      // and
      std::vector<Node> cs;
      if (body.getKind() == Kind::AND)
      {
        cs.insert(cs.end(), body.begin(), body.end());
      }
      else
      {
        cs.push_back(body);
      }
      // flat: the conjuncts that the rules below read
      std::vector<Node> flat = cs;
      // FILTER_CONFLICTING_CONSTANTS, first part: a conjunct (= a c), or
      // (= c a), with c a constant and a not, fixes the term a to c. When two
      // conjuncts fix one term to two distinct constants, no row passes and
      // the filter is empty; constants are in a normal form, so two distinct
      // constant nodes are two distinct values. fixed maps each term that a
      // conjunct fixes to its constant.
      std::map<Node, Node> fixed;
      for (const Node& c : flat)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        bool leftConst = c[0].isConst();
        bool rightConst = c[1].isConst();
        // an equality of two constants, or of two terms that are not, fixes
        // nothing
        if (leftConst == rightConst)
        {
          continue;
        }
        Node a = c[0].isConst() ? c[1] : c[0];
        Node v = c[0].isConst() ? c[0] : c[1];
        auto it = fixed.find(a);
        if (it == fixed.end())
        {
          fixed[a] = v;
        }
        else if (it->second != v)
        {
          return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                     Rewrite::FILTER_CONFLICTING_CONSTANTS);
        }
      }
      // nonNull: the terms that a membership conjunct puts in a column that is
      // never null. For (>= (bag.count (tuple a e) Y) 1) and column 1 of Y
      // never null (see nonNullColumns), the row (tuple a e) is in Y, so e is
      // not null.
      std::set<Node> nonNull;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && c[0].getKind() == Kind::BAG_COUNT
            && c[0][0].getKind() == Kind::APPLY_CONSTRUCTOR
            && c[0][1].getType().getBagElementType().isTuple())
        {
          std::set<uint32_t> nn = nonNullColumns(c[0][1]);
          for (uint32_t k : nn)
          {
            if (k < c[0][0].getNumChildren())
            {
              nonNull.insert(c[0][0][k]);
            }
          }
        }
      }
      // FILTER_CONFLICTING_CONSTANTS, second part: a conjunct that other
      // conjuncts imply goes. These are
      // - a tester of the constructor of the constant that fixed maps its
      //   argument to, as (nullable.is_some a) next to (= a (nullable.some 5));
      // - (nullable.is_some e), or (not (= (as nullable.null (Nullable Int))
      //   e)) either way round, for e in nonNull;
      // - (>= (* a b) 1), of integers, next to (>= a 1) and (>= b 1): a
      //   product of positive integers is positive. Such a conjunct tests that
      //   the product of the counts of rows of two groups is positive.
      // positive holds the integer terms a of the conjuncts (>= a 1).
      std::set<Node> positive;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && c[0].getType().isInteger())
        {
          positive.insert(c[0]);
        }
      }
      std::vector<Node> kept;
      for (const Node& c : flat)
      {
        if (c.getKind() == Kind::GEQ && c[1].isConst()
            && c[1].getConst<Rational>() == Rational(1)
            && (c[0].getKind() == Kind::MULT
                || c[0].getKind() == Kind::NONLINEAR_MULT))
        {
          // the product goes when every factor is in positive
          bool implied = true;
          for (const Node& m : c[0])
          {
            implied = implied && positive.count(m) > 0;
          }
          if (implied)
          {
            continue;
          }
        }
        // ci is the index of the constructor that c tests a for, when c is a
        // tester, and -1 otherwise
        Node a;
        int ci = datatypes::utils::isTester(c, a);
        auto it = ci >= 0 ? fixed.find(a) : fixed.end();
        if (it != fixed.end() && it->second.getKind() == Kind::APPLY_CONSTRUCTOR
            && datatypes::utils::indexOf(it->second.getOperator())
                   == static_cast<size_t>(ci))
        {
          // a is fixed to a constant of the constructor that c tests for
          continue;
        }
        if (ci >= 0 && nonNull.count(a) && a.getType().isNullable()
            && a.getType().getDType()[ci].getNumArgs() == 1)
        {
          // c tests a, which is not null, for nullable.some, the constructor
          // of a nullable sort that has an argument
          continue;
        }
        if (c.getKind() == Kind::NOT && c[0].getKind() == Kind::EQUAL
            && ((isNullConstant(c[0][0]) && nonNull.count(c[0][1]))
                || (isNullConstant(c[0][1]) && nonNull.count(c[0][0]))))
        {
          continue;
        }
        kept.push_back(c);
      }
      // when a conjunct went, the filter by the others, or by true when none
      // is left
      if (kept.size() < flat.size())
      {
        Node newBody =
            kept.empty()
                ? d_nm->mkConst(true)
                : (kept.size() == 1 ? kept[0] : d_nm->mkNode(Kind::AND, kept));
        Node ret =
            d_nm->mkNode(Kind::BAG_FILTER, mkLambda(P[0][0], newBody), A);
        return BagsRewriteResponse(ret, Rewrite::FILTER_CONFLICTING_CONSTANTS);
      }
    }
    if (body.getKind() == Kind::AND)
    {
      // FILTER_FALSE: no row passes a conjunct c and its negation (not c),
      // so a body (and .. c .. (not c) ..) makes the filter empty
      std::unordered_set<Node> present(body.begin(), body.end());
      for (const Node& c : body)
      {
        if (c.getKind() == Kind::NOT && present.count(c[0]))
        {
          return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                     Rewrite::FILTER_FALSE);
        }
      }
    }
    // CANONICAL_VARIABLE: P with its variable renamed to t_N, N the id of P's
    // alpha key, a node that is the same for lambdas that differ only in the
    // names of their variables (see canonicalLambda), so that such lambdas
    // become one node
    Node canonical = canonicalLambda(P);
    if (canonical != P)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, canonical, A);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  if (A.isConst())
  {
    // (bag.filter p (as bag.empty (Bag T)) = (as bag.empty (Bag T))
    // (bag.filter p (bag "a" 3) ((bag "b" 2))) =
    //   (bag.union_disjoint
    //     (ite (p "a") (bag "a" 3) (as bag.empty (Bag T)))
    //     (ite (p "b") (bag "b" 2) (as bag.empty (Bag T)))

    Node ret = BagsUtils::evaluateBagFilter(n);
    return BagsRewriteResponse(ret, Rewrite::FILTER_CONST);
  }
  Kind k = A.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // FILTER_BAG_MAKE: x is kept as often as it occurs when it passes, and
      // not at all otherwise. The result is a bag of x again, with an ite as
      // its count, rather than an ite of two bags, so that a map or a product
      // over it still has a (bag x ..) to apply its rules to:
      //   (bag.filter p (bag x y)) ---> (bag x (ite (p x) y 0))
      Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, A[0]);
      Node count = d_nm->mkNode(Kind::ITE, pOfe, A[1], d_zero);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, A[0], count);
      return BagsRewriteResponse(ret, Rewrite::FILTER_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.filter p (bag.union_disjoint A B)) =
      //    (bag.union_disjoint (bag.filter p A) (bag.filter p B))
      Node a = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::FILTER_UNION_DISJOINT);
    }

    // FILTER_MAP: a filter of a map is a map of a filter, by the predicate of
    // the image of each row, when both functions are lambdas and with the
    // higher-order flag (see rewriteFilterOfMap, which returns n otherwise)
    case Kind::BAG_MAP: return rewriteFilterOfMap(n);
    case Kind::TABLE_AGGREGATE:
    {
      // AGGREGATE_KEYED, for A = ((_ table.aggr K) f i Y). The aggregate of an
      // empty Y is one row, the row of initial values i, which SQL's GROUP BY
      // does not have; P drops that row when (P i) rewrites to false (see
      // rejectsInitialRow). When K contains a key of Y, columns on which no
      // two rows of Y agree, every group is one row t of Y, folded once, so
      // the aggregate's other rows are (bag.map (lambda ((t ..)) (f t i)) Y)
      // (see keyedAggregateRows, null when K holds no key), and the filter of
      // that map keeps the same rows.
      if (rejectsInitialRow(n[0], A[1]))
      {
        Node rows = keyedAggregateRows(A);
        if (!rows.isNull())
        {
          Node ret = d_nm->mkNode(Kind::BAG_FILTER, n[0], rows);
          return BagsRewriteResponse(ret, Rewrite::AGGREGATE_KEYED);
        }
      }
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    case Kind::TABLE_PRODUCT:
    {
      {
        // AGGREGATE_KEYED, for A a product. The components of A are the
        // factors of the right-nested product, G, Y and Z for
        // (table.product G (table.product Y Z)), and starts holds the column
        // of A's rows at which the columns of each component start. An
        // aggregate among them has a row of initial values when its input is
        // empty; a component is "reached" when no row that passes P has that
        // row in its columns, as when P tests the component's count of rows
        // positive (see reachedComponents). A reached aggregate grouped by a
        // key of its input is replaced by the rows of its groups, as in the
        // case above (see keyedAggregateRows): the rows of A that this drops
        // do not pass P.
        std::vector<Node> comps;
        std::vector<size_t> starts;
        Node rest = A;
        size_t at = 0;
        // collect the components from left to right; tuples is false when a
        // component's rows are not tuples, and then nothing is done
        bool tuples = true;
        while (tuples)
        {
          Node c = rest.getKind() == Kind::TABLE_PRODUCT ? rest[0] : rest;
          tuples = c.getType().getBagElementType().isTuple();
          comps.push_back(c);
          starts.push_back(at);
          if (!tuples || rest.getKind() != Kind::TABLE_PRODUCT)
          {
            break;
          }
          at += c.getType().getBagElementType().getTupleLength();
          rest = rest[1];
        }
        if (tuples)
        {
          // reached[c] is nonzero for a reached component c; test, which
          // gives the conjunct of P that tests each component's count, is not
          // read here
          std::vector<int> test;
          std::vector<int> reached =
              reachedComponents(n[0], comps, starts, test);
          bool changed = false;
          for (size_t c = 0; c < comps.size(); c++)
          {
            if (reached[c] && comps[c].getKind() == Kind::TABLE_AGGREGATE)
            {
              // null when the group columns hold no key of the input
              Node rows = keyedAggregateRows(comps[c]);
              if (!rows.isNull())
              {
                comps[c] = rows;
                changed = true;
              }
            }
          }
          if (changed)
          {
            // the right-nested product of the new components, built from the
            // last one leftwards, under the same filter
            Node prod = comps.back();
            for (size_t pos = comps.size() - 1; pos-- > 0;)
            {
              prod = d_nm->mkNode(Kind::TABLE_PRODUCT, comps[pos], prod);
            }
            Node ret = d_nm->mkNode(Kind::BAG_FILTER, n[0], prod);
            return BagsRewriteResponse(ret, Rewrite::AGGREGATE_KEYED);
          }
        }
      }
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
}

// For a filter predicate P over the rows of a product of the components
// comps, those of comps[c] starting at column starts[c]: which components are
// reached. An aggregate ((_ table.aggr K) f i X) of an empty X is one row of
// initial values i; a component is reached when no row that passes P has
// that row in the component's columns, only groups of rows of its input. The
// result holds per component
// - 1 when P tests the aggregate's counter column, which counts the rows of
//   each group by (+ ((_ tuple.select c) acc) 1) from 0, to be at least 1;
//   test[c] is then the index of that conjunct of P (and -1 when there is
//   none);
// - 2 when P equates the copy of each group column in the aggregate's rows
//   with the copy of the matching group column of a reached aggregate, and
//   the inputs of the two have one set of group values;
// - 0 otherwise, also for an aggregate that does not copy all its group
//   columns to its rows.
// For X : (Bag (Tuple Int Int)),
// G1 = ((_ table.aggr 0) f i X) and G2 = ((_ table.aggr 0) g j X), each with
// rows of three columns that copy group column 0 to column 0 and count the
// rows of the group in column 2, and
//   P = (lambda ((t (Tuple Int Int Int Int Int Int)))
//         (and (>= ((_ tuple.select 2) t) 1)
//              (= ((_ tuple.select 0) t) ((_ tuple.select 3) t))))
// over (table.product G1 G2), with starts {0, 3}, the result is {1, 2} and
// test is {0, -1}: G1's count is tested, and every group of G2 that a reached
// group of G1 meets has a row of X, with the same group values as that group.
std::vector<int> BagsRewriter::reachedComponents(
    const Node& P,
    const std::vector<Node>& comps,
    const std::vector<size_t>& starts,
    std::vector<int>& test) const
{
  std::vector<int> reached(comps.size(), 0);
  test.assign(comps.size(), -1);
  // nothing is reached unless P is a lambda of one variable r, and without
  // the rewriter, which keySet below needs
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || d_rewriter == nullptr)
  {
    return reached;
  }
  Node r = lambda[0][0];
  // the conjuncts of P's body, or the body itself when it is not an and
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  // First the components reached by a test of their counter (1). Only an
  // aggregate A = ((_ table.aggr K) f i X) whose step f is a lambda of a row
  // t and an accumulator acc, with a tuple as its body, is considered.
  std::vector<std::map<uint32_t, size_t>> keyAt(comps.size());
  std::vector<bool> keyed(comps.size(), false);
  for (size_t c = 0; c < comps.size(); c++)
  {
    const Node& A = comps[c];
    if (A.getKind() != Kind::TABLE_AGGREGATE)
    {
      continue;
    }
    Node f = asLambda(A[0]);
    if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
        || !isTupleTerm(f[1]))
    {
      continue;
    }
    // K, the group columns of A, are columns of X
    const std::vector<uint32_t>& K =
        A.getOperator().getConst<ProjectOp>().getIndices();
    for (size_t q = 0; q < f[1].getNumChildren(); q++)
    {
      const Node& e = f[1][q];
      if (e.getKind() == Kind::APPLY_SELECTOR && e[0] == f[0][0])
      {
        uint32_t k = datatypes::utils::indexOf(e.getOperator());
        if (std::find(K.begin(), K.end(), k) != K.end() && !keyAt[c].count(k))
        {
          keyAt[c][k] = q;
        }
      }
    }
    // keyAt[c] maps each group column k to the first column q of A's rows
    // that copies it, the q-th component of f's tuple being
    // ((_ tuple.select k) t). keyed[c] holds when K is not empty and every
    // group column has such a copy; the other components are never reached.
    keyed[c] =
        !K.empty()
        && keyAt[c].size() == std::set<uint32_t>(K.begin(), K.end()).size();
    if (!keyed[c])
    {
      continue;
    }
    // A conjunct (>= ((_ tuple.select pos) r) 1) of P, with pos among the w
    // columns of component c, tests column pos - starts[c] of A's own rows.
    // local is that test as a predicate over A's rows, with the row variable
    // of their sort; counterColumn says whether that column counts the rows
    // of each group, by (+ ((_ tuple.select q) acc) 1) from 0. The row of
    // initial values has 0 in it and fails the test.
    Node row = rowVariable(A.getType().getBagElementType());
    for (size_t k = 0; k < conjuncts.size(); k++)
    {
      const Node& d = conjuncts[k];
      if (d.getKind() != Kind::GEQ || !d[1].isConst()
          || d[1].getConst<Rational>() != Rational(1)
          || d[0].getKind() != Kind::APPLY_SELECTOR || d[0][0] != r)
      {
        continue;
      }
      size_t pos = datatypes::utils::indexOf(d[0].getOperator());
      size_t w = A.getType().getBagElementType().getTupleLength();
      if (pos < starts[c] || pos >= starts[c] + w)
      {
        continue;
      }
      Node local = mkLambda(
          row,
          d_nm->mkNode(
              Kind::GEQ,
              datatypes::TupleUtils::nthElementOfTuple(row, pos - starts[c]),
              d_one));
      if (counterColumn(local, f, A[1]) == static_cast<int>(pos - starts[c]))
      {
        // with several such conjuncts, test[c] is the last one
        test[c] = static_cast<int>(k);
        reached[c] = 1;
      }
    }
  }
  // equated(a, b): whether a conjunct of P is
  // (= ((_ tuple.select a) r) ((_ tuple.select b) r)), either way round
  auto equated = [&](size_t a, size_t b) {
    for (const Node& e : conjuncts)
    {
      if (e.getKind() == Kind::EQUAL && e[0].getKind() == Kind::APPLY_SELECTOR
          && e[1].getKind() == Kind::APPLY_SELECTOR && e[0][0] == r
          && e[1][0] == r)
      {
        size_t x0 = datatypes::utils::indexOf(e[0].getOperator());
        size_t x1 = datatypes::utils::indexOf(e[1].getOperator());
        if ((x0 == a && x1 == b) || (x0 == b && x1 == a))
        {
          return true;
        }
      }
    }
    return false;
  };
  // keySet(c): the set of the values that the group columns K take in the
  // input X of the keyed component c, in the order of K, as a rewritten term,
  // cached in keySets. For group column 0 of X : (Bag (Tuple Int Int)), it
  // is the rewrite of
  //   (bag.setof
  //     (bag.map (lambda ((s (Tuple Int Int))) (tuple ((_ tuple.select 0) s)))
  //              X))
  // Two components whose sets rewrite to one term have the same group
  // values, so the input of one is empty exactly when that of the other is.
  std::map<size_t, Node> keySets;
  auto keySet = [&](size_t c) {
    auto it = keySets.find(c);
    if (it != keySets.end())
    {
      return it->second;
    }
    const Node& A = comps[c];
    const std::vector<uint32_t>& K =
        A.getOperator().getConst<ProjectOp>().getIndices();
    Node X = A[2];
    Node xr = rowVariable(X.getType().getBagElementType());
    std::vector<Node> cols;
    std::vector<TypeNode> types;
    for (uint32_t k : K)
    {
      cols.push_back(datatypes::TupleUtils::nthElementOfTuple(xr, k));
      types.push_back(cols.back().getType());
    }
    TypeNode kt = d_nm->mkTupleType(types);
    Node m =
        d_nm->mkNode(Kind::BAG_MAP,
                     mkLambda(xr,
                              datatypes::TupleUtils::constructTupleFromElements(
                                  kt, cols, 0, cols.size() - 1)),
                     X);
    Node ks = d_rewriter->rewrite(d_nm->mkNode(Kind::BAG_SETOF, m));
    keySets[c] = ks;
    return ks;
  };
  // Then the components reached through a join (2): a keyed component j with
  // a reached keyed component i such that both have as many group columns,
  // P equates the copy of the m-th group column of i with that of j, for
  // every m, and keySet(i) and keySet(j) are one term. In a row that passes
  // P, i's columns hold a group of rows of i's input, so that input is not
  // empty, nor is j's, and j has no row of initial values. A component
  // marked 2 may let another one be reached, so this repeats until nothing
  // changes.
  bool changed = true;
  while (changed)
  {
    changed = false;
    for (size_t j = 0; j < comps.size(); j++)
    {
      if (reached[j] || !keyed[j])
      {
        continue;
      }
      for (size_t i = 0; i < comps.size() && !reached[j]; i++)
      {
        if (i == j || !reached[i] || !keyed[i])
        {
          continue;
        }
        const std::vector<uint32_t>& Ki =
            comps[i].getOperator().getConst<ProjectOp>().getIndices();
        const std::vector<uint32_t>& Kj =
            comps[j].getOperator().getConst<ProjectOp>().getIndices();
        if (Ki.size() != Kj.size())
        {
          continue;
        }
        bool joined = true;
        for (size_t m = 0; m < Ki.size() && joined; m++)
        {
          joined =
              equated(starts[i] + keyAt[i][Ki[m]], starts[j] + keyAt[j][Kj[m]]);
        }
        if (!joined)
        {
          continue;
        }
        Node keysI = keySet(i);
        Node keysJ = keySet(j);
        if (keysI == keysJ)
        {
          reached[j] = 2;
          changed = true;
        }
      }
    }
  }
  return reached;
}

BagsRewriteResponse BagsRewriter::postRewriteAll(TNode n)
{
  Assert(n.getKind() == Kind::BAG_ALL);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.all p (as bag.empty (Bag T)) = true)
      return BagsRewriteResponse(nm->mkConst(true), Rewrite::ALL_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.all p (bag x n)) = (or (p x) (<= n 0)
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::LEQ, n[1][1], d_zero);
      Node ret = px.orNode(leq);
      return BagsRewriteResponse(ret, Rewrite::ALL_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.all p (bag.union_disjoint A B)) =
      //   (and (bag.all p A) (bag.all p B))
      Node a = nm->mkNode(Kind::BAG_ALL, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_ALL, n[0], n[1][1]);
      Node ret = a.andNode(b);
      return BagsRewriteResponse(ret, Rewrite::ALL_UNION_DISJOINT);
    }
    default:
    {
      // (bag.all p A) is rewritten as (bag.filter p A) = A
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node all = filter.eqNode(n[1]);
      return BagsRewriteResponse(all, Rewrite::ALL_FILTER);
    }
  }
}

BagsRewriteResponse BagsRewriter::postRewriteSome(TNode n)
{
  Assert(n.getKind() == Kind::BAG_SOME);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::BAG_EMPTY:
    {
      // (bag.some p (as bag.empty (Set T)) = false)
      return BagsRewriteResponse(nm->mkConst(false), Rewrite::SOME_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // (bag.some p (bag x n)) = (and (> n 0) (p x))
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::GT, n[1][1], d_zero);
      Node ret = px.andNode(leq);
      return BagsRewriteResponse(ret, Rewrite::SOME_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // (bag.some p (bag.union_disjoint A B)) =
      //   (or (bag.some p A) (bag.union_disjoint p B))
      Node a = nm->mkNode(Kind::BAG_SOME, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_SOME, n[0], n[1][1]);
      Node ret = a.orNode(b);
      return BagsRewriteResponse(ret, Rewrite::SOME_UNION_DISJOINT);
    }
    default:
    {
      // (bag.some p A) is rewritten as (distinct (bag.filter p A) bag.empty))
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node empty = nm->mkConst(EmptyBag(n[1].getType()));
      Node some = filter.eqNode(empty).notNode();
      return BagsRewriteResponse(some, Rewrite::SOME_FILTER);
    }
  }
}

// The rules for (bag.fold f t X), the step f folded over the rows of X from
// the initial value t (X is bag in the code), tried in this order; the first
// that applies returns:
// - FOLD_CONST, for X a constant, and FOLD_BAG, for X = (bag x c) with c a
//   positive constant: the fold is evaluated or unrolled;
// - NOT_NULL_COLUMNS, for f a lambda of a row and an accumulator, over rows
//   of tuples (assumeNonNull);
// - FOLD_TUPLE (rewriteFoldOfTuple);
// - FOLD_CONSTANT_STEP;
// - FOLD_UNION_DISJOINT, for X a bag.union_disjoint;
// - CANONICAL_VARIABLE (canonicalLambda), for f a lambda node.
// Any other X, a (bag x c) with c not a constant among them, goes on past
// FOLD_BAG. For X : (Bag Int),
//   (bag.fold (lambda ((t Int) (acc Int)) 7) 0 X)
//   ---> (ite (= X (as bag.empty (Bag Int))) 0 7)        (FOLD_CONSTANT_STEP)
BagsRewriteResponse BagsRewriter::postRewriteFold(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  Node f = n[0];
  Node t = n[1];
  Node bag = n[2];
  if (bag.isConst())
  {
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  if (bag.getKind() == Kind::BAG_MAKE && bag[1].isConst()
      && bag[1].getConst<Rational>() > Rational(0))
  {
    // (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times, n > 0
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_BAG);
  }
  {
    // l is f as a lambda, also when f is a function array constant (see
    // asLambda); its two variables are the row l[0][0] and the accumulator
    // l[0][1]
    Node l = asLambda(f);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2)
    {
      if (bag.getType().getBagElementType().isTuple())
      {
        // NOT_NULL_COLUMNS: in the step's body, the null tests of the columns
        // of the row that no row of X has null in (see nonNullColumns) are
        // decided, as (nullable.is_some ((_ tuple.select 1) t)) becomes true
        // for column 1 never null (see assumeNonNull). The new lambda keeps
        // f's variables, l[0].
        Node b = assumeNonNull(l[1], l[0][0], nonNullColumns(bag));
        if (b != l[1])
        {
          Node ret = d_nm->mkNode(
              Kind::BAG_FOLD, d_nm->mkNode(Kind::LAMBDA, l[0], b), t, bag);
          return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
        }
      }
    }
  }
  {
    // FOLD_TUPLE: a fold whose accumulator is a tuple, and whose step computes
    // each component from that component of the accumulator only, is the
    // tuple of the folds of the components (see rewriteFoldOfTuple, which
    // returns n when the rule does not apply)
    BagsRewriteResponse r = rewriteFoldOfTuple(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // FOLD_CONSTANT_STEP: a step c that reads neither the row nor the
    // accumulator gives c after any row, and the fold of no row is the
    // initial value t, so the fold is (ite (= X (as bag.empty ..)) t c)
    Node lambda = asLambda(f);
    if (lambda.getKind() == Kind::LAMBDA && lambda[0].getNumChildren() == 2
        && !occursFree(lambda[1], lambda[0][0])
        && !occursFree(lambda[1], lambda[0][1]))
    {
      Node empty = d_nm->mkConst(EmptyBag(bag.getType()));
      Node ret = d_nm->mkNode(Kind::ITE, bag.eqNode(empty), t, lambda[1]);
      return BagsRewriteResponse(ret, Rewrite::FOLD_CONSTANT_STEP);
    }
  }
  if (bag.getKind() == Kind::BAG_UNION_DISJOINT)
  {
    // (bag.fold f t (bag.union_disjoint A B)) =
    //       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry
    Node A = bag[0] < bag[1] ? bag[0] : bag[1];
    Node B = bag[0] < bag[1] ? bag[1] : bag[0];
    Node foldA = d_nm->mkNode(Kind::BAG_FOLD, f, t, A);
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, f, foldA, B);
    return BagsRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
  }
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N
    // the id of f's alpha key, a node that is the same for lambdas that differ
    // only in the names of their variables (see canonicalLambda)
    Node canonical = canonicalLambda(f);
    if (canonical != f)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FOLD, canonical, t, bag);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewritePartition(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_PARTITION);
  if (n[1].isConst())
  {
    Node ret = BagsUtils::evaluateBagPartition(d_rewriter, n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::PARTITION_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rules for ((_ table.aggr K) f i X): X split into groups, the rows that
// agree on the columns K, and each group folded by the step f from the
// initial value i into one row. They are tried in this order; the first that
// applies returns:
// - NOT_NULL_COLUMNS, for f a lambda of a row and an accumulator, over rows
//   of tuples (assumeNonNull);
// - AGGREGATE_NO_KEYS, for K empty: one group, all of X;
// - AGGREGATE_SORT_OUTPUT (rewriteAggregateSortOutput);
// - CANONICAL_VARIABLE (canonicalLambda), for f a lambda node;
// - AGGREGATE_MAP, for X a map (rewriteAggregateOfMap);
// - AGGREGATE_CONST, for i and X constants: the aggregate is evaluated.
// The rules after AGGREGATE_NO_KEYS see only a K that is not empty. For
// X : (Bag (Tuple Int Int)) and
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int)))
//         (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t)))),
//   (table.aggr f (tuple 0) X)
//   ---> (bag (bag.fold f (tuple 0) X) 1)                 (AGGREGATE_NO_KEYS)
BagsRewriteResponse BagsRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);

  {
    // NOT_NULL_COLUMNS: in the body of f, as a lambda (see asLambda), the null
    // tests of the columns of the row f[0][0] that no row of X has null in
    // (see nonNullColumns) are decided, as
    // (nullable.is_some ((_ tuple.select 1) t)) becomes true for column 1
    // never null (see assumeNonNull). The new aggregate keeps f's variables
    // and the operator (_ table.aggr K), its first child.
    Node f = asLambda(n[0]);
    if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2
        && n[2].getType().getBagElementType().isTuple())
    {
      Node b = assumeNonNull(f[1], f[0][0], nonNullColumns(n[2]));
      if (b != f[1])
      {
        Node lambda = d_nm->mkNode(Kind::LAMBDA, f[0], b);
        std::vector<Node> children{n.getOperator(), lambda, n[1], n[2]};
        Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
        return BagsRewriteResponse(ret, Rewrite::NOT_NULL_COLUMNS);
      }
    }
  }
  if (n.getOperator().getConst<ProjectOp>().getIndices().empty())
  {
    // AGGREGATE_NO_KEYS: grouping by no column makes one group, all of X, also
    // when X is empty (table.group by no column of an empty table is one
    // empty part), so the result is that group folded, once:
    //   (table.aggr f i X) ---> (bag (bag.fold f i X) 1)
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, n[0], n[1], n[2]);
    Node ret = d_nm->mkNode(Kind::BAG_MAKE, fold, d_one);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_NO_KEYS);
  }
  {
    // AGGREGATE_SORT_OUTPUT: the columns of the aggregate's rows in one
    // order, the copies of the group columns first, under a map that puts
    // them back, so that two aggregates that compute the same columns in two
    // orders become one aggregate (see rewriteAggregateSortOutput, which
    // returns n when the rule does not apply)
    BagsRewriteResponse r = rewriteAggregateSortOutput(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE: f with its variables renamed to t_N and acc_N, N
    // the id of f's alpha key, a node that is the same for lambdas that differ
    // only in the names of their variables (see canonicalLambda)
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      std::vector<Node> children{n.getOperator(), canonical, n[1], n[2]};
      Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  if (n[2].getKind() == Kind::BAG_MAP)
  {
    // AGGREGATE_MAP: for X = (bag.map g Y), the aggregate of Y, grouped by
    // the columns of Y that g copies to the group columns, with g read inside
    // the step; only for a step whose value does not depend on the order of
    // the rows (see rewriteAggregateOfMap)
    BagsRewriteResponse r = rewriteAggregateOfMap(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  // AGGREGATE_CONST: the aggregate of a constant table, from a constant
  // initial value, is evaluated
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = BagsUtils::evaluateTableAggregate(n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// The rule for (table.product X Y), every row of X followed by the columns
// of every row of Y:
// - PRODUCT_EMPTY: a product with the empty table on either side is empty.
// (A product of two constants is evaluated before, see postRewrite.)
// For X : (Bag (Tuple Int)),
//   (table.product X (as bag.empty (Bag (Tuple Int))))
//   ---> (as bag.empty (Bag (Tuple Int Int)))                 (PRODUCT_EMPTY)
BagsRewriteResponse BagsRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyBag(tableType));
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // PRODUCT_EMPTY: a product with the empty table is empty, here the empty
    // table of the product's sort, whose rows have the columns of both sides
    return BagsRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// Returns the bound variable that the rules use for a row of sort tupleType
// when they build a lambda over the rows of a bag. There is one such
// variable per sort: every call with (Tuple Int Int) returns the same
// variable row_N : (Tuple Int Int), where N is the node id of the constant
// (as bag.empty (Bag (Tuple Int Int))). So two lambdas that the rules build
// for the same operation, as
//   (lambda ((row_N (Tuple Int Int))) ((_ tuple.project 1 0) row_N))
// for the same projection, are one node, and purification turns them into
// one function symbol. Any sort works, not only a tuple sort (lambdaOf
// passes the argument sort of any function).
Node BagsRewriter::rowVariable(TypeNode tupleType) const
{
  // The empty bag of the row sort is a constant that only this sort has; the
  // variable is cached on the role "row" and that key (see mkRewriterVar).
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(tupleType)));
  return mkRewriterVar(
      d_nm, "row", key, "row_" + std::to_string(key.getId()), tupleType);
}

// Whether some closure in body (a lambda, a quantifier, or any other binder,
// body itself included) has var among its bound variables. It says nothing
// about free occurrences of var. Callers test it before they substitute for
// var in body, because Node::substitute is syntactic: it would also replace
// the occurrences of var that such an inner closure binds. For
// t : (Tuple Int Int) and X : (Bag (Tuple Int Int)), it is true for the body
//   (>= (bag.count ((_ tuple.project 0) t)
//                  (bag.map (lambda ((t (Tuple Int Int)))
//                             ((_ tuple.project 1) t))
//                           X))
//       1)
// whose inner lambda binds t again, and false for (> ((_ tuple.select 0) t) 3).
bool BagsRewriter::bindsVariable(const Node& body, const Node& var) const
{
  // Visit each node of the DAG of body once; a leaf binds nothing.
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo = {body};
  while (!todo.empty())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second || cur.getNumChildren() == 0)
    {
      continue;
    }
    if (cur.isClosure())
    {
      // The first child of a closure is the list of the variables it binds.
      for (const TNode& v : cur[0])
      {
        if (v == var)
        {
          return true;
        }
      }
    }
    for (const TNode& c : cur)
    {
      todo.push_back(c);
    }
  }
  return false;
}

// Whether the bound variable v occurs free in n, that is, somewhere outside
// every closure of n that binds v. For t : (Tuple Int Int) and
// X : (Bag (Tuple Int Int)), it is true for
//   ((_ tuple.select 0) t)
// and false for
//   (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.select 0) t)) X)
// whose only occurrence of t is bound by the lambda.
bool BagsRewriter::occursFree(const Node& n, const Node& v) const
{
  // Cheap test first: a term that does not contain v has no free v.
  if (!expr::hasSubterm(n, v))
  {
    return false;
  }
  // Otherwise collect the bound variables that occur free in n.
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(n, fvs);
  return fvs.find(v) != fvs.end();
}

// Returns f as a lambda when f is a function array constant, and f itself
// otherwise (a lambda, or a function symbol such as a declared function).
// The rewriter stores a lambda whose body is a constant, or an ite over
// constants, as a function array constant (kind FUNCTION_ARRAY_CONST), so a
// rule that needs the variable and the body of a lambda reads such an f back
// first. For example, the predicate of the filter that keeps every row,
//   (lambda ((t (Tuple Int Int))) true),
// is a function array constant, and asLambda returns this lambda again (with
// a bound variable that FunctionConst::toLambda chooses).
Node BagsRewriter::asLambda(const Node& f) const
{
  if (f.getKind() == Kind::FUNCTION_ARRAY_CONST)
  {
    // toLambda returns the null node when it cannot convert f; f is then
    // returned unchanged.
    Node lambda = uf::FunctionConst::toLambda(f);
    if (!lambda.isNull())
    {
      return lambda;
    }
  }
  return f;
}

// Returns the application (fn x) beta-reduced, i.e. the body of the lambda
// fn with its variable replaced by x. For
//   fn = (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3))
// and x = (tuple a b), it returns
//   (> ((_ tuple.select 1) (tuple a b)) 3),
// which is not rewritten here; the rewriter later simplifies it to (> b 3).
// It returns the null node when the substitution could capture a variable,
// and the unreduced application (fn x), an APPLY_UF, when fn is not a lambda
// of one variable, as a declared function symbol.
Node BagsRewriter::applyFunction(const Node& fn, const Node& x) const
{
  // A function array constant is read as the lambda it stands for.
  Node f = asLambda(fn);
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    TNode var = f[0][0];
    if (var == x)
    {
      // (f var) is the body itself.
      return f[1];
    }
    if (bindsVariable(f[1], var) || bindsVariable(x, var))
    {
      // A closure in f's body that binds var again would have its own
      // occurrences of var replaced too, since substitute is syntactic. The
      // code also gives up when x contains a closure that binds var, which
      // is stricter than avoiding capture requires.
      return Node::null();
    }
    // A closure in f's body must not bind a variable that is free in x:
    // the copies of x placed under it would then refer to its variable.
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(x, fvs);
    for (const Node& v : fvs)
    {
      if (bindsVariable(f[1], v))
      {
        return Node::null();
      }
    }
    return f[1].substitute(var, TNode(x));
  }
  // Not a lambda of one variable: keep the application of the original fn.
  return d_nm->mkNode(Kind::APPLY_UF, fn, x);
}

// Returns the variable and the body of the lambda that the function f stands
// for, as a pair. For a lambda of one variable,
//   f = (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t))),
// it is (t, (tuple ((_ tuple.select 1) t))). For any other f, as a declared
// function h : (-> (Tuple Int Int) (Tuple Int)), it is (row_N, (h row_N)),
// with row_N the row variable of the argument sort (see rowVariable): f is
// then read as (lambda ((row_N (Tuple Int Int))) (h row_N)). f is not read
// through asLambda, so a function array constant also takes the second form;
// the rewriter beta-reduces such an application later.
std::pair<Node, Node> BagsRewriter::lambdaOf(const Node& f) const
{
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    return std::make_pair(f[0][0], f[1]);
  }
  // f has a function sort (-> T R): its variable has the sort T.
  TypeNode domain = f.getType().getArgTypes()[0];
  Node t = rowVariable(domain);
  return std::make_pair(t, d_nm->mkNode(Kind::APPLY_UF, f, t));
}

// Adds to positions the columns of the row var that body reads, a column
// being k in ((_ tuple.select k) var), and returns whether body reads var
// only through such selectors. For t : (Tuple Int Int Int) and
//   body = (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)),
// it adds {0, 2} and returns true. It returns false for (= t (tuple a b)),
// which reads the whole row, and for any occurrence of a var that is not a
// tuple: the selectors of another datatype, as (nullable.val t) for
// t : (Nullable Int), are not columns. A body without var gives true and adds
// nothing. Binders are not looked at, so an occurrence of var bound by a
// closure inside body counts too (callers test bindsVariable for that). On
// false, positions may already hold some columns.
bool BagsRewriter::readPositions(const Node& body,
                                 const Node& var,
                                 std::set<uint32_t>& positions) const
{
  bool tuple = var.getType().isTuple();
  // Visit each node of the DAG of body once.
  std::unordered_set<TNode> visited;
  std::vector<TNode> todo = {body};
  while (!todo.empty())
  {
    TNode cur = todo.back();
    todo.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    if (cur == var)
    {
      // The row itself, reached other than as the argument of a selector:
      // body reads the whole row.
      return false;
    }
    if (tuple && cur.getKind() == Kind::APPLY_SELECTOR && cur[0] == var)
    {
      // ((_ tuple.select k) var): record column k, and do not descend to var.
      positions.insert(datatypes::utils::indexOf(cur.getOperator()));
      continue;
    }
    for (const TNode& c : cur)
    {
      todo.push_back(c);
    }
  }
  return true;
}

// Whether the rules that compose functions, FILTER_MAP and MAP_MAP, may use
// the function f of a filter or a map: f must be a lambda of one variable, or
// a function array constant of one argument (see asLambda), since these rules
// build a new lambda from f's body. True for
//   (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
// and false for a declared function h : (-> (Tuple Int Int) (Tuple Int)).
// A declared function stays as it is, as cvc5 left it before these rules:
// composing it would build (lambda ((t (Tuple Int Int))) (h t)), a lambda
// that the input did not have, around a function whose value the model
// chooses.
bool BagsRewriter::composable(const Node& f) const
{
  Node l = asLambda(f);
  return l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 1;
}

// Returns the lambda of the one variable var with the body body: for
// t : (Tuple Int Int) and the body (> ((_ tuple.select 0) t) 3), it is
//   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3)).
Node BagsRewriter::mkLambda(const Node& var, const Node& body) const
{
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
}

// FILTER_MAP: a filter of a map becomes a map of a filter, which moves
// filters below maps. For n = (bag.filter p (bag.map f A)) with
// p = (lambda ((s S)) b) and f = (lambda ((t T)) e), the new filter keeps the
// rows t of A whose image e satisfies p:
//   (bag.map f (bag.filter (lambda ((t T)) b[s := e]) A)).
// This is sound for bags: the copies of an image y come from the rows t with
// e = y, and p keeps or drops all of them together, as b[s := e] does. For
// X : (Bag (Tuple Int Int)),
//   (bag.filter (lambda ((s (Tuple Int))) (> ((_ tuple.select 0) s) 3))
//               (bag.map (lambda ((t (Tuple Int Int)))
//                          (tuple ((_ tuple.select 1) t)))
//                        X))
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) t)))
//                 (bag.filter (lambda ((t (Tuple Int Int)))
//                               (> ((_ tuple.select 1) t) 3))
//                             X))                          (FILTER_MAP)
// once the rewriter simplifies ((_ tuple.select 0) (tuple ..)) in b[s := e].
BagsRewriteResponse BagsRewriter::rewriteFilterOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a new lambda, which the theory of uninterpreted
    // functions accepts only in a higher-order logic (see the constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // p, the filter's predicate over the rows s of the map; f, the map's
  // function over the rows t of A.
  Node p = n[0];
  Node f = n[1][0];
  Node A = n[1][1];
  if (!composable(p) || !composable(f))
  {
    // A declared function symbol is left alone (see composable).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t and e: the variable of f, a row of A, and f's body, its image.
  std::pair<Node, Node> lf = lambdaOf(f);
  Node t = lf.first;
  // b[s := e], the predicate p applied to the image of t; null when the
  // substitution would capture a variable (see applyFunction).
  Node body = applyFunction(p, lf.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // (bag.filter (lambda ((t T)) b[s := e]) A), under the original map f.
  Node filtered = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), A);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, f, filtered);
  return BagsRewriteResponse(ret, Rewrite::FILTER_MAP);
}

// MAP_MAP: a map of a map becomes one map, by the composition of the two
// functions. For n = (bag.map f (bag.map g A)) with f = (lambda ((s S)) e)
// and g = (lambda ((t T)) d), each row t of A is mapped to e[s := d]:
//   (bag.map (lambda ((t T)) e[s := d]) A).
// It is sound for bags since a row t of A, with its multiplicity, ends as the
// same row f(g(t)) either way. For X : (Bag (Tuple Int Int)),
//   (bag.map (lambda ((s (Tuple Int))) (tuple (+ ((_ tuple.select 0) s) 1)))
//            (bag.map (lambda ((t (Tuple Int Int)))
//                       (tuple ((_ tuple.select 1) t)))
//                     X))
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   (tuple (+ ((_ tuple.select 1) t) 1)))
//                 X)                                       (MAP_MAP)
// once the rewriter simplifies ((_ tuple.select 0) (tuple ..)) in e[s := d].
BagsRewriteResponse BagsRewriter::rewriteMapOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a new lambda, which the theory of uninterpreted
    // functions accepts only in a higher-order logic (see the constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // f, the outer map's function over the rows s of the inner map; g, the
  // inner map's function over the rows t of A.
  Node f = n[0];
  Node g = n[1][0];
  Node A = n[1][1];
  if (!composable(f) || !composable(g))
  {
    // A declared function symbol is left alone (see composable).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t and d: the variable of g, a row of A, and g's body, its image.
  std::pair<Node, Node> lg = lambdaOf(g);
  Node t = lg.first;
  // e[s := d], f applied to the image of t; null when the substitution
  // would capture a variable (see applyFunction).
  Node body = applyFunction(f, lg.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // (bag.map (lambda ((t T)) e[s := d]) A)
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, body), A);
  return BagsRewriteResponse(ret, Rewrite::MAP_MAP);
}

// PROJECT_TO_MAP: a projection of a table becomes the map of tuple.project
// over its rows, with the same columns, so that the rules for maps, as
// MAP_MAP and FILTER_MAP, also apply to projections. For
// X : (Bag (Tuple Int Int)),
//   ((_ table.project 1 0) X)
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   ((_ tuple.project 1 0) t))
//                 X)                                       (PROJECT_TO_MAP)
// where t is the row variable of X's row sort (see rowVariable), so that
// two equal projections become one lambda.
BagsRewriteResponse BagsRewriter::postRewriteProject(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // The rule builds a lambda where the term has none, which the theory of
    // uninterpreted functions accepts only in a higher-order logic (see the
    // constructor).
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Assert(n.getKind() == Kind::TABLE_PROJECT);
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  // The columns of table.project, kept in a ProjectOp, become the operator
  // of tuple.project.
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = d_nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  // ((_ tuple.project J) t) for t, a row of A.
  Node t = rowVariable(elementType);
  Node projection = d_nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, projection), A);
  return BagsRewriteResponse(ret, Rewrite::PROJECT_TO_MAP);
}

// Returns the columns that a projection lambda selects, in order, and an
// empty vector when f is not a projection. A projection is a lambda of one
// row x whose body is one of
//   (tuple ((_ tuple.select j0) x) .. ((_ tuple.select jm) x))
//   ((_ tuple.project j0 .. jm) x)
// and the result is then j0, .., jm. Both
//   (lambda ((t (Tuple Int Int Int)))
//     (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
// and
//   (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 2 0) t))
// give {2, 0}. A column may repeat: the body
//   (tuple ((_ tuple.select 1) t) ((_ tuple.select 1) t))
// gives {1, 1}. A projection onto no column also gives the empty vector.
std::vector<uint32_t> BagsRewriter::projectionIndices(const Node& f) const
{
  std::vector<uint32_t> out;
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return out;
  }
  Node x = f[0][0];
  Node body = f[1];
  if (body.getKind() == Kind::TUPLE_PROJECT && body[0] == x)
  {
    // ((_ tuple.project j0 .. jm) x): the indices of the operator.
    return body.getOperator().getConst<ProjectOp>().getIndices();
  }
  // Otherwise the body must build a tuple from a row x that is a tuple
  // itself: the selectors of a row of another datatype, as (field1 x), are
  // not columns.
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple()
      || !x.getType().isTuple())
  {
    return out;
  }
  for (const Node& c : body)
  {
    // Each component must be ((_ tuple.select j) x), a copy of column j of
    // x; any other component, as a constant or (+ ((_ tuple.select 0) x) 1),
    // means f is not a projection.
    if (c.getKind() != Kind::APPLY_SELECTOR || c[0] != x)
    {
      return std::vector<uint32_t>();
    }
    out.push_back(datatypes::utils::indexOf(c.getOperator()));
  }
  return out;
}

// AGGREGATE_MAP: an aggregate of a map becomes an aggregate of the map's
// argument. n = ((_ table.aggr K) f i (bag.map g X)) groups the rows of the
// map by their columns K and folds each group with the step f from the
// initial value i; a step is the function (lambda ((t R) (acc A)) e) that a
// fold applies to each row t and the accumulator acc, the value so far. The
// rule instead groups X by the columns JK of X that g copies to the group
// columns, and folds with f[t := (g x)], which reads each row x of X through
// g. For X : (Bag (Tuple Int Int Int)),
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t)
//              (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
//     (tuple 0 0)
//     (bag.map (lambda ((t (Tuple Int Int Int)))
//                (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
//              X))
//   ---> ((_ table.aggr 2)
//          (lambda ((x (Tuple Int Int Int)) (acc (Tuple Int Int)))
//            (tuple ((_ tuple.select 2) x)
//                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) x))))
//          (tuple 0 0)
//          X)                                              (AGGREGATE_MAP)
// once the rewriter simplifies the selectors of (g x). Each group of the map
// is then the image under g of one group of X. The rule also needs a step
// whose result does not depend on the order of the rows
// (see orderIndependentStep).
BagsRewriteResponse BagsRewriter::rewriteAggregateOfMap(const TNode& n) const
{
  // Unlike FILTER_MAP, this rule does not test the higher-order flag: its new
  // lambda replaces the lambda f that the term already has.
  // f, the step, must be a lambda of a row and an accumulator (it is not
  // read through asLambda), and g, the map's function, a lambda whose body
  // builds a tuple (tuple c0 .. cm), so that column k of a row of the map is
  // the term ck.
  Node f = n[0];
  Node i = n[1];
  Node g = asLambda(n[2][0]);
  Node X = n[2][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
      || g[1].getKind() != Kind::APPLY_CONSTRUCTOR || !g[1].getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // gv, the variable of g, is a row of X. Each group column k of the map's
  // rows is one of three kinds, by the term ck that g puts there:
  // - a copy ((_ tuple.select j) gv) of column j of X, whose j goes to JK;
  // - a term that reads gv otherwise, as (+ ((_ tuple.select 0) gv) 42),
  //   collected in computed and checked below;
  // - a term that does not read gv, as the constant 7: every row of the map
  //   has the same value there, so it splits no group and is dropped.
  Node gv = g[0][0];
  std::vector<uint32_t> K = n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<uint32_t> JK;
  std::vector<Node> computed;
  for (uint32_t k : K)
  {
    if (k >= g[1].getNumChildren())
    {
      // K names a column that g's tuple does not have.
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    Node c = g[1][k];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == gv)
    {
      JK.push_back(datatypes::utils::indexOf(c.getOperator()));
    }
    else if (occursFree(c, gv))
    {
      computed.push_back(c);
    }
  }
  for (const Node& c : computed)
  {
    // A computed group column must read only columns of gv that are also
    // copied to group columns, i.e. columns in JK, through
    // ((_ tuple.select j) gv), with no closure inside it binding gv again.
    // Then two rows of X that agree on JK agree on it too, so it splits no
    // group that the copied columns do not: (+ ((_ tuple.select 0) gv) 42)
    // beside ((_ tuple.select 0) gv), as deptno + 42 beside deptno in SQL.
    std::set<uint32_t> positions;
    if (!readPositions(c, gv, positions) || bindsVariable(c, gv))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    for (uint32_t pos : positions)
    {
      if (std::find(JK.begin(), JK.end(), pos) == JK.end())
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
  }
  // JK, sorted and without duplicates, holds the group columns of the new
  // aggregate. Two rows of X agree on JK exactly when their images under g
  // agree on K, so grouping X by JK and the map by K give matching groups.
  std::sort(JK.begin(), JK.end());
  JK.erase(std::unique(JK.begin(), JK.end()), JK.end());
  TypeNode rowType = X.getType().getBagElementType();
  if (!rowType.isTuple())
  {
    // The rows of X must be tuples, else the selectors of gv above are not
    // columns.
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // A group of the map and the group of X it comes from are two different
  // bags, and cvc5 may fold each in an order of its own. So the rule applies
  // only to a step whose result is the same in every order. The rows of a
  // group of the map all agree on the columns K, and nonNullColumns gives
  // the columns of the map's rows that are never null.
  std::set<uint32_t> same(K.begin(), K.end());
  if (!orderIndependentStep(f, same, nonNullColumns(n[2])))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // The new step is (lambda ((x R) (y A)) f's body[t := (g x)]): x, the row
  // variable of X's row sort, y, f's own accumulator, and gx = (g x)
  // beta-reduced.
  Node x = rowVariable(rowType);
  Node y = f[0][1];
  Node gx = applyFunction(n[2][0], x);
  // Give up when computing (g x) would capture a variable (gx is null), when
  // a closure in f's body binds x (the copies of gx under it would refer to
  // that closure's variable), or when x is f's accumulator y itself, which
  // the new lambda would bind twice.
  if (gx.isNull() || bindsVariable(f[1], x) || x == y)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node body = f[1].substitute(TNode(f[0][0]), TNode(gx));
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, y), body);
  // ((_ table.aggr JK) new step i X)
  Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(JK));
  std::vector<Node> children{op, lambda, i, X};
  Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_MAP);
}

// Whether folding a bag with the step f gives the same value whatever the
// order of its rows. A step is the function (lambda ((x R) (acc A)) e) that a
// fold applies to each row x and the accumulator acc, the value so far. cvc5
// folds each bag in an order of its own (see
// BagReduction::reduceFoldOperator), so a rule that replaces the bag being
// folded by another with the same rows, as AGGREGATE_MAP does, keeps the
// value only for such a step. same holds the columns of x that all rows
// folded together share (the group columns of an aggregate), and nonNull the
// columns of x that are never null. With same {0}, it is true for the step
//   (lambda ((x (Tuple Int Int)) (acc (Tuple Int Int)))
//     (tuple ((_ tuple.select 0) x)
//            (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) x))))
// (the group column and a sum), and false for
//   (lambda ((x (Tuple Int Int)) (acc Int)) ((_ tuple.select 1) x))
// whose value is column 1 of whichever row comes last. The accepted shapes,
// sums, counts, minimums, maximums, SQL's null-skipping SUM, MIN and MAX,
// and copies of shared columns, are listed in the lambda column below.
bool BagsRewriter::orderIndependentStep(const Node& f,
                                        const std::set<uint32_t>& same,
                                        const std::set<uint32_t>& nonNull) const
{
  // When the step builds a tuple of the accumulator's sort, each column of
  // the tuple is checked on its own, with its own component of acc as its
  // accumulator; a column may read no other component (see column below).
  // The columns then fold independently of each other, and when each one's
  // value is the same in any order, so is the tuple's.
  Node l = asLambda(f);
  if (l.getKind() != Kind::LAMBDA || l[0].getNumChildren() != 2)
  {
    return false;
  }
  // x, the row; acc, the accumulator.
  Node x = l[0][0];
  Node acc = l[0][1];
  // free(e): whether e reads no accumulator, i.e. acc is not free in e.
  auto free = [&](const Node& e) { return !occursFree(e, acc); };
  // valueOf(t), for t of a nullable sort (Nullable S): the value v when t is
  // (nullable.some v), and otherwise the term (nullable.val t), built with
  // the selector of the constructor that has one argument.
  auto valueOf = [&](const Node& t) {
    if (t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getNumChildren() == 1)
    {
      return t[0];
    }
    const DType& dt = t.getType().getDType();
    size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
    return d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), t);
  };
  // compares(c, a, b): whether c compares a and b, which are both numbers or
  // both strings: c is one of (< a b), (<= a b), (> a b), (>= a b), or
  // (str.< a b), (str.<= a b), with a and b either way round. c and each
  // candidate are compared after rewriting, so c may be written in any form
  // that the rewriter brings to the same normal form. Without a rewriter
  // (d_rewriter null) no c compares.
  auto compares = [&](const Node& c, const Node& a, const Node& b) {
    bool numbers = a.getType().isRealOrInt() && b.getType().isRealOrInt();
    bool strings = a.getType().isString() && b.getType().isString();
    if (d_rewriter == nullptr || !(numbers || strings))
    {
      return false;
    }
    Node rc = d_rewriter->rewrite(c);
    std::vector<Kind> kinds =
        numbers ? std::vector<Kind>{Kind::LT, Kind::LEQ, Kind::GT, Kind::GEQ}
                : std::vector<Kind>{Kind::STRING_LT, Kind::STRING_LEQ};
    for (Kind k : kinds)
    {
      // Each kind with (a, b) and with (b, a).
      for (size_t s = 0; s < 2; s++)
      {
        Node cmp = s == 0 ? d_nm->mkNode(k, a, b) : d_nm->mkNode(k, b, a);
        if (rc == d_rewriter->rewrite(cmp))
        {
          return true;
        }
      }
    }
    return false;
  };
  // combines(c, a, b), for nullable a and b that are both not null where c
  // is used: whether c is their sum, minimum or maximum. The sum is
  // (nullable.some s) with s equal to (+ (nullable.val a) (nullable.val b))
  // up to rewriting; the minimum or the maximum is (ite cmp a b) or
  // (ite cmp b a) with cmp comparing their values, as
  // (ite (< (nullable.val a) (nullable.val b)) a b). Each is commutative and
  // associative, so it combines the rows in any order to one value.
  auto combines = [&](const Node& c, const Node& a, const Node& b) {
    if (c.getKind() == Kind::APPLY_CONSTRUCTOR && c.getNumChildren() == 1)
    {
      // (nullable.some s): s must have the sort of the sum, and the rewriter
      // must reduce (= s sum) to true.
      Node sum = d_nm->mkNode(Kind::ADD, {valueOf(a), valueOf(b)});
      TypeNode t = c[0].getType();
      if (d_rewriter == nullptr || t != sum.getType())
      {
        return false;
      }
      Node r = d_rewriter->rewrite(c[0].eqNode(sum));
      return r.isConst() && r.getConst<bool>();
    }
    // An ite that returns a or b by a comparison of their values (any
    // comparison of the two picks the smaller or the larger one).
    if (c.getKind() != Kind::ITE
        || !((c[1] == a && c[2] == b) || (c[1] == b && c[2] == a)))
    {
      return false;
    }
    Node va = valueOf(a);
    Node vb = valueOf(b);
    return compares(c[0], va, vb);
  };
  // nullTested(c): the term t that c tests for null, for
  // c = (= (as nullable.null (Nullable Int)) t) or the same equality the
  // other way round; the null node for any other c.
  auto nullTested = [](const Node& c) {
    if (c.getKind() == Kind::EQUAL)
    {
      for (size_t s = 0; s < 2; s++)
      {
        if (isNullConstant(c[s]))
        {
          return c[1 - s];
        }
      }
    }
    return Node::null();
  };
  // sumOf(e, own): whether e is a sum (+ own e1 .. em) of own, exactly once,
  // and terms ei that read no accumulator (they may read the row x). Each
  // row adds its own amount, so the total is the same in any order.
  auto sumOf = [&](const Node& e, const Node& own) {
    if (e.getKind() != Kind::ADD)
    {
      return false;
    }
    size_t owns = 0;
    for (const Node& c : e)
    {
      if (c == own)
      {
        owns++;
      }
      else if (!free(c))
      {
        return false;
      }
    }
    return owns == 1;
  };
  // column(e, own): whether e, the term that computes the new value of the
  // accumulator own (a component ((_ tuple.select q) acc), or acc itself),
  // gives the same final value in every order of the rows. Below, v and a
  // stand for terms that read no accumulator; they may read the row x.
  std::function<bool(const Node&, const Node&)> column;
  column = [&](const Node& e, const Node& own) {
    if (free(e))
    {
      // A term that reads no accumulator: the final value is e of the last
      // row folded. That is one value in any order when e reads no column of
      // x, as a constant, or reads only columns in same, which all rows
      // folded together share, as the copy ((_ tuple.select 0) x) of a group
      // column 0. A term that reads x other than through the selectors
      // ((_ tuple.select k) x) is rejected.
      std::set<uint32_t> read;
      return !occursFree(e, x)
             || (readPositions(e, x, read)
                 && std::includes(
                     same.begin(), same.end(), read.begin(), read.end()));
    }
    if (e == own)
    {
      // own unchanged: the column keeps its initial value.
      return true;
    }
    {
      // Every other shape must read the accumulator through own only: with
      // own replaced by a fresh variable mark, acc must no longer occur free
      // in e. A column that reads another component of acc is rejected.
      Node mark = NodeManager::mkBoundVar("own", own.getType());
      if (occursFree(e.substitute(TNode(own), TNode(mark)), acc))
      {
        return false;
      }
    }
    // A sum: (+ own v ..), as the counter (+ own 1); or, for a nullable own,
    // (nullable.some (+ (nullable.val own) v ..)).
    TypeNode ownType = own.getType();
    bool nullable = ownType.isNullable();
    if (sumOf(e, own)
        || (nullable && e.getKind() == Kind::APPLY_CONSTRUCTOR
            && e.getNumChildren() == 1 && sumOf(e[0], valueOf(own))))
    {
      return true;
    }
    // Every remaining shape is an ite.
    if (e.getKind() != Kind::ITE)
    {
      return false;
    }
    if (free(e[0]))
    {
      // The condition reads no accumulator. SQL's SUM, MIN or MAX of a
      // nullable argument a: a null a keeps own, a non-null a replaces a
      // null own, and otherwise combines with own (see combines):
      //   (ite (= (as nullable.null (Nullable Int)) a)
      //        own
      //        (ite (= (as nullable.null (Nullable Int)) own) a C))
      // with C the sum, minimum or maximum of a and own. The result does not
      // depend on the order: it is the sum, minimum or maximum of the values
      // that are not null among own's initial value and the a of the rows,
      // and null when there is none.
      Node a = nullTested(e[0]);
      if (nullable && !a.isNull() && e[1] == own && free(a)
          && a.getType() == ownType && e[2].getKind() == Kind::ITE
          && nullTested(e[2][0]) == own && e[2][1] == a
          && combines(e[2][2], a, own))
      {
        return true;
      }
      // An accepted shape u applied only to the rows on which the condition
      // c fails, (ite c own u), or holds, (ite c u own). Since c reads no
      // accumulator, these rows form a sub-bag fixed by the rows alone, so u
      // must be accepted itself. SQL's COUNT of a nullable column 1, which
      // counts the rows where it is not null, is
      //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
      //        own
      //        (+ own 1)).
      if (e[1] == own)
      {
        return column(e[2], own);
      }
      if (e[2] == own)
      {
        return column(e[1], own);
      }
      return false;
    }
    // The condition reads the accumulator. A minimum or a maximum: the ite
    // returns v or own by a comparison of v and own (see compares), as
    // (ite (> v own) v own), the maximum of own's initial value and the v of
    // the rows, or (ite (< own v) own v), their minimum.
    for (size_t s = 1; s < 3; s++)
    {
      if (e[3 - s] == own && free(e[s]) && compares(e[0], e[s], own))
      {
        return true;
      }
    }
    // SQL's SUM, MIN or MAX as above, of an argument a that is never null
    // (nonNullTerm, given the columns nonNull of x that are never null): the
    // test of a for null has been decided false and removed, which leaves
    //   (ite (= (as nullable.null (Nullable Int)) own) a C)
    // with C the sum, minimum or maximum of a and own. Without knowing that a
    // is never null, this shape could depend on the order, so the test is
    // needed.
    return nullable && nullTested(e[0]) == own && free(e[1])
           && e[1].getType() == ownType
           && nonNullTerm(e[1], x, nonNull, Node::null(), {})
           && combines(e[2], e[1], own);
  };
  Node body = l[1];
  TypeNode accType = acc.getType();
  if (body.getKind() == Kind::APPLY_CONSTRUCTOR && accType.isTuple()
      && body.getType() == accType)
  {
    // The step builds a tuple (tuple e0 .. em) of the accumulator's sort:
    // check each ei with ((_ tuple.select i) acc) as its own accumulator.
    for (size_t q = 0, w = body.getNumChildren(); q < w; q++)
    {
      if (!column(body[q], datatypes::TupleUtils::nthElementOfTuple(acc, q)))
      {
        return false;
      }
    }
    return true;
  }
  // Any other body is checked as one column, with acc as its accumulator.
  return column(body, acc);
}

// Whether the formula n rewrites to false: true exactly when the full
// rewriter d_rewriter turns n into the constant false. For instance
//   (>= ((_ tuple.select 2) (tuple 0 0 0)) 1)
// rewrites to (>= 0 1) and then to false, so the answer is true; for
//   (>= ((_ tuple.select 2) r) 1)
// with r a variable it is false, as a formula that the rewriter does not
// decide is not known to be false. d_rewriter must not be null: the callers
// check it (see rejectsInitialRow).
bool BagsRewriter::rewritesToFalse(const Node& n) const
{
  Node r = d_rewriter->rewrite(n);
  return r.isConst() && !r.getConst<bool>();
}

// Whether the predicate P is false on the row of initial values i of an
// aggregate ((_ table.aggr K) f i X), that is, whether (P i) rewrites to
// false. That row is the one row of the aggregate of an empty table: for an
// empty X, table.group gives one empty group, which folds to i, so the
// aggregate is (bag i 1) although no row of X made it. A filter by such a P
// drops that row anyway, which lets AGGREGATE_KEYED replace the aggregate
// under it by rows that lack it (see keyedAggregateRows). The answer is true
// for a test that a count of rows, which starts at 0, is positive:
//   P = (lambda ((r (Tuple (Nullable Int) (Nullable Int) Int)))
//         (>= ((_ tuple.select 2) r) 1))
//   i = (tuple (as nullable.null (Nullable Int)) (nullable.some 0) 0)
// as (P i) is (>= ((_ tuple.select 2) i) 1), which rewrites to (>= 0 1),
// that is, to false.
bool BagsRewriter::rejectsInitialRow(const Node& P, const Node& i) const
{
  // Without the rewriter (P i) cannot be decided: answer false, which makes
  // the callers leave their term as it is.
  if (d_rewriter == nullptr)
  {
    return false;
  }
  // (P i) beta-reduced, P's variable replaced by i (see applyFunction). It is
  // null when the replacement would capture a variable, and the answer is
  // then false too. For a P that is not a lambda, it is the application
  // (P i) as an APPLY_UF.
  Node applied = applyFunction(P, i);
  return !applied.isNull() && rewritesToFalse(applied);
}

// For an aggregate A = ((_ table.aggr K) f i X) whose group columns K contain
// a key of X, the rows of the groups that some row of X reached; null for any
// other A. A key of X is a set of columns on which no two rows of X agree, a
// second copy of a row counting as another row (see rowKeys). The rows of one
// group agree on K, hence on that key, so every group is one row t of X, once,
// folded once from i to (f t i): the result is the map of X by
// (lambda ((t T)) (f t i)), with (f t i) beta-reduced, T the sort of X's rows.
// It is A except for an empty X: then table.group gives one empty group,
// folded to the row of initial values, so A is (bag i 1), which the map does
// not have. The callers use it where that row is dropped (see
// rejectsInitialRow). For X : (Bag (Tuple Int Int)) with the key {0},
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
//     (tuple 0 0)
//     X)
// gives
//   (bag.map (lambda ((t (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t)
//                     (+ ((_ tuple.select 1) (tuple 0 0)) 1)))
//            X)
// which the rewriter then simplifies to a map by
// (tuple ((_ tuple.select 0) t) 1), each group counting one row.
Node BagsRewriter::keyedAggregateRows(const Node& A) const
{
  // K: the group columns, the indices of the operator (_ table.aggr K). f: the
  // step, read as a lambda when the rewriter keeps it as a function array
  // constant (see asLambda).
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  Node f = asLambda(A[0]);
  // The rule needs some group column (an aggregate by no column has one group,
  // all of X, see AGGREGATE_NO_KEYS) and a step that is a lambda of a row and
  // an accumulator, so that (f t i) can be beta-reduced.
  if (K.empty() || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2)
  {
    return Node::null();
  }
  // keyed: whether some key of X, read off X's structure, lies inside K.
  std::set<uint32_t> grouped(K.begin(), K.end());
  bool keyed = false;
  for (const std::set<uint32_t>& key : rowKeys(A[2]))
  {
    bool inside = true;
    for (uint32_t c : key)
    {
      inside = inside && grouped.count(c) > 0;
    }
    keyed = keyed || inside;
  }
  if (!keyed)
  {
    return Node::null();
  }
  // (f t i): f's body with its accumulator variable f[0][1] replaced by i.
  // f's row variable t = f[0][0] stays and becomes the variable of the map's
  // lambda. Two rows with equal results give that result twice, in the map as
  // in A, since table.aggr maps the groups to their folds with bag.map.
  Node body = f[1].substitute(TNode(f[0][1]), TNode(A[1]));
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(f[0][0], body), A[2]);
}

// The bound variable that the rules use as the accumulator, the second
// variable, of the step of an aggregate or a fold that they build: one
// variable per sort S of the accumulator, so that two steps built the same way
// are one node. It is named accrow_N, N the id of the node
// (as bag.empty (Bag S)) that it is cached on. Like rowVariable, it comes from
// mkRewriterVar, here with the role "accumulator", which keeps it apart from
// the row variable of the same sort: for S = (Tuple Int Int) the accumulator
// is accrow_N and the row variable is row_N, with the same N, and they are
// two variables, so a lambda can bind both.
Node BagsRewriter::accumulatorVariable(TypeNode type) const
{
  // the key (as bag.empty (Bag S)) is a node that depends only on S
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(type)));
  return mkRewriterVar(
      d_nm, "accumulator", key, "accrow_" + std::to_string(key.getId()), type);
}

// The alpha key of the lambda f: a node that is the same for two lambdas that
// differ only in the names of their variables. It is f with every variable
// that f binds, at any depth, replaced by a placeholder for its binding depth
// (f's own variables are depths 0, 1, ..., and those of a lambda inside f
// come next), every variable free in f by one placeholder per sort, the
// arguments of commutative operators sorted and arithmetic atoms oriented
// (see alphaKeyScope). It does not change when a lambda inside f or around f
// renames its variables. The key is used only for its identity, as a cache
// key and by its node id, never as a term of the problem. The keys of
//   (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
//   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
// are one node, (lambda ((b0 (Tuple Int Int))) (> ((_ tuple.select 0) b0) 3))
// with the atom in the arithmetic rewriter's form, writing b0 for the
// placeholder of depth 0. A variable r free in f, such as the variable of an
// enclosing lambda, becomes the placeholder of its sort, so the key of
//   (lambda ((t (Tuple Int Int)))
//     (= ((_ tuple.select 0) t) ((_ tuple.select 0) r)))
// does not depend on the name of r either. Lambdas that read different free
// variables of one sort thus share a key, which only means that they get the
// same canonical names (see canonicalLambda). Keys are cached in d_alphaKeys.
Node BagsRewriter::alphaKey(const Node& f) const
{
  std::unordered_map<Node, Node>::iterator it = d_alphaKeys.find(f);
  if (it != d_alphaKeys.end())
  {
    return it->second;
  }
  // f is the outermost binder: no variable is bound around it, at depth 0
  std::unordered_map<TNode, Node> bound;
  Node key = alphaKeyScope(f, bound, 0);
  d_alphaKeys[f] = key;
  return key;
}

// The alpha key of root (see alphaKey), where root is the lambda whose key is
// computed or a part of it: bound maps the variables of the binders around
// root, inside that lambda, to their placeholders, and depth is the number of
// variables those binders bind, which is the depth that the next variable
// bound gets (both are empty and 0 for the lambda itself). A placeholder is a
// bound variable made by mkRewriterVar, one per role, number and sort, so the
// same depth and sort give the same node. For
//   (lambda ((s (Tuple Int Int)))
//     (bag.map (lambda ((u (Tuple Int Int)))
//                (tuple ((_ tuple.select 0) s) ((_ tuple.select 1) u)))
//              Y))
// the key is the same lambda with b0 for s and b1 for u, writing bk for the
// placeholder of depth k. The key of the inner lambda alone has b0 for u and,
// as s is free in it, the placeholder of the sort (Tuple Int Int) for s.
// Leaves that are not variables, such as Y, stay: lambdas that read different
// tables have different keys. The arguments of commutative operators are
// sorted, arithmetic atoms and ites over a negation are normalized, and the
// operator of a parameterized node is converted like an argument; the
// comments below say how each keeps the key the same when variables are
// renamed.
Node BagsRewriter::alphaKeyScope(TNode root,
                                 std::unordered_map<TNode, Node>& bound,
                                 size_t depth) const
{
  // The terms of one scope, each converted once, as the bodies of lambdas
  // share subterms. The terms under a binder inside root are converted by a
  // recursive call with its own cache, since more variables are bound there.
  std::unordered_map<TNode, Node> cache;
  // A traversal in post-order: a node is converted once its operator and its
  // children are.
  std::vector<TNode> todo{root};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    // A variable. When a binder around it binds it, it becomes that binder's
    // placeholder for it. Otherwise it is free in the lambda whose key is
    // computed (for instance the variable of an enclosing lambda) and becomes
    // the one placeholder of its sort, so that the key does not depend on its
    // name either.
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      std::unordered_map<TNode, Node>::iterator b = bound.find(n);
      if (b != bound.end())
      {
        cache[n] = b->second;
      }
      else
      {
        // the free placeholder of this sort: role "alpha-free", number 0
        Node zero = d_nm->mkConstInt(Rational(0));
        cache[n] = mkRewriterVar(d_nm, "alpha-free", zero, n.getType());
      }
      todo.pop_back();
      continue;
    }
    // Any other leaf, such as a constant or a declared constant like a table,
    // is its own key.
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    if (n.isClosure())
    {
      // A binder, such as a lambda. A lambda of the variables s and acc at
      // depth d becomes the lambda of the placeholders b_d and b_d+1, and its
      // body is converted in the scope of those placeholders, by a recursive
      // call at depth d + 2. The binder is converted at once, not after its
      // children as the other nodes are.
      todo.pop_back();
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> vars;
      std::vector<std::pair<TNode, Node>> saved;
      for (size_t i = 0; i < nvars; i++)
      {
        TNode v = n[0][i];
        // the bound placeholder of depth depth + i: role "alpha-bound"
        Node index = d_nm->mkConstInt(Rational(depth + i));
        Node p = mkRewriterVar(d_nm, "alpha-bound", index, v.getType());
        // A binder around this one may bind v too, which this one shadows:
        // save the placeholder it gave v, to restore it after the body.
        std::unordered_map<TNode, Node>::iterator b = bound.find(v);
        saved.push_back({v, b != bound.end() ? b->second : Node::null()});
        bound[v] = p;
        vars.push_back(p);
      }
      // the binder's operator, if it has one, is kept as is
      std::vector<Node> children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      children.push_back(d_nm->mkNode(Kind::BOUND_VAR_LIST, vars));
      // the children after the variable list: the body, and for a quantifier
      // its patterns, if any
      for (size_t i = 1, nc = n.getNumChildren(); i < nc; i++)
      {
        children.push_back(alphaKeyScope(n[i], bound, depth + nvars));
      }
      // restore bound to what it was around this binder
      for (const std::pair<TNode, Node>& s : saved)
      {
        if (s.second.isNull())
        {
          bound.erase(s.first);
        }
        else
        {
          bound[s.first] = s.second;
        }
      }
      cache[n] = d_nm->mkNode(n.getKind(), children);
      continue;
    }
    // Any other node. The operator of a parameterized node (as of an
    // APPLY_UF, a selector or a constructor application) is converted like
    // its arguments, since it can be a bound variable: in
    // (lambda ((f (-> Int Int))) (f 0)), f is the operator of (f 0). A
    // selector or a constructor is a leaf and stays.
    bool parameterized = n.getMetaKind() == kind::metakind::PARAMETERIZED;
    Node op = parameterized ? n.getOperator() : Node::null();
    // convert the operator and the children first, if not yet done; n stays
    // on todo and is converted when the traversal comes back to it
    bool ready = true;
    if (parameterized && !cache.count(op))
    {
      todo.push_back(op);
      ready = false;
    }
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // n over its converted operator and children. changed records whether
    // any of them differs from the original: when none does, n is its own
    // key and no node is built. The operator must count: in (f 0) above only
    // the operator changes, and keeping n would leave the name of f in the
    // key. A key that holds the name of a variable that a lambda binds
    // changes each time canonicalLambda renames that variable, so the renamed
    // lambda would get a new key, hence new names, and so on: the rewriter
    // would never reach a fixed point.
    std::vector<Node> children;
    bool changed = false;
    if (parameterized)
    {
      children.push_back(cache[op]);
      changed = cache[op] != op;
    }
    // first: the index of the first argument, after the operator if any
    size_t first = children.size();
    for (const Node& c : n)
    {
      Node cc = cache[c];
      changed = changed || cc != c;
      children.push_back(cc);
    }
    switch (n.getKind())
    {
      // Commutative operators. The rewriter sorts their arguments by node id,
      // and renaming a variable gives the arguments that read it other ids,
      // so after a renaming the rewriter may put them in another order. The
      // key sorts the converted arguments, which do not depend on the names,
      // so that both orders have one key. changed is set so that the sorted
      // order is used even when no argument changed.
      case Kind::EQUAL:
      case Kind::DISTINCT:
      case Kind::AND:
      case Kind::OR:
      case Kind::XOR:
      case Kind::ADD:
      case Kind::MULT:
      case Kind::NONLINEAR_MULT:
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      case Kind::BAG_INTER_MIN:
        std::sort(children.begin() + first, children.end());
        changed = true;
        break;
      default: break;
    }
    Node built = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
    Kind k = n.getKind();
    auto atom = [](Kind a) {
      return a == Kind::GEQ || a == Kind::GT || a == Kind::LEQ || a == Kind::LT;
    };
    if (d_rewriter != nullptr
        && (atom(k)
            || (k == Kind::NOT && built.getKind() == Kind::NOT
                && (atom(built[0].getKind())
                    || built[0].getKind() == Kind::NOT))))
    {
      // An arithmetic atom (>=, >, <= or <), or a negation whose converted
      // argument is an atom or a negation. The arithmetic rewriter writes an
      // atom in a normal form oriented by the order of the terms it reads,
      // which is by node id: for integers a and b, (>= (- a b) 0) and
      // (not (>= (- b a) 1)) say the same, and which of them it writes depends
      // on whether a or b comes first. Renaming a lambda's variables can thus
      // flip the form. Here the converted atom, over the placeholders, is
      // rewritten, so that the two forms have one key. A negation is
      // rewritten too, since the rewriting of the atom inside it may have
      // negated it again, giving (not (not c)). The rewriter rewrites the
      // whole atom, any term inside it included; the result still depends
      // only on the converted atom.
      built = d_rewriter->rewrite(built);
    }
    if (k == Kind::ITE && built.getKind() == Kind::ITE
        && built[0].getKind() == Kind::NOT)
    {
      // (ite (not c) a b) is (ite c b a), and the Boolean rewriter writes it
      // so. The converted condition may be a negation that the lambda's own
      // ite did not have, when the rewriting of an atom above negated it, so
      // the key flips the ite too: both forms have one key.
      built = d_nm->mkNode(Kind::ITE, built[0][0], built[2], built[1]);
    }
    cache[n] = built;
  }
  return cache[root];
}

// body with every subterm (ite (= a b) b a) replaced by a, and every
// (ite (= a b) a b) by b, at any depth, under binders too. Both are sound:
// the result is the else branch, and when a = b the then branch has the same
// value. The null-aware steps that sqleq's translator writes for SQL
// aggregates leave such ites once an accumulator is known, for instance the
// step of a minimum,
//   (ite (= (as nullable.null (Nullable Int)) acc) a (ite ...))
// with acc the accumulator column of a, the one that holds its minimum. For
// t : (Tuple Int Int),
//   (ite (= ((_ tuple.select 0) t) ((_ tuple.select 1) t))
//        ((_ tuple.select 1) t)
//        ((_ tuple.select 0) t))
// becomes ((_ tuple.select 0) t).
Node BagsRewriter::simplifyIteSame(const Node& body) const
{
  // A traversal in post-order: a node is simplified after its children, and
  // each distinct subterm once.
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{body};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    // a leaf stays
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    // simplify the children first; n stays on todo until they are done
    bool ready = true;
    for (const Node& c : n)
    {
      if (!cache.count(c))
      {
        todo.push_back(c);
        ready = false;
      }
    }
    if (!ready)
    {
      continue;
    }
    todo.pop_back();
    // m: n over its simplified children, or n itself when none changed. The
    // operator of a parameterized node is kept as it is, not simplified.
    std::vector<Node> children;
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      children.push_back(n.getOperator());
    }
    bool changed = false;
    for (const Node& c : n)
    {
      changed = changed || cache[c] != c;
      children.push_back(cache[c]);
    }
    Node m = changed ? d_nm->mkNode(n.getKind(), children) : Node(n);
    // m = (ite (= a b) x y): replaced by a when x is b and y is a, by b when
    // x is a and y is b. The result is a part of m's condition, which is
    // simplified already, and m's parent is checked with this result, so one
    // pass leaves no such ite, except in the operators kept as they are.
    if (m.getKind() == Kind::ITE && m[0].getKind() == Kind::EQUAL)
    {
      const Node& a = m[0][0];
      const Node& b = m[0][1];
      if (m[1] == b && m[2] == a)
      {
        m = a;
      }
      else if (m[1] == a && m[2] == b)
      {
        m = b;
      }
    }
    cache[n] = m;
  }
  return cache[body];
}

// CANONICAL_VARIABLE: the lambda f with its variables renamed to canonical
// ones, named after f's alpha key (see alphaKey: a node that is the same for
// lambdas that differ only in the names of their variables). With N the node
// id of the key, the variable of a lambda of one variable, as of a filter or
// a map, is renamed to t_N, and the two of a lambda of two, as of a fold or
// an aggregate, to t_N and acc_N. Lambdas that differ only in the names of
// their variables thus become one node, which the solver purifies into one
// function symbol (see rewrites.h). For X : (Bag (Tuple Int Int)),
//   (bag.filter (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3)) X)
//   ---> (bag.filter
//          (lambda ((t_N (Tuple Int Int))) (> ((_ tuple.select 0) t_N) 3))
//          X)
// and the same filter over a variable t instead of s gives the same term,
// for the same N. First, f's body is simplified (see simplifyIteSame), so that
// (ite (= a b) b a) in it is a. Two lambdas one inside the other have
// different keys, as the key of the outer one holds the converted inner one,
// so canonical names never shadow each other. The key does not change when a
// lambda inside or around f is renamed, so renaming terminates.
Node BagsRewriter::canonicalLambda(const Node& f) const
{
  Assert(f.getKind() == Kind::LAMBDA);
  {
    // Simplify the body first, then canonicalize the simplified lambda, so
    // that the key and the names come from the simplified body. The body of
    // that lambda has nothing left to simplify, so the recursion stops there.
    Node simpler = simplifyIteSame(f[1]);
    if (simpler != f[1])
    {
      return canonicalLambda(d_nm->mkNode(Kind::LAMBDA, f[0], simpler));
    }
  }
  size_t arity = f[0].getNumChildren();
  std::vector<Node> vars(f[0].begin(), f[0].end());
  Node key = alphaKey(f);
  // The canonical variable of position k: the bound variable that the
  // BoundVarManager gives for the id BAGS_FIRST_INDEX, the cache node
  // (SEXPR "canonical" (SEXPR key k)) and the sort of f's k-th variable (see
  // mkRewriterVar). The manager returns one variable per id, cache node and
  // sort, so two lambdas with one key get the same canonical variables. The
  // role "canonical" keeps them apart from the row, accumulator and
  // placeholder variables, which have other roles, and the bag reductions,
  // the other users of BAGS_FIRST_INDEX, cache on the bag terms they reduce,
  // never on an SEXPR. This gives one node per class of lambdas that differ
  // only in the names of their variables: such lambdas get the same
  // variables, and renaming makes their bodies one node, since the lambdas
  // inside them have been rewritten first and are canonical already.
  std::vector<Node> canonical;
  for (size_t k = 0; k < arity; k++)
  {
    Node cache = d_nm->mkNode(Kind::SEXPR, key, d_nm->mkConstInt(Rational(k)));
    // Named apart: the name holds N, so canonical variables of different keys
    // print with different names. A printed problem binds by name, and if a
    // lambda and a variable free in it had one name, the printed lambda would
    // capture that variable. Every position after the first is named acc_N;
    // the callers pass lambdas of at most two variables.
    std::string name = (k == 0 ? "t_" : "acc_") + std::to_string(key.getId());
    canonical.push_back(
        mkRewriterVar(d_nm, "canonical", cache, name, vars[k].getType()));
  }
  // f is canonical already: the fixed point. The rewriter rewrites the
  // renamed lambda again, which may reorder the arguments or orient the atoms
  // in its body by the ids of the new variables; the key is built to stay
  // the same under these changes (see alphaKeyScope), so the rewritten
  // lambda gets the same canonical variables and ends here.
  if (canonical == vars)
  {
    return f;
  }
  // A canonical variable that is not the variable it replaces occurs in the
  // body already, free in it or bound by a lambda inside it: renaming would
  // capture it or merge it with f's variable, so f is left as it is. This
  // keeps the renaming sound even if the keys above did not keep the names
  // apart.
  Node body = f[1];
  for (size_t k = 0; k < arity; k++)
  {
    if (canonical[k] != vars[k] && expr::hasSubterm(body, canonical[k]))
    {
      return f;
    }
  }
  // rename all the variables at once and bind the canonical ones
  Node newBody = body.substitute(
      vars.begin(), vars.end(), canonical.begin(), canonical.end());
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, canonical), newBody);
}

// AGGREGATE_SORT_OUTPUT: for n = ((_ table.aggr K) f i X), puts the columns
// of the aggregate's rows in one canonical order, under a bag.map that puts
// them back in their old order. Two aggregates that compute the same columns
// in different orders then become one aggregate under two different maps.
// Here f = (lambda ((t R) (acc T)) (tuple e_0 .. e_(m-1))), with t : R a row
// of X and acc : T the accumulator, and column q of the result is computed by
// e_q from the initial value i_q. The columns that copy a group column of t
// (a column of X that the aggregate groups its rows by, one of K) come first,
// ordered by that column; the other columns follow, ordered by what they
// compute when each e_q reads no column of acc but its own, and otherwise
// left in their order.
// For X : (Bag (Tuple Int Int)),
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 1) t))
//              ((_ tuple.select 0) t)))
//     (tuple 0 0) X)
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
//          ((_ table.aggr 0)
//            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t)
//                     (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
//            (tuple 0 0) X))                       (AGGREGATE_SORT_OUTPUT)
BagsRewriteResponse BagsRewriter::rewriteAggregateSortOutput(
    const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
  // f must be a lambda of the row and the accumulator whose body is a tuple
  // (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as many
  // components: the rule permutes the components of both
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple()
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  const std::vector<uint32_t>& K =
      n.getOperator().getConst<ProjectOp>().getIndices();
  std::set<uint32_t> keys(K.begin(), K.end());
  // x is the row t of X, y the old accumulator acc
  Node x = f[0][0];
  Node y = f[0][1];
  size_t m = f[1].getNumChildren();
  // Each column q gets a sort key (class, rank). Class 0 holds the copies of
  // group columns, ((_ tuple.select k) x) with k in K, ranked by k. Class 1
  // holds the other columns. These are ranked by what they compute (the alpha
  // key of their step and their initial value) when every e_q is
  // independent, that is, reads no column of y but its own column q: then
  // e_q with i_q is a computation of its own, which looks the same at any
  // position. Otherwise they are ranked by position, keeping their order.
  // readPositions fails when e_q reads y other than through a selector.
  bool independent = true;
  for (uint32_t q = 0; q < m && independent; q++)
  {
    std::set<uint32_t> pos;
    independent = readPositions(f[1][q], y, pos) && pos.size() <= 1
                  && (pos.empty() || pos.count(q));
  }
  std::vector<std::pair<std::pair<int, uint64_t>, uint32_t>> order;
  for (uint32_t q = 0; q < m; q++)
  {
    Node c = f[1][q];
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0] == x
        && keys.count(datatypes::utils::indexOf(c.getOperator())))
    {
      // e_q = ((_ tuple.select k) x), a copy of the group column k: every
      // row of a group has the same value there. Class 0, ranked by k
      order.push_back({{0, datatypes::utils::indexOf(c.getOperator())}, q});
    }
    else if (independent)
    {
      // ranked by what e_q computes: the alpha key (see alphaKey) of the
      // step (lambda ((x R) (v S)) e_q), with its own column
      // ((_ tuple.select q) y) read as a fresh variable v of its sort S,
      // together with i_q.
      // This key does not depend on q or on the names of the variables. The
      // rank is the id of the node (SEXPR key i_q): an arbitrary order, but
      // the same rank for the same column of any other aggregate, since that
      // column gives the same node
      Node own = datatypes::TupleUtils::nthElementOfTuple(y, q);
      Node v = NodeManager::mkBoundVar("v", own.getType());
      Node step = d_nm->mkNode(Kind::LAMBDA,
                               {d_nm->mkNode(Kind::BOUND_VAR_LIST, x, v),
                                c.substitute(TNode(own), TNode(v))});
      Node key = d_nm->mkNode(Kind::SEXPR, alphaKey(step), i[q]);
      order.push_back({{1, key.getId()}, q});
    }
    else
    {
      // some e_p reads a column of y other than its own: ranked by position
      order.push_back({{1, q}, q});
    }
  }
  // stable, so columns with equal sort keys, as two copies of one group
  // column, keep their order
  std::stable_sort(order.begin(), order.end());
  std::vector<uint32_t> sigma;  // new position -> old position
  bool identity = true;
  for (uint32_t q = 0; q < m; q++)
  {
    sigma.push_back(order[q].second);
    identity = identity && order[q].second == q;
  }
  if (identity)
  {
    // the columns are in order already; in particular the rule does not
    // apply again to its own result
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<uint32_t> inverse(m);  // old position -> new position
  for (uint32_t q = 0; q < m; q++)
  {
    inverse[sigma[q]] = q;
  }
  // newType, the sort of the sorted rows: the column sorts permuted by sigma
  TypeNode oldType = f[1].getType();
  std::vector<TypeNode> types;
  for (uint32_t q = 0; q < m; q++)
  {
    types.push_back(oldType.getTupleTypes()[sigma[q]]);
  }
  TypeNode newType = d_nm->mkTupleType(types);
  // acc, the new accumulator, is the rewriter's variable for accumulators of
  // newType. It must not be the row variable x, nor occur in the body unless
  // it is y itself, which the substitution below replaces
  Node acc = accumulatorVariable(newType);
  if (acc == x || (acc != y && expr::hasSubterm(f[1], acc)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // The old accumulator expressed through the new one: old column p is new
  // column inverse[p], so it is the tuple of the ((_ tuple.select inverse[p])
  // acc); in the example above, (tuple ((_ tuple.select 1) acc)
  // ((_ tuple.select 0) acc)). With it for y, the body reads the sorted
  // accumulator
  std::vector<Node> oldAcc;
  for (uint32_t p = 0; p < m; p++)
  {
    oldAcc.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, inverse[p]));
  }
  Node unsortedAcc = datatypes::TupleUtils::constructTupleFromElements(
      oldType, oldAcc, 0, m - 1);
  Node body = f[1].substitute(TNode(y), TNode(unsortedAcc));
  // Column q of the new step and of the new initial value is column sigma[q]
  // of the old ones. Over the rows of a group, the new accumulator is then
  // always the old one with its columns sorted, so the new fold computes the
  // sorted rows of the old one
  std::vector<Node> newElems, newInit;
  for (uint32_t q = 0; q < m; q++)
  {
    newElems.push_back(body[sigma[q]]);
    newInit.push_back(i[sigma[q]]);
  }
  Node newBody = datatypes::TupleUtils::constructTupleFromElements(
      newType, newElems, 0, m - 1);
  Node newI = datatypes::TupleUtils::constructTupleFromElements(
      newType, newInit, 0, m - 1);
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc), newBody);
  // the same operator, so the same group columns K of X: the order of the
  // output columns does not change the groups
  std::vector<Node> children{n.getOperator(), lambda, newI, X};
  Node sortedAggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  // The map that puts the columns back: column p of an old row is column
  // inverse[p] of the row r of the sorted aggregate. It is a bijection
  // between the two row sorts, so the bag.map keeps every multiplicity
  Node r = rowVariable(newType);
  std::vector<Node> back;
  for (uint32_t p = 0; p < m; p++)
  {
    back.push_back(datatypes::TupleUtils::nthElementOfTuple(r, inverse[p]));
  }
  Node unsort = mkLambda(r,
                         datatypes::TupleUtils::constructTupleFromElements(
                             oldType, back, 0, m - 1));
  Node ret = d_nm->mkNode(Kind::BAG_MAP, unsort, sortedAggr);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_SORT_OUTPUT);
}

// FOLD_TUPLE: for n = (bag.fold f i X) with a tuple accumulator, splits the
// fold into the tuple of one fold per component. This needs f =
// (lambda ((t E) (acc T)) (tuple e_0 .. e_(m-1))), t : E an element of X and
// acc : T the accumulator, with each e_k reading acc only through its own
// component ((_ tuple.select k) acc). Fold k then has the step e_k, with that
// component read as an accumulator a of its own, and starts from component k
// of i.
// The folds over X read its elements in one order, so each component of the
// old accumulator is, after every element, the accumulator of its own fold.
// For X : (Bag (Tuple Int)),
//   (bag.fold (lambda ((t (Tuple Int)) (acc (Tuple Int Int)))
//               (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t))
//                      (+ ((_ tuple.select 1) acc) 1)))
//             (tuple 0 0) X)
//   ---> (tuple (bag.fold (lambda ((t (Tuple Int)) (a Int))
//                           (+ a ((_ tuple.select 0) t)))
//                         0 X)
//               (bag.fold (lambda ((t (Tuple Int)) (a Int)) (+ a 1)) 0 X))
//                                                            (FOLD_TUPLE)
// that is, the sum and the count of the rows of X.
BagsRewriteResponse BagsRewriter::rewriteFoldOfTuple(const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
  // f must be a lambda of the element and the accumulator whose body builds a
  // tuple, (tuple e_0 .. e_(m-1)), so that its components can be split
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  Node body = f[1];
  size_t m = body.getNumChildren();
  if (m == 0)
  {
    // the empty tuple has no component to fold
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // components[k] is the fold of e_k
  std::vector<Node> components;
  for (size_t k = 0; k < m; k++)
  {
    // e_k must read acc only through selectors, ((_ tuple.select p) acc),
    // never whole, and no lambda inside e_k may bind acc again (a read of
    // that inner variable is no read of the accumulator)
    std::set<uint32_t> positions;
    if (!readPositions(body[k], acc, positions) || bindsVariable(body[k], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // and only its own component, p = k; it may also read none
    for (uint32_t pos : positions)
    {
      if (pos != k)
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
    // a, the accumulator of fold k, is the rewriter's variable for
    // accumulators of the sort of e_k. It must not be the element variable
    // x, nor occur in e_k already, or the substitution below would mix it up
    // with the occurrences there
    TypeNode type = body[k].getType();
    Node a = accumulatorVariable(type);
    if (a == x || expr::hasSubterm(body[k], a))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // the step of fold k: e_k with ((_ tuple.select k) acc) read as a; the
    // checks above leave no other occurrence of acc, and this one makes sure
    Node selected = datatypes::TupleUtils::nthElementOfTuple(acc, k);
    Node step = body[k].substitute(TNode(selected), TNode(a));
    if (expr::hasSubterm(step, acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // (bag.fold (lambda ((x E) (a S)) step) i_k X), S the sort of e_k and
    // i_k component k of i: i[k] when i is a tuple (tuple i_0 ..), else
    // ((_ tuple.select k) i)
    Node lambda = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, a), step);
    Node seed = datatypes::TupleUtils::nthElementOfTuple(i, k);
    components.push_back(d_nm->mkNode(Kind::BAG_FOLD, lambda, seed, X));
  }
  Node ret = datatypes::TupleUtils::constructTupleFromElements(
      n.getType(), components, 0, m - 1);
  return BagsRewriteResponse(ret, Rewrite::FOLD_TUPLE);
}

// SETOF_PROJECTION_SORT: for n = (bag.setof (bag.map f Y)), where f maps a
// row t of Y to a tuple of its columns ((_ tuple.select j) t) that are not
// in strictly increasing order of j (out of order, or a column twice),
// returns the set of the projection onto those columns sorted, each once,
// under a bag.map that puts them back in f's order. That map is injective,
// so it commutes with removing duplicates.
// Queries that select the same columns of Y in different orders then share
// one set term. For Y : (Bag (Tuple Int Int Int)),
//   (bag.setof
//     (bag.map (lambda ((t (Tuple Int Int Int)))
//                (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
//              Y))
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
//          (bag.setof
//            (bag.map (lambda ((t (Tuple Int Int Int)))
//                       (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
//                     Y)))                          (SETOF_PROJECTION_SORT)
BagsRewriteResponse BagsRewriter::rewriteSetofOfMap(const TNode& n) const
{
  // SETOF_PROJECTION_SORT: see the comment above this function and rewrites.h.
  // n = (bag.setof (bag.map f Y)), with f read as a lambda of one variable,
  // a row t of Y, even when it is kept as a function constant
  Node f = asLambda(n[0][0]);
  Node Y = n[0][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node var = f[0][0];
  Node body = f[1];
  // f's body must be written as a tuple, (tuple e_0 .. e_(k-1))
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  {
    // J: the columns f selects, in f's order, as [2, 0] in the example
    // above; empty when some e_k is not a column ((_ tuple.select j) t)
    std::vector<uint32_t> J = projectionIndices(f);
    if (!J.empty())
    {
      // sorted: the columns of J in increasing order, each once, as [0, 2].
      // It differs from J when J is out of order or has a column twice
      std::vector<uint32_t> sorted = J;
      std::sort(sorted.begin(), sorted.end());
      sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
      if (sorted != J)
      {
        // g, the projection onto the sorted columns, and inner =
        // (bag.setof (bag.map g Y)); in the example, g is
        //   (lambda ((t (Tuple Int Int Int)))
        //     (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
        TypeNode rowType = Y.getType().getBagElementType();
        std::vector<Node> cols;
        std::vector<TypeNode> types;
        for (uint32_t j : sorted)
        {
          cols.push_back(datatypes::TupleUtils::nthElementOfTuple(var, j));
          types.push_back(rowType.getTupleTypes()[j]);
        }
        TypeNode sortedType = d_nm->mkTupleType(types);
        Node g = mkLambda(var,
                          datatypes::TupleUtils::constructTupleFromElements(
                              sortedType, cols, 0, cols.size() - 1));
        Node inner =
            d_nm->mkNode(Kind::BAG_SETOF, d_nm->mkNode(Kind::BAG_MAP, g, Y));
        // unsort, the map back to f's order, for r a row of inner: its
        // component k is column j = J[k] of t, which is component at of r,
        // the position of j in sorted; in the example, (tuple
        // ((_ tuple.select 1) r) ((_ tuple.select 0) r)). f is g followed by
        // unsort. unsort reads every component of r, so it is injective, and
        // maps a set to a set: the set of (bag.map unsort (bag.map g Y)) is
        // (bag.map unsort (bag.setof (bag.map g Y)))
        Node r = rowVariable(sortedType);
        std::vector<Node> back;
        for (uint32_t j : J)
        {
          size_t at = std::lower_bound(sorted.begin(), sorted.end(), j)
                      - sorted.begin();
          back.push_back(datatypes::TupleUtils::nthElementOfTuple(r, at));
        }
        Node unsort =
            mkLambda(r,
                     datatypes::TupleUtils::constructTupleFromElements(
                         body.getType(), back, 0, back.size() - 1));
        Node ret = d_nm->mkNode(Kind::BAG_MAP, unsort, inner);
        return BagsRewriteResponse(ret, Rewrite::SETOF_PROJECTION_SORT);
      }
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

// Returns the formula that says the nullable Boolean X : (Nullable Bool) is
// true, (= X (nullable.some true)), when X is built of ites whose leaves are
// (nullable.some b) or (as nullable.null (Nullable Bool)); returns the null
// Node for any other X. In SQL's three-valued logic, which (Nullable Bool)
// encodes, null is not true, so a null leaf says false. For c, b : Bool,
//   X = (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
//   ---> returns (ite c b false)
// and nested ites give nested ites of the same shape. For X a variable of
// sort (Nullable Bool) it returns the null Node.
Node BagsRewriter::truthOf(const Node& X) const
{
  if (X.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // a leaf: (nullable.some b), the constructor of one argument, is true
    // when b is; (as nullable.null (Nullable Bool)), of none, never is
    return X.getNumChildren() == 1 ? X[0] : d_nm->mkConst(false);
  }
  if (X.getKind() == Kind::ITE)
  {
    // (ite c X1 X2) is true when X1 is, if c holds, and when X2 is, if not
    Node a = truthOf(X[1]);
    Node b = truthOf(X[2]);
    if (a.isNull() || b.isNull())
    {
      return Node::null();
    }
    return d_nm->mkNode(Kind::ITE, X[0], a, b);
  }
  // another term, as a variable or a column of a row: no formula
  return Node::null();
}

// FILTER_NULLABLE_TRUTH: body is the body of a filter's predicate. SQL's
// WHERE keeps a row when its three-valued condition X : (Nullable Bool) is
// true, which can be written as two conjuncts, (nullable.is_some X) and
// (nullable.val X). When X is an ite that truthOf reads, both conjuncts are
// replaced by the one formula truthOf(X) that they say together, at the
// place of the first of them; the other conjuncts are kept in their order.
// So a WHERE over a three-valued condition is one formula, whether it was
// written as the two conjuncts or as the formula. For
// t : (Tuple Int (Nullable Int)) and
//   X = (ite (nullable.is_some ((_ tuple.select 1) t))
//            (nullable.some (> (nullable.val ((_ tuple.select 1) t)) 3))
//            (as nullable.null (Nullable Bool))),
//   (and (nullable.is_some X) (nullable.val X) (> ((_ tuple.select 0) t) 0))
//   ---> (and (ite (nullable.is_some ((_ tuple.select 1) t))
//                  (> (nullable.val ((_ tuple.select 1) t)) 3)
//                  false)
//             (> ((_ tuple.select 0) t) 0))
// which the rewriter then simplifies further. Returns body itself when it has
// no such pair of conjuncts.
Node BagsRewriter::normalizeTruth(const Node& body) const
{
  // the top-level conjuncts of body, or body itself as the one conjunct
  std::vector<Node> conjuncts;
  if (body.getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), body.begin(), body.end());
  }
  else
  {
    conjuncts.push_back(body);
  }
  // vals: the terms X, ites of a nullable sort, for which body has the
  // conjunct (nullable.val X), nullable.val being the one selector of a
  // nullable sort; the conjunct is a formula, so X : (Nullable Bool)
  std::set<Node> vals;
  for (const Node& c : conjuncts)
  {
    if (c.getKind() == Kind::APPLY_SELECTOR && c[0].getType().isNullable()
        && c[0].getKind() == Kind::ITE)
    {
      vals.insert(c[0]);
    }
  }
  if (vals.empty())
  {
    return body;
  }
  // out: the new conjuncts; done: the X whose formula is in out already
  std::vector<Node> out;
  bool changed = false;
  std::set<Node> done;
  for (const Node& c : conjuncts)
  {
    // X, the term of vals that c is about: c = (nullable.val X), or c a
    // tester of X; isTester returns the index of the constructor it tests,
    // -1 for no tester, and sets a to the tested term
    Node X;
    Node a;
    if (c.getKind() == Kind::APPLY_SELECTOR && vals.count(c[0]))
    {
      X = c[0];
    }
    else if (datatypes::utils::isTester(c, a) >= 0 && vals.count(a))
    {
      X = a;
    }
    if (!X.isNull())
    {
      Node t = truthOf(X);
      if (!t.isNull())
      {
        // Both conjuncts become the one formula t, provided that body also
        // has the conjunct (nullable.is_some X), the tester of the
        // constructor of one argument. A lone (nullable.val X) is kept: its
        // value when X is null is unspecified, so it is not t. When the pair
        // is there, c is dropped, whichever constructor it tests, and t is
        // added once per X. A (nullable.is_null X) conjunct does not occur
        // in the rewritten bodies seen here: the datatypes rewriter writes it
        // as an equality with null, which is no tester
        bool hasTester = false;
        for (const Node& d : conjuncts)
        {
          Node b;
          int ci = datatypes::utils::isTester(d, b);
          hasTester = hasTester
                      || (ci >= 0 && b == X
                          && X.getType().getDType()[ci].getNumArgs() == 1);
        }
        if (hasTester)
        {
          if (done.insert(X).second)
          {
            out.push_back(t);
          }
          changed = true;
          continue;
        }
      }
    }
    // any other conjunct is kept as it is
    out.push_back(c);
  }
  if (!changed)
  {
    return body;
  }
  return out.size() == 1 ? out[0] : d_nm->mkNode(Kind::AND, out);
}

// AGGREGATE_DEAD_COLUMNS: for n = (bag.map h A) or n = (bag.map h
// (bag.filter P A)), with A = ((_ table.aggr K) f i X), removes from A the
// dead columns: the columns of A's rows that the rest of the term never
// reads. A column q is dead when neither h nor P reads it, and the step f
// computes it from the row of X and from column q of the accumulator only,
// a column of the accumulator that no other column of f reads. Then column q
// changes no column that is read. The aggregate groups the rows of X by its
// group columns K, columns of X and not of its output, so no group changes.
// table.aggr gives one row per group, and two groups whose rows differ only
// in dead columns give equal new rows, which h maps as it mapped the old
// ones, so the multiplicities agree too. For X : (Bag (Tuple Int Int)) and
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
//         (tuple ((_ tuple.select 0) t)
//                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
//                (+ ((_ tuple.select 2) acc) 1))),
//   (bag.map (lambda ((r (Tuple Int Int Int)))
//              (tuple ((_ tuple.select 0) r) ((_ tuple.select 2) r)))
//            ((_ table.aggr 0) f (tuple 0 0 0) X))
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 0) r) ((_ tuple.select 1) r)))
//          ((_ table.aggr 0)
//            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//              (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
//            (tuple 0 0) X))                       (AGGREGATE_DEAD_COLUMNS)
// Here the map reads the group column 0 and the count of rows, column 2, and
// the sum in column 1 is dead. With a filter (bag.filter P A) in between, P
// is rewritten as h is, to read the new rows.
BagsRewriteResponse BagsRewriter::rewriteAggregateDeadColumns(
    const TNode& n) const
{
  // Phase 1, the shape. n = (bag.map h Y); when Y is a filter
  // (bag.filter P A), P is its predicate and Y becomes A. h and P are read
  // as lambdas of one variable, a row r of A, even when they are kept as
  // function constants
  Node h = asLambda(n[0]);
  Node Y = n[1];
  Node P;
  if (Y.getKind() == Kind::BAG_FILTER)
  {
    P = asLambda(Y[0]);
    Y = Y[1];
  }
  if (Y.getKind() != Kind::TABLE_AGGREGATE || h.getKind() != Kind::LAMBDA
      || h[0].getNumChildren() != 1
      || (!P.isNull()
          && (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // Y = ((_ table.aggr K) f i X), with f = (lambda ((t R) (acc T))
  // (tuple e_0 .. e_(m-1))), t : R a row of X and acc : T the accumulator,
  // and i = (tuple i_0 .. i_(m-1)): column q of A's rows is computed by e_q
  // from i_q, so a column can be removed by removing e_q and i_q
  Node f = Y[0];
  Node i = Y[1];
  Node X = Y[2];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || f[1].getKind() != Kind::APPLY_CONSTRUCTOR || !f[1].getType().isTuple()
      || i.getKind() != Kind::APPLY_CONSTRUCTOR
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  size_t m = f[1].getNumChildren();
  // Phase 2, the columns of A's rows that are read. read collects the
  // columns k that h reads, as ((_ tuple.select k) r), and those that P
  // reads. h and P must read their row only through such selectors, never
  // whole, and no lambda inside them may bind their variable again (a read
  // of that inner variable is not a read of A's row)
  std::set<uint32_t> read;
  if (!readPositions(h[1], h[0][0], read) || bindsVariable(h[1], h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  if (!P.isNull()
      && (!readPositions(P[1], P[0][0], read) || bindsVariable(P[1], P[0][0])))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  // reads[q]: the columns of the accumulator acc that e_q reads, by the same
  // rules; in the example above, {1} for e_1 and {2} for e_2
  std::vector<std::set<uint32_t>> reads(m);
  for (size_t q = 0; q < m; q++)
  {
    if (!readPositions(f[1][q], acc, reads[q]) || bindsVariable(f[1][q], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // Phase 3, the dead columns. Column q is dead, keep[q] false, when it is
  // not in read, e_q reads no column of acc but q (self), and no other e_o
  // reads column q of acc (readByOthers). In the example, read is {0, 2}
  // and column 1 is dead
  std::vector<bool> keep(m, true);
  bool dropped = false;
  for (size_t q = 0; q < m; q++)
  {
    if (read.count(q))
    {
      continue;
    }
    bool self = true;
    for (uint32_t p : reads[q])
    {
      self = self && p == q;
    }
    bool readByOthers = false;
    for (size_t o = 0; o < m; o++)
    {
      readByOthers = readByOthers || (o != q && reads[o].count(q) > 0);
    }
    if (self && !readByOthers)
    {
      keep[q] = false;
      dropped = true;
    }
  }
  if (!dropped)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // Phase 4, the new row sort. newIndex[q] is the position of a kept column
  // q in the new rows, which have the kept columns in their order, of sort
  // newType: in the example, columns 0 and 2 become 0 and 1, of sort
  // (Tuple Int Int)
  std::vector<uint32_t> newIndex(m, 0);
  std::vector<TypeNode> types;
  uint32_t next = 0;
  TypeNode oldType = f[1].getType();
  for (size_t q = 0; q < m; q++)
  {
    if (keep[q])
    {
      newIndex[q] = next++;
      types.push_back(oldType.getTupleTypes()[q]);
    }
  }
  if (types.empty())
  {
    // every column is dead, as for an h that reads none: the rule does not
    // build an aggregate whose rows have no column
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // acc2 and r2, the rewriter's variables for an accumulator and for a row of
  // newType, are the variables of the new step and of the new h and P. acc2
  // must not be the row variable x nor occur in f's body, and r2 must not
  // occur in the bodies of h and P: the substitutions below would mix them
  // up with those occurrences
  TypeNode newType = d_nm->mkTupleType(types);
  Node acc2 = accumulatorVariable(newType);
  Node r2 = rowVariable(newType);
  if (acc2 == x || expr::hasSubterm(f[1], acc2) || expr::hasSubterm(h[1], r2)
      || (!P.isNull() && expr::hasSubterm(P[1], r2)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // reindex(body, var, to): body with each read ((_ tuple.select q) var) of
  // a kept column q replaced by ((_ tuple.select newIndex[q]) to), the same
  // column in the new tuple to. Reads of dead columns stay as they are; the
  // checks after each use make sure that var no longer occurs
  auto reindex = [&](const Node& body, const Node& var, const Node& to) {
    std::vector<Node> from, into;
    for (size_t q = 0; q < m; q++)
    {
      if (keep[q])
      {
        from.push_back(datatypes::TupleUtils::nthElementOfTuple(var, q));
        into.push_back(
            datatypes::TupleUtils::nthElementOfTuple(to, newIndex[q]));
      }
    }
    return body.substitute(from.begin(), from.end(), into.begin(), into.end());
  };
  // Phase 5, the smaller step and initial value: the e_q and i_q of the
  // kept columns, each e_q reading acc2 in place of acc. In the example,
  // e_2 = (+ ((_ tuple.select 2) acc) 1) becomes
  // (+ ((_ tuple.select 1) acc2) 1). A kept e_q reads no dead column of acc,
  // as no dead column is read by another, so acc is gone; the check makes
  // sure
  std::vector<Node> elems, init;
  for (size_t q = 0; q < m; q++)
  {
    if (keep[q])
    {
      elems.push_back(reindex(f[1][q], acc, acc2));
      init.push_back(i[q]);
    }
  }
  Node body = datatypes::TupleUtils::constructTupleFromElements(
      newType, elems, 0, elems.size() - 1);
  if (occursFree(body, acc))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the new aggregate ((_ table.aggr K) f2 i2 X): the same operator, so the
  // same group columns K, and f2 = (lambda ((x R) (acc2 newType)) body).
  // Its row for a group is the old row for that group without the dead
  // columns, and so is its row of initial values for an empty X
  Node f2 = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
  Node i2 = datatypes::TupleUtils::constructTupleFromElements(
      newType, init, 0, init.size() - 1);
  std::vector<Node> children{Y.getOperator(), f2, i2, X};
  Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  // Phase 6, the map and the filter over the new rows: h, and P if there is
  // one, reading the row r2 of the new aggregate. They read no dead column,
  // so their variable is gone; the checks make sure
  Node h2body = reindex(h[1], h[0][0], r2);
  if (occursFree(h2body, h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node below = aggr;
  if (!P.isNull())
  {
    // (bag.filter (lambda ((r2 newType)) p2body) aggr)
    Node p2body = reindex(P[1], P[0][0], r2);
    if (occursFree(p2body, P[0][0]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    below = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r2, p2body), aggr);
  }
  // (bag.map (lambda ((r2 newType)) h2body) below)
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(r2, h2body), below);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_DEAD_COLUMNS);
}

// Returns the columns that the filter predicate p fixes to constants, as a
// map from column index to constant: k -> c for each top-level conjunct
// (= ((_ tuple.select k) t) c) or (= c ((_ tuple.select k) t)) of p's body,
// with t the variable of p and c a constant. Every row that passes the
// filter has c in column k. For t : (Tuple Int Int),
//   (lambda ((t (Tuple Int Int)))
//     (and (= ((_ tuple.select 1) t) 5) (> ((_ tuple.select 0) t) 3)))
//   ---> returns {1 -> 5}
// The map is empty when p is not a lambda of one variable of a tuple sort.
std::map<uint32_t, Node> BagsRewriter::fixedColumns(const Node& p) const
{
  std::map<uint32_t, Node> fixed;
  // p may be kept as a function constant, read as the lambda it stands for
  Node lambda = asLambda(p);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1)
  {
    return fixed;
  }
  Node t = lambda[0][0];
  if (!t.getType().isTuple())
  {
    // the selectors of a row that is no tuple are no columns: in a filter
    // over a (Bag (Nullable Int)), (= (nullable.val t) 5) fixes no column
    return fixed;
  }
  // the top-level conjuncts of p's body, or the body as the one conjunct
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  for (const Node& c : conjuncts)
  {
    if (c.getKind() != Kind::EQUAL)
    {
      continue;
    }
    // the column on either side of the equality, the constant on the other.
    // When two conjuncts fix one column, the later one is kept; if their
    // constants differ, no row passes the filter, and either constant is
    // right for all the rows that do
    for (size_t side = 0; side < 2; side++)
    {
      if (c[side].getKind() == Kind::APPLY_SELECTOR && c[side][0] == t
          && c[1 - side].isConst())
      {
        fixed[datatypes::utils::indexOf(c[side].getOperator())] = c[1 - side];
      }
    }
  }
  return fixed;
}

// Returns body with each read ((_ tuple.select k) var) of a column k that
// fixed maps to a constant c replaced by c. fixed comes from fixedColumns or
// reachedGroupConstants, so that every row var ranges over has c in column
// k. For t : (Tuple Int Int) and fixed = {1 -> 5},
//   (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0)
//   ---> returns (tuple ((_ tuple.select 0) t) 5 0)
Node BagsRewriter::readFixed(const Node& body,
                             const Node& var,
                             const std::map<uint32_t, Node>& fixed) const
{
  // Nothing to replace for an empty map. When a lambda inside body binds
  // var again, the reads of that inner variable are not reads of the row,
  // and the substitution below would replace them too; body is then kept
  if (fixed.empty() || bindsVariable(body, var))
  {
    return body;
  }
  std::vector<Node> from, to;
  for (const std::pair<const uint32_t, Node>& fc : fixed)
  {
    from.push_back(datatypes::TupleUtils::nthElementOfTuple(var, fc.first));
    to.push_back(fc.second);
  }
  return body.substitute(from.begin(), from.end(), to.begin(), to.end());
}

// For F = (bag.filter P A), A = ((_ table.aggr K) f i X), returns a map from
// each column that has one constant in every row P keeps to that constant,
// when P keeps only reached groups; an empty map otherwise. A reached group
// is a group that some row of X falls in. Every group of a non-empty X is
// one, but an aggregate of an empty X still has one row, made of the initial
// values i, which comes from no reached group.
// P keeps only reached groups when it has a conjunct
// (>= ((_ tuple.select c) r) 1), r P's variable, on a counter column c: a
// column whose step adds 1 per row, (+ ((_ tuple.select c) acc) 1), from the
// initial value 0, as SQL's COUNT(*); it is at least 1 exactly in the
// reached groups. A reached group folds at least one row, so a column whose
// step is a constant has that constant, and a column the step keeps as it
// is, ((_ tuple.select q) acc), has its initial value. For
// X : (Bag (Tuple Int Int)) and r, acc : (Tuple Int Int Int Int),
//   F = (bag.filter (lambda ((r (Tuple Int Int Int Int)))
//                     (>= ((_ tuple.select 3) r) 1))
//         ((_ table.aggr 0)
//           (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int Int)))
//             (tuple ((_ tuple.select 0) t) 7 ((_ tuple.select 2) acc)
//                    (+ ((_ tuple.select 3) acc) 1)))
//           (tuple 0 0 4 0) X))
//   ---> returns {1 -> 7, 2 -> 4}
std::map<uint32_t, Node> BagsRewriter::reachedGroupConstants(
    const Node& F) const
{
  // F[1] is the aggregate A (the caller checks it). P must be a lambda of one
  // variable, f a lambda of the row and the accumulator whose body is a tuple
  // (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as many
  // components
  std::map<uint32_t, Node> constants;
  Node P = asLambda(F[0]);
  Node aggr = F[1];
  Node f = aggr[0];
  Node i = aggr[1];
  if (P.getKind() != Kind::LAMBDA || P[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i)
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return constants;
  }
  // r, a row of the aggregate's result; x, a row of X; acc, the accumulator
  Node r = P[0][0];
  Node x = f[0][0];
  Node acc = f[0][1];
  std::vector<Node> conjuncts;
  if (P[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
  }
  else
  {
    conjuncts.push_back(P[1]);
  }
  // reached: whether P tests a counter column positive, by the same checks
  // as counterColumn
  bool reached = false;
  for (const Node& c : conjuncts)
  {
    // c = (>= ((_ tuple.select col) r) 1), for a column col of A's rows
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::APPLY_SELECTOR || c[0][0] != r)
    {
      continue;
    }
    uint32_t col = datatypes::utils::indexOf(c[0].getOperator());
    if (col >= f[1].getNumChildren())
    {
      continue;
    }
    // e_col = (+ ((_ tuple.select col) acc) 1), or (+ 1 ..), and i_col = 0
    Node step = f[1][col];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, col);
    bool increment = step.getKind() == Kind::ADD && step.getNumChildren() == 2
                     && ((step[0] == own && step[1] == d_one)
                         || (step[1] == own && step[0] == d_one));
    if (increment && i[col].isConst()
        && i[col].getConst<Rational>() == Rational(0))
    {
      reached = true;
    }
  }
  if (!reached)
  {
    return constants;
  }
  for (size_t q = 0, m = f[1].getNumChildren(); q < m; q++)
  {
    Node c = f[1][q];
    if (c.isConst() && !occursFree(c, x) && !occursFree(c, acc))
    {
      // a constant step e_q = c: after the first row of the group, column q
      // is c, and it stays c
      constants[q] = c;
    }
    else if (c == datatypes::TupleUtils::nthElementOfTuple(acc, q)
             && i[q].isConst())
    {
      // a column the step keeps as it is, e_q = ((_ tuple.select q) acc),
      // with a constant initial value i_q: column q is i_q
      constants[q] = i[q];
    }
  }
  return constants;
}

// Returns the counter column of an aggregate ((_ table.aggr K) f i X) that
// the filter predicate P tests positive, or -1 when there is none. A counter
// column is a column c whose step adds 1 per row,
// (+ ((_ tuple.select c) acc) 1) or (+ 1 ((_ tuple.select c) acc)), from the
// initial value 0, as SQL's COUNT(*). P tests it positive when it has the
// top-level conjunct (>= ((_ tuple.select c) r) 1), r its variable, the form
// the arithmetic rewriter gives (> ((_ tuple.select c) r) 0) on integers.
// sqleq's translator from SQL adds such a counter and test to every
// aggregate with group columns: SQL's GROUP BY makes no group of an empty
// table, while table.aggr of an empty table has one row, of the initial
// values, whose count 0 the test rejects. A filter by P thus keeps only the
// reached groups, those that some row of X falls in.
// For X : (Bag (Tuple Int Int)),
//   P = (lambda ((r (Tuple Int Int Int)))
//         (and (>= ((_ tuple.select 2) r) 1) (>= ((_ tuple.select 1) r) 10)))
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
//         (tuple ((_ tuple.select 0) t)
//                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))
//                (+ ((_ tuple.select 2) acc) 1)))
//   i = (tuple 0 0 0)
//   ---> returns 2
int BagsRewriter::counterColumn(const Node& P,
                                const Node& f,
                                const Node& i) const
{
  // P must be a lambda of one variable (or a function constant that stands
  // for one), f a lambda of the row and the accumulator whose body is a
  // tuple (tuple e_0 .. e_(m-1)), and i a tuple (tuple i_0 .. i_(m-1)) of as
  // many components
  Node lambda = asLambda(P);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1
      || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i)
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return -1;
  }
  // r, a row of the aggregate's result; acc, the accumulator of f
  Node r = lambda[0][0];
  Node acc = f[0][1];
  std::vector<Node> conjuncts;
  if (lambda[1].getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), lambda[1].begin(), lambda[1].end());
  }
  else
  {
    conjuncts.push_back(lambda[1]);
  }
  for (const Node& c : conjuncts)
  {
    // c = (>= ((_ tuple.select col) r) 1), for a column col of the rows
    if (c.getKind() != Kind::GEQ || !c[1].isConst()
        || c[1].getConst<Rational>() != Rational(1)
        || c[0].getKind() != Kind::APPLY_SELECTOR || c[0][0] != r)
    {
      continue;
    }
    uint32_t col = datatypes::utils::indexOf(c[0].getOperator());
    if (col >= f[1].getNumChildren())
    {
      continue;
    }
    // e_col adds the integer 1 to its own column of acc, and i_col is 0
    Node step = f[1][col];
    Node own = datatypes::TupleUtils::nthElementOfTuple(acc, col);
    bool increment = step.getKind() == Kind::ADD && step.getNumChildren() == 2
                     && ((step[0] == own && step[1] == d_one)
                         || (step[1] == own && step[0] == d_one));
    if (increment && i[col].isConst()
        && i[col].getConst<Rational>() == Rational(0))
    {
      return static_cast<int>(col);
    }
  }
  return -1;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
