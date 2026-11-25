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
 * Notation, in SMT-LIB:
 *
 *   (tuple a b)                     a row of sort (Tuple Int Int)
 *   ((_ tuple.select 1) t)          column 1 of the row t
 *   ((_ tuple.project 0 2) t)       the row of columns 0 and 2 of t
 *   (nullable.some 5)               a value of sort (Nullable Int)
 *   (as nullable.null (Nullable Int))
 *   (bag e 2)                       the bag with e twice (Kind::BAG_MAKE)
 *   (bag.map f X)                   (f t) for every row t of X
 *   (bag.filter p X)                the rows t of X with (p t)
 *   (bag.fold f i X)                f folded over the rows of X, from i
 *   (table.product X Y)             the rows of X followed by those of Y
 *   ((_ table.project 0 2) X)       the map of X by tuple.project 0 2
 *   ((_ table.aggr 0) f i X)        each group of rows of X with one column
 *                                   0, folded by f from i
 *
 * X, Y, Z: tables; t, s: rows; acc: an accumulator. The rewriter's own bound
 * variables are row_N, t_N and acc_N.
 */

namespace {
/**
 * true for (as nullable.null (Nullable Int)); false for (nullable.some 5) and
 * for y : (Nullable Int).
 */
bool isNullConstant(const Node& n)
{
  return n.getKind() == Kind::APPLY_CONSTRUCTOR && n.getNumChildren() == 0
         && n.getType().isNullable();
}

/**
 * true for (tuple 1 (nullable.some 2)); false for (nullable.some 2), for a row
 * variable t and for ((_ tuple.project 0 1) t).
 */
bool isTupleTerm(const Node& t)
{
  return t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getType().isTuple();
}

/**
 * The bound variable for (role, n, tn), the same at every call, so that
 * rewriting a term twice builds the same lambda.
 */
Node mkRewriterVar(NodeManager* nm, const char* role, Node n, TypeNode tn)
{
  Node cache = nm->mkNode(Kind::SEXPR, nm->mkConst(String(role)), n);
  return nm->getBoundVarManager()->mkBoundVar(
      BoundVarId::BAGS_FIRST_INDEX, cache, tn);
}

/**
 * The same, printed as name. rowVariable passes "row",
 * (as bag.empty (Bag (Tuple Int Int))), "row_N" and (Tuple Int Int).
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

BagsRewriter::BagsRewriter(NodeManager* nm,
                           Rewriter* r,
                           HistogramStat<Rewrite>* statistics,
                           bool higherOrder,
                           const TableFacts* facts)
    : TheoryRewriter(nm),
      d_rewriter(r),
      d_statistics(statistics),
      d_higherOrder(higherOrder),
      d_facts(facts)
{
  d_zero = d_nm->mkConstInt(Rational(0));
  d_one = d_nm->mkConstInt(Rational(1));
}

// See bags_rewriter.h.
RewriteResponse BagsRewriter::postRewrite(TNode n)
{
  BagsRewriteResponse response;
  if (n.isConst())
  {
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

// See bags_rewriter.h.
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
    // IDENTICAL_NODES: (= A A) ---> true
    return BagsRewriteResponse(d_nm->mkConst(true), Rewrite::IDENTICAL_NODES);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSubBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SUBBAG);

  // SUB_BAG: (bag.subbag A B)
  //   ---> (= (bag.difference_subtract A B) (as bag.empty (Bag Int)))
  Node emptybag = d_nm->mkConst(EmptyBag(n[0].getType()));
  Node subtract = d_nm->mkNode(Kind::BAG_DIFFERENCE_SUBTRACT, n[0], n[1]);
  Node equal = subtract.eqNode(emptybag);
  return BagsRewriteResponse(equal, Rewrite::SUB_BAG);
}

BagsRewriteResponse BagsRewriter::rewriteMember(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MEMBER);

  // MEMBER: (bag.member x A) ---> (>= (bag.count x A) 1)
  Node count = d_nm->mkNode(Kind::BAG_COUNT, n[0], n[1]);
  Node geq = d_nm->mkNode(Kind::GEQ, count, d_one);
  return BagsRewriteResponse(geq, Rewrite::MEMBER);
}

BagsRewriteResponse BagsRewriter::rewriteMakeBag(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAKE);
  if (n[1].isConst() && n[1].getConst<Rational>().sgn() != 1)
  {
    // BAG_MAKE_COUNT_NEGATIVE: (bag x 0) ---> (as bag.empty (Bag Int))
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
    // COUNT_EMPTY: (bag.count x (as bag.empty (Bag Int))) ---> 0
    return BagsRewriteResponse(d_zero, Rewrite::COUNT_EMPTY);
  }
  if (n[1].getKind() == Kind::BAG_MAKE && n[0] == n[1][0] && n[1][1].isConst()
      && n[1][1].getConst<Rational>() > Rational(0))
  {
    // COUNT_BAG_MAKE: (bag.count x (bag x 3)) ---> 3
    Node c = n[1][1];
    return BagsRewriteResponse(c, Rewrite::COUNT_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteSetof(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_SETOF);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst()
      && n[0][1].getConst<Rational>().sgn() == 1)
  {
    // SETOF_BAG_MAKE: (bag.setof (bag x 3)) ---> (bag x 1)
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], d_one);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  if (n[0].getKind() == Kind::BAG_MAKE && !n[0][1].isConst())
  {
    // SETOF_BAG_MAKE: (bag.setof (bag x c)) ---> (bag x (ite (>= c 1) 1 0))
    Node count = d_nm->mkNode(
        Kind::ITE, d_nm->mkNode(Kind::GEQ, n[0][1], d_one), d_one, d_zero);
    Node bag = d_nm->mkNode(Kind::BAG_MAKE, n[0][0], count);
    return BagsRewriteResponse(bag, Rewrite::SETOF_BAG_MAKE);
  }
  if (n[0].getKind() == Kind::BAG_MAP)
  {
    // SETOF_PROJECTION_SORT, see rewriteSetofOfMap
    return rewriteSetofOfMap(n);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionMax(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_MAX);
  if (n[1].getKind() == Kind::BAG_EMPTY || n[0] == n[1])
  {
    // UNION_MAX_SAME_OR_EMPTY:
    //   (bag.union_max A A) ---> A
    //   (bag.union_max A (as bag.empty (Bag Int))) ---> A
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_SAME_OR_EMPTY);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // UNION_MAX_EMPTY: (bag.union_max (as bag.empty (Bag Int)) A) ---> A
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_EMPTY);
  }

  if ((n[1].getKind() == Kind::BAG_UNION_MAX
       || n[1].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0] == n[1][0] || n[0] == n[1][1]))
  {
    // UNION_MAX_UNION_LEFT:
    //   (bag.union_max A (bag.union_max B A))
    //   ---> (bag.union_max B A)
    //   (bag.union_max A (bag.union_disjoint A B))
    //   ---> (bag.union_disjoint A B)
    return BagsRewriteResponse(n[1], Rewrite::UNION_MAX_UNION_LEFT);
  }

  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       || n[0].getKind() == Kind::BAG_UNION_DISJOINT)
      && (n[0][0] == n[1] || n[0][1] == n[1]))
  {
    // UNION_MAX_UNION_RIGHT:
    //   (bag.union_max (bag.union_max A B) A)
    //   ---> (bag.union_max A B)
    //   (bag.union_max (bag.union_disjoint B A) A)
    //   ---> (bag.union_disjoint B A)
    return BagsRewriteResponse(n[0], Rewrite::UNION_MAX_UNION_RIGHT);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteUnionDisjoint(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_UNION_DISJOINT);
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // UNION_DISJOINT_EMPTY_RIGHT:
    //   (bag.union_disjoint A (as bag.empty (Bag Int))) ---> A
    return BagsRewriteResponse(n[0], Rewrite::UNION_DISJOINT_EMPTY_RIGHT);
  }
  if (n[0].getKind() == Kind::BAG_EMPTY)
  {
    // UNION_DISJOINT_EMPTY_LEFT:
    //   (bag.union_disjoint (as bag.empty (Bag Int)) A) ---> A
    return BagsRewriteResponse(n[1], Rewrite::UNION_DISJOINT_EMPTY_LEFT);
  }
  if ((n[0].getKind() == Kind::BAG_UNION_MAX
       && n[1].getKind() == Kind::BAG_INTER_MIN)
      || (n[1].getKind() == Kind::BAG_UNION_MAX
          && n[0].getKind() == Kind::BAG_INTER_MIN))

  {
    // UNION_DISJOINT_MAX_MIN:
    //   (bag.union_disjoint (bag.union_max A B) (bag.inter_min B A))
    //   ---> (bag.union_disjoint A B)
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
    // INTERSECTION_EMPTY_LEFT:
    //   (bag.inter_min (as bag.empty (Bag Int)) A)
    //   ---> (as bag.empty (Bag Int))
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_EMPTY_LEFT);
  }
  if (n[1].getKind() == Kind::BAG_EMPTY)
  {
    // INTERSECTION_EMPTY_RIGHT:
    //   (bag.inter_min A (as bag.empty (Bag Int)))
    //   ---> (as bag.empty (Bag Int))
    return BagsRewriteResponse(n[1], Rewrite::INTERSECTION_EMPTY_RIGHT);
  }
  if (n[0] == n[1])
  {
    // INTERSECTION_SAME: (bag.inter_min A A) ---> A
    return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SAME);
  }
  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // INTERSECTION_SHARED_LEFT:
      //   (bag.inter_min A (bag.union_disjoint B A)) ---> A
      //   (bag.inter_min A (bag.union_max A B)) ---> A
      return BagsRewriteResponse(n[0], Rewrite::INTERSECTION_SHARED_LEFT);
    }
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT
      || n[0].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // INTERSECTION_SHARED_RIGHT:
      //   (bag.inter_min (bag.union_disjoint B A) A) ---> A
      //   (bag.inter_min (bag.union_max A B) A) ---> A
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
    // SUBTRACT_RETURN_LEFT:
    //   (bag.difference_subtract A (as bag.empty (Bag Int))) ---> A
    //   (bag.difference_subtract (as bag.empty (Bag Int)) A)
    //   ---> (as bag.empty (Bag Int))
    return BagsRewriteResponse(n[0], Rewrite::SUBTRACT_RETURN_LEFT);
  }
  if (n[0] == n[1])
  {
    // SUBTRACT_SAME:
    //   (bag.difference_subtract A A) ---> (as bag.empty (Bag Int))
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_SAME);
  }

  if (n[0].getKind() == Kind::BAG_UNION_DISJOINT)
  {
    if (n[1] == n[0][0])
    {
      // SUBTRACT_DISJOINT_SHARED_LEFT:
      //   (bag.difference_subtract (bag.union_disjoint A B) A) ---> B
      return BagsRewriteResponse(n[0][1],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT);
    }
    if (n[1] == n[0][1])
    {
      // SUBTRACT_DISJOINT_SHARED_RIGHT:
      //   (bag.difference_subtract (bag.union_disjoint B A) A) ---> B
      return BagsRewriteResponse(n[0][0],
                                 Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT);
    }
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // SUBTRACT_FROM_UNION:
      //   (bag.difference_subtract A (bag.union_disjoint B A))
      //   ---> (as bag.empty (Bag Int))
      //   (bag.difference_subtract A (bag.union_max A B))
      //   ---> (as bag.empty (Bag Int))
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::SUBTRACT_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // SUBTRACT_MIN:
      //   (bag.difference_subtract (bag.inter_min B A) A)
      //   ---> (as bag.empty (Bag Int))
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
    // REMOVE_RETURN_LEFT:
    //   (bag.difference_remove A (as bag.empty (Bag Int))) ---> A
    //   (bag.difference_remove (as bag.empty (Bag Int)) A)
    //   ---> (as bag.empty (Bag Int))
    return BagsRewriteResponse(n[0], Rewrite::REMOVE_RETURN_LEFT);
  }

  if (n[0] == n[1])
  {
    // REMOVE_SAME:
    //   (bag.difference_remove A A) ---> (as bag.empty (Bag Int))
    Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
    return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_SAME);
  }

  if (n[1].getKind() == Kind::BAG_UNION_DISJOINT
      || n[1].getKind() == Kind::BAG_UNION_MAX)
  {
    if (n[0] == n[1][0] || n[0] == n[1][1])
    {
      // REMOVE_FROM_UNION:
      //   (bag.difference_remove A (bag.union_disjoint B A))
      //   ---> (as bag.empty (Bag Int))
      //   (bag.difference_remove A (bag.union_max A B))
      //   ---> (as bag.empty (Bag Int))
      Node emptyBag = d_nm->mkConst(EmptyBag(n.getType()));
      return BagsRewriteResponse(emptyBag, Rewrite::REMOVE_FROM_UNION);
    }
  }

  if (n[0].getKind() == Kind::BAG_INTER_MIN)
  {
    if (n[1] == n[0][0] || n[1] == n[0][1])
    {
      // REMOVE_MIN:
      //   (bag.difference_remove (bag.inter_min B A) A)
      //   ---> (as bag.empty (Bag Int))
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
    // CHOOSE_BAG_MAKE: (bag.choose (bag x 3)) ---> x
    return BagsRewriteResponse(n[0][0], Rewrite::CHOOSE_BAG_MAKE);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::rewriteCard(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_CARD);
  if (n[0].getKind() == Kind::BAG_MAKE && n[0][1].isConst())
  {
    // CARD_BAG_MAKE: (bag.card (bag x 3)) ---> 3
    return BagsRewriteResponse(n[0][1], Rewrite::CARD_BAG_MAKE);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

bool BagsRewriter::readTableFact(TNode lit, TableFacts& facts) const
{
  // a negated equality states no fact
  if (lit.getKind() != Kind::EQUAL || !lit[0].getType().isBag())
  {
    return false;
  }
  bool key = readKey(lit, facts);
  bool notNull = readNotNull(lit, facts);
  return key || notNull;
}

namespace {
/**
 * The table constant T that M projects and the columns K it keeps, or a null T:
 *   ((_ table.project 2 0) X) ---> X, 2 0
 *   (bag.map (lambda ((t (Tuple Int Int Int))) ((_ tuple.project 2 0) t)) X)
 *   ---> X, 2 0
 */
std::pair<Node, std::vector<uint32_t>> projectionOf(
    const Node& M, const std::function<std::vector<uint32_t>(const Node&)>& ix)
{
  if (M.getKind() == Kind::TABLE_PROJECT && M[0].isVar())
  {
    return {M[0], M.getOperator().getConst<ProjectOp>().getIndices()};
  }
  if (M.getKind() == Kind::BAG_MAP && M[1].isVar())
  {
    std::vector<uint32_t> K = ix(M[0]);
    if (!K.empty())
    {
      return {M[1], K};
    }
  }
  return {Node::null(), {}};
}
}  // namespace

bool BagsRewriter::readKey(const TNode& n, TableFacts& facts) const
{
  std::function<std::vector<uint32_t>(const Node&)> ix = [this](const Node& f) {
    return projectionIndices(asLambda(f));
  };
  for (size_t i = 0; i < 2; i++)
  {
    // M, either side, a projection of the table constant T onto K
    auto [T, K] = projectionOf(n[1 - i], ix);
    // no columns would be a key {} of a table of at most one row, which the
    // rules do not read
    if (T.isNull() || K.empty())
    {
      continue;
    }
    Node S = n[i];
    bool isSet = false;
    if (S.getKind() == Kind::BAG_SETOF && S[0] == n[1 - i])
    {
      // (= (bag.setof M) M)
      isSet = true;
    }
    else if (S.getKind() == Kind::BAG_MAP && S[1].getKind() == Kind::BAG_SETOF)
    {
      // (= M (bag.map h (bag.setof M'))), M' the projection of T onto the
      // columns of M in order and h a permutation of its columns, so that the
      // image of the set (bag.setof M') is a set
      auto [T2, K2] = projectionOf(S[1][0], ix);
      std::vector<uint32_t> H = ix(S[0]);
      std::vector<uint32_t> sorted = K;
      std::sort(sorted.begin(), sorted.end());
      std::vector<uint32_t> perm = H;
      std::sort(perm.begin(), perm.end());
      bool permutation = perm.size() == K2.size();
      for (size_t j = 0; permutation && j < perm.size(); j++)
      {
        permutation = perm[j] == j;
      }
      isSet =
          T2 == T && K2 == sorted && permutation
          && std::adjacent_find(sorted.begin(), sorted.end()) == sorted.end();
    }
    if (!isSet)
    {
      continue;
    }
    // K = 2 0 2 ---> {0, 2}
    std::set<uint32_t> key(K.begin(), K.end());
    std::vector<std::set<uint32_t>>& keys = facts.d_keys[T];
    if (std::find(keys.begin(), keys.end(), key) == keys.end())
    {
      keys.push_back(key);
    }
    return true;
  }
  return false;
}

bool BagsRewriter::readNotNull(const TNode& n, TableFacts& facts) const
{
  // n = (= (bag.filter p X) (as bag.empty (Bag (Tuple Int (Nullable Int))))),
  // for
  //   p = (lambda ((t (Tuple Int (Nullable Int))))
  //         (= ((_ tuple.select 1) t) (as nullable.null (Nullable Int))))
  // with both equalities either way round.
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
    if (!T.isVar() || !T.getType().getBagElementType().isTuple()
        || p.getKind() != Kind::LAMBDA || p[0].getNumChildren() != 1
        || p[1].getKind() != Kind::EQUAL)
    {
      continue;
    }
    Node v = p[0][0];
    Node col;
    // col = ((_ tuple.select 1) t)
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
    facts.d_notNull[T].insert(datatypes::utils::indexOf(col.getOperator()));
    return true;
  }
  return false;
}

bool BagsRewriter::nonNullTerm(const Node& t,
                               const Node& x,
                               const std::set<uint32_t>& nx,
                               const Node& acc,
                               const std::set<uint32_t>& nacc) const
{
  // ((_ tuple.select 0) x) : Int ---> true
  if (!t.getType().isNullable())
  {
    return true;
  }
  if (t.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // (nullable.some a) ---> true, (as nullable.null (Nullable Int)) ---> false
    return t.getNumChildren() == 1;
  }
  if (t.getKind() == Kind::APPLY_SELECTOR && t[0].getType().isTuple())
  {
    // for nx = {1}: ((_ tuple.select 1) x) ---> true; likewise acc and nacc
    uint32_t k = datatypes::utils::indexOf(t.getOperator());
    return (!x.isNull() && t[0] == x && nx.count(k) > 0)
           || (!acc.isNull() && t[0] == acc && nacc.count(k) > 0);
  }
  if (t.getKind() == Kind::BAG_FOLD)
  {
    //   (bag.fold (lambda ((t (Tuple Int Int)) (acc (Nullable Int)))
    //               (ite p (nullable.some ((_ tuple.select 0) t)) acc))
    //             (nullable.some 0)
    //             X)
    //   ---> true
    Node l = asLambda(t[0]);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2
        && t[1].getKind() == Kind::APPLY_CONSTRUCTOR
        && t[1].getNumChildren() == 1)
    {
      // keeps((ite p (nullable.some a) acc)) = true
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
    return false;
  }
  if (t.getKind() == Kind::ITE)
  {
    // for nx = {1}:
    //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x)) b c)
    //   ---> nonNullTerm(c)
    //   (ite p b c)
    //   ---> nonNullTerm(b) and nonNullTerm(c)
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
  // y : (Nullable Int) ---> false
  return false;
}

std::set<uint32_t> BagsRewriter::aggregateNonNull(const Node& B) const
{
  std::set<uint32_t> out;
  Node f = asLambda(B[0]);
  Node init = B[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(init)
      || init.getNumChildren() != f[1].getNumChildren())
  {
    return out;
  }
  std::set<uint32_t> nx = nonNullColumns(B[2]);
  Node x = f[0][0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  // inv: the columns never null in i that every step keeps never null. For
  //   i = (tuple (nullable.some 0) (as nullable.null (Nullable Int)))
  // and the body (tuple ((_ tuple.select 0) acc) (nullable.some 1)),
  // inv = {0}.
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
  // out = {0, 1} for the example above
  for (size_t j = 0; j < w; j++)
  {
    if (nonNullTerm(f[1][j], x, nx, acc, inv))
    {
      out.insert(j);
    }
  }
  return out;
}

std::set<uint32_t> BagsRewriter::nonNullColumns(const Node& B) const
{
  auto it = d_nonNull.find(B);
  if (it != d_nonNull.end())
  {
    return it->second;
  }
  std::set<uint32_t> out;
  TypeNode et = B.getType().getBagElementType();
  // (Bag Int) ---> {}
  if (et.isTuple())
  {
    switch (B.getKind())
    {
      case Kind::BAG_FILTER:
      {
        // For column 0 of Y never null,
        //   (bag.filter
        //     (lambda ((t (Tuple (Nullable Int) (Nullable Int))))
        //       (nullable.is_some ((_ tuple.select 1) t)))
        //     Y)
        //   ---> {0, 1}
        out = nonNullColumns(B[1]);
        Node p = asLambda(B[0]);
        if (p.getKind() == Kind::LAMBDA && p[0].getNumChildren() == 1)
        {
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
            // (nullable.is_some ((_ tuple.select 1) x)) ---> 1
            Node a;
            int ci = datatypes::utils::isTester(c, a);
            if (ci >= 0 && a.getKind() == Kind::APPLY_SELECTOR && a[0] == x
                && a.getType().isNullable()
                && a.getType().getDType()[ci].getNumArgs() == 1)
            {
              out.insert(datatypes::utils::indexOf(a.getOperator()));
            }
            // (= ((_ tuple.select 1) x) (nullable.some 5)) ---> 1
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
        break;
      }
      // (bag.setof Y), (bag.difference_subtract Y Z) ---> nonNullColumns(Y)
      case Kind::BAG_SETOF:
      case Kind::BAG_DIFFERENCE_SUBTRACT:
      case Kind::BAG_DIFFERENCE_REMOVE: out = nonNullColumns(B[0]); break;
      case Kind::BAG_INTER_MIN:
      {
        // (bag.inter_min Y Z), with {0} for Y and {1} for Z ---> {0, 1}
        out = nonNullColumns(B[0]);
        std::set<uint32_t> more = nonNullColumns(B[1]);
        out.insert(more.begin(), more.end());
        break;
      }
      case Kind::BAG_UNION_DISJOINT:
      case Kind::BAG_UNION_MAX:
      {
        // (bag.union_disjoint Y Z), with {0, 1} for Y and {1} for Z ---> {1}
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
        // (table.product Y Z), Y of 2 columns, with {0} for Y and Z
        // ---> {0, 2}
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
        // For column 1 of Y never null,
        //   (bag.map
        //     (lambda ((t (Tuple Int (Nullable Int))))
        //       (tuple ((_ tuple.select 1) t) (nullable.some 0)))
        //     Y)
        //   ---> {0, 1}
        // and ((_ tuple.project 1 0) t) as the body ---> {}
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
      case Kind::TABLE_AGGREGATE: out = aggregateNonNull(B); break;
      default:
        // a table constant with column 1 NOT NULL in the facts ---> {1}; any
        // other node ---> {}
        if (B.isVar() && d_facts != nullptr)
        {
          auto facts = d_facts->d_notNull.find(B);
          if (facts != d_facts->d_notNull.end())
          {
            out = facts->second;
          }
        }
        break;
    }
  }
  d_nonNull[B] = out;
  return out;
}

Node BagsRewriter::assumeNonNull(const Node& body,
                                 const Node& x,
                                 const std::set<uint32_t>& cols) const
{
  if (cols.empty())
  {
    return body;
  }
  // for cols = {1}:
  //   (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x)) ---> false
  //   (nullable.is_some ((_ tuple.select 1) x)) ---> true
  //   (nullable.is_null ((_ tuple.select 1) x)) ---> false
  //   any other n ---> null
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
  // body rebuilt bottom up, without recursion; cache: node ---> replacement.
  // Nested lambdas are entered too, without checking whether one binds x.
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
    // the operator first for ((_ tuple.select 1) x)
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

std::vector<std::set<uint32_t>> BagsRewriter::keysOf(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  // (bag.filter p (bag.filter q X)) ---> X
  Node T = B;
  while (T.getKind() == Kind::BAG_FILTER)
  {
    T = T[1];
  }
  if (!T.isVar() || d_facts == nullptr)
  {
    return keys;
  }
  auto it = d_facts->d_keys.find(T);
  if (it != d_facts->d_keys.end())
  {
    keys = it->second;
  }
  return keys;
}

std::vector<std::set<uint32_t>> BagsRewriter::rowKeys(const Node& B) const
{
  std::vector<std::set<uint32_t>> keys;
  TypeNode et = B.getType().getBagElementType();
  // (Bag Int) ---> {}
  if (!et.isTuple())
  {
    return keys;
  }
  size_t width = et.getTupleLength();
  switch (B.getKind())
  {
    case Kind::BAG_FILTER:
    {
      // For X : (Bag (Tuple Int Int Int)) with the key {0, 1},
      //   (bag.filter
      //     (lambda ((t (Tuple Int Int Int))) (= ((_ tuple.select 1) t) 5))
      //     X)
      //   ---> {{0}}
      // and with the key {1, 2},
      //   (bag.filter
      //     (lambda ((t (Tuple Int Int Int)))
      //       (= ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
      //     X)
      //   ---> {{0, 1}}
      keys = rowKeys(B[1]);
      // {1 -> 5} for the first example
      std::map<uint32_t, Node> fixed = fixedColumns(B[0]);
      Node P = asLambda(B[0]);
      // find(2) = 0 for the second example
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
      // {0, 1} ---> {0}, {1, 2} ---> {1, 0}, and {1} with column 1 fixed
      // ---> {}, at most one row
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
    // (bag.difference_subtract Y Z) ---> rowKeys(Y)
    case Kind::BAG_DIFFERENCE_SUBTRACT:
    case Kind::BAG_DIFFERENCE_REMOVE: return rowKeys(B[0]);
    case Kind::BAG_INTER_MIN:
    {
      // (bag.inter_min Y Z) ---> rowKeys(Y) and rowKeys(Z)
      keys = rowKeys(B[0]);
      std::vector<std::set<uint32_t>> more = rowKeys(B[1]);
      keys.insert(keys.end(), more.begin(), more.end());
      return keys;
    }
    case Kind::BAG_SETOF:
    {
      // (bag.setof Y) ---> rowKeys(Y) and all the columns
      keys = rowKeys(B[0]);
      // but those of a map that are constants or repeat an earlier column. For
      // Y with no key,
      //   (bag.setof
      //     (bag.map
      //       (lambda ((t (Tuple Int Int)))
      //         (tuple ((_ tuple.select 0) t) 5 ((_ tuple.select 0) t)))
      //       Y))
      //   ---> {{0}}
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
      // For X with the key {0},
      //   (bag.map
      //     (lambda ((t (Tuple Int Int)))
      //       (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
      //     X)
      //   ---> {{1}}
      Node g = asLambda(B[0]);
      if (g.getKind() != Kind::LAMBDA || g[0].getNumChildren() != 1
          || !isTupleTerm(g[1]) || g[1].getNumChildren() != width)
      {
        return keys;
      }
      // carried = {0 -> 1, 1 -> 0} for the example
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
      // {0} ---> {1}; a key with a column that g does not copy is lost
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
      // (table.product Y Z), Y of 2 columns, with {0} for Y and Z
      // ---> {{0, 2}}
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
      // For
      //   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
      //         (tuple (+ ((_ tuple.select 1) acc) 1) ((_ tuple.select 0) t)))
      //   ((_ table.aggr 0) f i Y) ---> {{1}}
      //   ((_ table.aggr 1) f i Y) ---> {}
      //   (table.aggr f i Y) ---> {{}}
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
  // a table constant ---> keysOf(B); any other node ---> {}
  if (B.isVar())
  {
    return keysOf(B);
  }
  return keys;
}

BagsRewriteResponse BagsRewriter::postRewriteEqual(const TNode& n) const
{
  Assert(n.getKind() == Kind::EQUAL);
  if (n[0] == n[1])
  {
    // EQ_REFL: (= A A) ---> true
    Node ret = d_nm->mkConst(true);
    return BagsRewriteResponse(ret, Rewrite::EQ_REFL);
  }

  if (n[0].isConst() && n[1].isConst())
  {
    // EQ_CONST_FALSE: (= (bag 1 2) (bag 1 3)) ---> false
    Node ret = d_nm->mkConst(false);
    return BagsRewriteResponse(ret, Rewrite::EQ_CONST_FALSE);
  }

  // EQ_SYM: (= B A) ---> (= A B)
  if (n[0] > n[1])
  {
    Node ret = d_nm->mkNode(Kind::EQUAL, n[1], n[0]);
    return BagsRewriteResponse(ret, Rewrite::EQ_SYM);
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteMap(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_MAP);
  TypeNode mapType = n.getType();
  TypeNode argType = n[1].getType();
  if (mapType == argType && argType.getBagElementType().isTuple())
  {
    // MAP_IDENTITY:
    //   (bag.map
    //     (lambda ((t (Tuple Int Int)))
    //       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t)))
    //     X)
    //   ---> X
    // J = 0 1, also for ((_ tuple.project 0 1) t)
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
    // NOT_NULL_COLUMNS, for column 1 of X NOT NULL:
    //   (bag.map
    //     (lambda ((t (Tuple Int (Nullable Int))))
    //       (tuple (nullable.is_some ((_ tuple.select 1) t))))
    //     X)
    //   ---> (bag.map (lambda ((t (Tuple Int (Nullable Int)))) (tuple true)) X)
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
    // MAP_CONST, for g = (lambda ((y Int)) (+ y 1)):
    //   (bag.map g (bag 1 3)) ---> (bag 2 3)
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
      // MAP_BAG_MAKE: (bag.map g (bag x 3)) ---> (bag (g x) 3)
      Node mappedElement = d_nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, mappedElement, n[1][1]);
      return BagsRewriteResponse(ret, Rewrite::MAP_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // MAP_UNION_DISJOINT:
      //   (bag.map g (bag.union_disjoint A B))
      //   ---> (bag.union_disjoint (bag.map g A) (bag.map g B))
      Node a = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_MAP, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::MAP_UNION_DISJOINT);
    }

    case Kind::BAG_MAP:
    {
      // MAP_MAP (rewriteMapOfMap), else the rules below
      BagsRewriteResponse r = rewriteMapOfMap(n);
      if (r.d_node != n)
      {
        return r;
      }
      break;
    }
    default: break;
  }
  {
    // AGGREGATE_DEAD_COLUMNS, see rewriteAggregateDeadColumns
    BagsRewriteResponse r = rewriteAggregateDeadColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[1].getKind() == Kind::BAG_FILTER)
  {
    // MAP_EQUAL_COLUMNS, for
    //   P = (lambda ((s (Tuple Int Int)))
    //         (= ((_ tuple.select 0) s) ((_ tuple.select 1) s))):
    //   (bag.map
    //     (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
    //     (bag.filter P X))
    //   ---> (bag.map
    //          (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 0) t)))
    //          (bag.filter P X))
    Node h = asLambda(n[0]);
    Node P = asLambda(n[1][0]);
    if (h.getKind() == Kind::LAMBDA && h[0].getNumChildren() == 1
        && P.getKind() == Kind::LAMBDA && P[0].getNumChildren() == 1
        && n[1][1].getType().getBagElementType().isTuple())
    {
      Node r = P[0][0];
      size_t w = n[1][1].getType().getBagElementType().getTupleLength();
      // rep: a union-find of the columns; find(1) = 0 for the example
      std::vector<uint32_t> rep(w);
      for (uint32_t col = 0; col < w; col++)
      {
        rep[col] = col;
      }
      std::function<uint32_t(uint32_t)> find = [&](uint32_t col) {
        return rep[col] == col ? col : (rep[col] = find(rep[col]));
      };
      std::vector<Node> conjuncts;
      if (P[1].getKind() == Kind::AND)
      {
        conjuncts.insert(conjuncts.end(), P[1].begin(), P[1].end());
      }
      else
      {
        conjuncts.push_back(P[1]);
      }
      // (= ((_ tuple.select 0) s) ((_ tuple.select 1) s)): rep[1] = 0
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
      // ((_ tuple.select 1) t) ---> ((_ tuple.select 0) t)
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
    // MAP_FIXED_COLUMNS, for
    //   Q = (lambda ((s (Tuple Int Int))) (= ((_ tuple.select 1) s) 5)):
    //   (bag.map
    //     (lambda ((t (Tuple Int Int)))
    //       (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0))
    //     (bag.filter Q X))
    //   ---> (bag.map
    //          (lambda ((t (Tuple Int Int)))
    //            (tuple ((_ tuple.select 0) t) 5 0))
    //          (bag.filter Q X))
    std::map<uint32_t, Node> fixed = fixedColumns(n[1][0]);
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
    // CANONICAL_VARIABLE, last, for g = (lambda ((y Int)) (+ y 1)):
    //   (bag.map g A) ---> (bag.map (lambda ((t_N Int)) (+ t_N 1)) A)
    Node canonical = canonicalLambda(n[0]);
    if (canonical != n[0])
    {
      Node ret = d_nm->mkNode(Kind::BAG_MAP, canonical, n[1]);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteFilter(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FILTER);
  Node P = n[0];
  Node A = n[1];
  TypeNode t = A.getType();
  {
    // NOT_NULL_COLUMNS, for column 1 of A NOT NULL:
    //   (bag.filter
    //     (lambda ((t (Tuple Int (Nullable Int))))
    //       (and (nullable.is_some ((_ tuple.select 1) t))
    //            (> ((_ tuple.select 0) t) 3)))
    //     A)
    //   ---> (bag.filter
    //          (lambda ((t (Tuple Int (Nullable Int))))
    //            (and true (> ((_ tuple.select 0) t) 3)))
    //          A)
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
      // FILTER_TRUE: (bag.filter (lambda ((y Int)) true) A) ---> A
      // FILTER_FALSE:
      //   (bag.filter (lambda ((y Int)) false) A) ---> (as bag.empty (Bag Int))
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
    // FILTER_NULLABLE_TRUTH, for
    //   b = (ite (nullable.is_some y)
    //            (nullable.some (> (nullable.val y) 3))
    //            (as nullable.null (Nullable Bool))):
    //   (bag.filter
    //     (lambda ((y (Nullable Int)))
    //       (and (nullable.is_some b) (nullable.val b)))
    //     C)
    //   ---> (bag.filter
    //          (lambda ((y (Nullable Int)))
    //            (ite (nullable.is_some y) (> (nullable.val y) 3) false))
    //          C)
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
      // unreachable: the test above returns for a constant body
      if (body.getConst<bool>())
      {
        return BagsRewriteResponse(A, Rewrite::FILTER_TRUE);
      }
      return BagsRewriteResponse(d_nm->mkConst(EmptyBag(t)),
                                 Rewrite::FILTER_FALSE);
    }
    {
      std::vector<Node> cs;
      if (body.getKind() == Kind::AND)
      {
        cs.insert(cs.end(), body.begin(), body.end());
      }
      else
      {
        cs.push_back(body);
      }
      std::vector<Node> flat = cs;
      // FILTER_CONFLICTING_CONSTANTS:
      //   (bag.filter (lambda ((y Int)) (and (= y 1) (= y 2))) A)
      //   ---> (as bag.empty (Bag Int))
      // fixed = {y -> 1}, then y -> 2 conflicts
      std::map<Node, Node> fixed;
      for (const Node& c : flat)
      {
        if (c.getKind() != Kind::EQUAL)
        {
          continue;
        }
        bool leftConst = c[0].isConst();
        bool rightConst = c[1].isConst();
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
      // for column 1 of Y never null, (>= (bag.count (tuple a e) Y) 1) puts e
      // in nonNull
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
      // FILTER_CONFLICTING_CONSTANTS, the conjuncts that others imply go:
      //   (and (nullable.is_some a) (= a (nullable.some 5)))
      //   ---> (= a (nullable.some 5))
      //   (and (nullable.is_some e) q), for e in nonNull
      //   ---> q
      //   (and (>= a 1) (>= b 1) (>= (* a b) 1))
      //   ---> (and (>= a 1) (>= b 1))
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
        Node a;
        int ci = datatypes::utils::isTester(c, a);
        auto it = ci >= 0 ? fixed.find(a) : fixed.end();
        if (it != fixed.end() && it->second.getKind() == Kind::APPLY_CONSTRUCTOR
            && datatypes::utils::indexOf(it->second.getOperator())
                   == static_cast<size_t>(ci))
        {
          // (nullable.is_some a) next to (= a (nullable.some 5))
          continue;
        }
        if (ci >= 0 && nonNull.count(a) && a.getType().isNullable()
            && a.getType().getDType()[ci].getNumArgs() == 1)
        {
          // (nullable.is_some e), for e in nonNull
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
      // no conjunct left ---> true
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
      // FILTER_FALSE:
      //   (bag.filter (lambda ((y Int)) (and (> y 3) (not (> y 3)))) A)
      //   ---> (as bag.empty (Bag Int))
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
    // CANONICAL_VARIABLE, for p = (lambda ((y Int)) (> y 0)):
    //   (bag.filter p A) ---> (bag.filter (lambda ((t_N Int)) (> t_N 0)) A)
    Node canonical = canonicalLambda(P);
    if (canonical != P)
    {
      Node ret = d_nm->mkNode(Kind::BAG_FILTER, canonical, A);
      return BagsRewriteResponse(ret, Rewrite::CANONICAL_VARIABLE);
    }
  }
  if (A.isConst())
  {
    // FILTER_CONST:
    //   (bag.filter p (bag.union_disjoint (bag 1 2) (bag (- 3) 1)))
    //   ---> (bag 1 2)

    Node ret = BagsUtils::evaluateBagFilter(n);
    return BagsRewriteResponse(ret, Rewrite::FILTER_CONST);
  }
  Kind k = A.getKind();
  switch (k)
  {
    case Kind::BAG_MAKE:
    {
      // FILTER_BAG_MAKE: (bag.filter p (bag x 2)) ---> (bag x (ite (p x) 2 0))
      // a (bag x ..), not an ite of bags, so that maps and products apply
      Node pOfe = d_nm->mkNode(Kind::APPLY_UF, P, A[0]);
      Node count = d_nm->mkNode(Kind::ITE, pOfe, A[1], d_zero);
      Node ret = d_nm->mkNode(Kind::BAG_MAKE, A[0], count);
      return BagsRewriteResponse(ret, Rewrite::FILTER_BAG_MAKE);
    }

    case Kind::BAG_UNION_DISJOINT:
    {
      // FILTER_UNION_DISJOINT:
      //   (bag.filter p (bag.union_disjoint A B))
      //   ---> (bag.union_disjoint (bag.filter p A) (bag.filter p B))
      Node a = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][0]);
      Node b = d_nm->mkNode(Kind::BAG_FILTER, n[0], n[1][1]);
      Node ret = d_nm->mkNode(Kind::BAG_UNION_DISJOINT, a, b);
      return BagsRewriteResponse(ret, Rewrite::FILTER_UNION_DISJOINT);
    }

    // FILTER_MAP, see rewriteFilterOfMap
    case Kind::BAG_MAP: return rewriteFilterOfMap(n);
    default: return BagsRewriteResponse(n, Rewrite::NONE);
  }
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
      // ALL_EMPTY: (bag.all p (as bag.empty (Bag Int))) ---> true
      return BagsRewriteResponse(nm->mkConst(true), Rewrite::ALL_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // ALL_BAG_MAKE: (bag.all p (bag x c)) ---> (or (p x) (<= c 0))
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::LEQ, n[1][1], d_zero);
      Node ret = px.orNode(leq);
      return BagsRewriteResponse(ret, Rewrite::ALL_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // ALL_UNION_DISJOINT:
      //   (bag.all p (bag.union_disjoint A B))
      //   ---> (and (bag.all p A) (bag.all p B))
      Node a = nm->mkNode(Kind::BAG_ALL, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_ALL, n[0], n[1][1]);
      Node ret = a.andNode(b);
      return BagsRewriteResponse(ret, Rewrite::ALL_UNION_DISJOINT);
    }
    default:
    {
      // ALL_FILTER: (bag.all p A) ---> (= (bag.filter p A) A)
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
      // SOME_EMPTY: (bag.some p (as bag.empty (Bag Int))) ---> false
      return BagsRewriteResponse(nm->mkConst(false), Rewrite::SOME_EMPTY);
    }
    case Kind::BAG_MAKE:
    {
      // SOME_BAG_MAKE: (bag.some p (bag x c)) ---> (and (p x) (> c 0))
      Node px = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node leq = nm->mkNode(Kind::GT, n[1][1], d_zero);
      Node ret = px.andNode(leq);
      return BagsRewriteResponse(ret, Rewrite::SOME_BAG_MAKE);
    }
    case Kind::BAG_UNION_DISJOINT:
    {
      // SOME_UNION_DISJOINT:
      //   (bag.some p (bag.union_disjoint A B))
      //   ---> (or (bag.some p A) (bag.some p B))
      Node a = nm->mkNode(Kind::BAG_SOME, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::BAG_SOME, n[0], n[1][1]);
      Node ret = a.orNode(b);
      return BagsRewriteResponse(ret, Rewrite::SOME_UNION_DISJOINT);
    }
    default:
    {
      // SOME_FILTER: (bag.some p A)
      //   ---> (not (= (bag.filter p A) (as bag.empty (Bag Int))))
      Node filter = nm->mkNode(Kind::BAG_FILTER, n[0], n[1]);
      Node empty = nm->mkConst(EmptyBag(n[1].getType()));
      Node some = filter.eqNode(empty).notNode();
      return BagsRewriteResponse(some, Rewrite::SOME_FILTER);
    }
  }
}

BagsRewriteResponse BagsRewriter::postRewriteFold(const TNode& n) const
{
  Assert(n.getKind() == Kind::BAG_FOLD);
  Node f = n[0];
  Node t = n[1];
  Node bag = n[2];
  if (bag.isConst())
  {
    // FOLD_CONST, for f = (lambda ((y Int) (a Int)) (+ y a)):
    //   (bag.fold f 0 (bag.union_disjoint (bag 3 2) (bag 4 1))) ---> 10
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_CONST);
  }
  if (bag.getKind() == Kind::BAG_MAKE && bag[1].isConst()
      && bag[1].getConst<Rational>() > Rational(0))
  {
    // FOLD_BAG: (bag.fold f 0 (bag x 2)) ---> (+ x (+ x 0))
    Node value = BagsUtils::evaluateBagFold(n);
    return BagsRewriteResponse(value, Rewrite::FOLD_BAG);
  }
  {
    Node l = asLambda(f);
    if (l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 2)
    {
      if (bag.getType().getBagElementType().isTuple())
      {
        // NOT_NULL_COLUMNS, for column 1 of X NOT NULL:
        //   (bag.fold
        //     (lambda ((t (Tuple Int (Nullable Int))) (a Int))
        //       (ite (nullable.is_some ((_ tuple.select 1) t)) (+ a 1) a))
        //     0
        //     X)
        //   ---> (bag.fold
        //          (lambda ((t (Tuple Int (Nullable Int))) (a Int))
        //            (ite true (+ a 1) a))
        //          0
        //          X)
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
    // FOLD_TUPLE, see rewriteFoldOfTuple
    BagsRewriteResponse r = rewriteFoldOfTuple(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // FOLD_CONSTANT_STEP:
    //   (bag.fold (lambda ((y Int) (a Int)) 7) 0 A)
    //   ---> (ite (= A (as bag.empty (Bag Int))) 0 7)
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
    // FOLD_UNION_DISJOINT, A the smaller node:
    //   (bag.fold f 0 (bag.union_disjoint A B))
    //   ---> (bag.fold f (bag.fold f 0 A) B)
    Node A = bag[0] < bag[1] ? bag[0] : bag[1];
    Node B = bag[0] < bag[1] ? bag[1] : bag[0];
    Node foldA = d_nm->mkNode(Kind::BAG_FOLD, f, t, A);
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, f, foldA, B);
    return BagsRewriteResponse(fold, Rewrite::FOLD_UNION_DISJOINT);
  }
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE:
    //   (bag.fold f 0 A)
    //   ---> (bag.fold (lambda ((t_N Int) (acc_N Int)) (+ t_N acc_N)) 0 A)
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
    // PARTITION_CONST, for
    //   r = (lambda ((a Int) (b Int)) (= (mod a 2) (mod b 2))):
    //   (bag.partition r (bag.union_disjoint (bag 1 1) (bag 2 1)))
    //   ---> (bag.union_disjoint (bag (bag 1 1) 1) (bag (bag 2 1) 1))
    Node ret = BagsUtils::evaluateBagPartition(d_rewriter, n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::PARTITION_CONST);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteAggregate(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_AGGREGATE);

  {
    // NOT_NULL_COLUMNS, for column 1 of X NOT NULL:
    //   ((_ table.aggr 0)
    //     (lambda ((t (Tuple Int (Nullable Int))) (acc (Tuple Int Int)))
    //       (tuple ((_ tuple.select 0) t)
    //              (ite (nullable.is_some ((_ tuple.select 1) t))
    //                   (+ ((_ tuple.select 1) acc) 1)
    //                   ((_ tuple.select 1) acc))))
    //     (tuple 0 0)
    //     X)
    //   ---> the same with true for (nullable.is_some ((_ tuple.select 1) t))
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
    // AGGREGATE_NO_KEYS, for X : (Bag (Tuple Int Int)):
    //   (table.aggr f i X)
    //   ---> (bag (bag.fold f i X)
    //             (ite (= X (as bag.empty (Bag (Tuple Int Int)))) 0 1))
    // The nodes are created one per statement, in this order.
    Node fold = d_nm->mkNode(Kind::BAG_FOLD, n[0], n[1], n[2]);
    Node emptyTable = d_nm->mkConst(EmptyBag(n[2].getType()));
    Node isEmpty = n[2].eqNode(emptyTable);
    Node times = d_nm->mkNode(Kind::ITE, isEmpty, d_zero, d_one);
    Node ret = d_nm->mkNode(Kind::BAG_MAKE, fold, times);
    return BagsRewriteResponse(ret, Rewrite::AGGREGATE_NO_KEYS);
  }
  {
    // AGGREGATE_CONSTANT_COLUMNS, see rewriteAggregateConstantColumns
    BagsRewriteResponse r = rewriteAggregateConstantColumns(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  {
    // AGGREGATE_SORT_OUTPUT, see rewriteAggregateSortOutput
    BagsRewriteResponse r = rewriteAggregateSortOutput(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  if (n[0].getKind() == Kind::LAMBDA && n[0][0].getNumChildren() == 2)
  {
    // CANONICAL_VARIABLE:
    //   ((_ table.aggr 0)
    //     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
    //       (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
    //     (tuple 0 0)
    //     X)
    //   ---> the same with t and acc renamed to t_N and acc_N
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
    // AGGREGATE_MAP, see rewriteAggregateOfMap
    BagsRewriteResponse r = rewriteAggregateOfMap(n);
    if (r.d_node != n)
    {
      return r;
    }
  }
  // AGGREGATE_CONST, for
  //   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
  //         (tuple ((_ tuple.select 0) t)
  //                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))):
  //   ((_ table.aggr 0) f (tuple 0 0)
  //     (bag.union_disjoint (bag (tuple 1 2) 1) (bag (tuple 1 3) 1)))
  //   ---> (bag (tuple 1 5) 1)
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = BagsUtils::evaluateTableAggregate(n);
    if (ret != n)
    {
      return BagsRewriteResponse(ret, Rewrite::AGGREGATE_CONST);
    }
  }
  {
    // AGGREGATE_KEYED, see keyedAggregateRows
    Node rows = keyedAggregateRows(n);
    if (!rows.isNull())
    {
      return BagsRewriteResponse(rows, Rewrite::AGGREGATE_KEYED);
    }
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

BagsRewriteResponse BagsRewriter::postRewriteProduct(const TNode& n) const
{
  Assert(n.getKind() == Kind::TABLE_PRODUCT);
  TypeNode tableType = n.getType();
  Node empty = d_nm->mkConst(EmptyBag(tableType));
  if (n[0].getKind() == Kind::BAG_EMPTY || n[1].getKind() == Kind::BAG_EMPTY)
  {
    // PRODUCT_EMPTY, for X : (Bag (Tuple Int)):
    //   (table.product X (as bag.empty (Bag (Tuple Int))))
    //   ---> (as bag.empty (Bag (Tuple Int Int)))
    return BagsRewriteResponse(empty, Rewrite::PRODUCT_EMPTY);
  }

  return BagsRewriteResponse(n, Rewrite::NONE);
}

// (Tuple Int Int) ---> row_N, for N the id of
// (as bag.empty (Bag (Tuple Int Int))), the same variable at every call
Node BagsRewriter::rowVariable(TypeNode tupleType) const
{
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(tupleType)));
  return mkRewriterVar(
      d_nm, "row", key, "row_" + std::to_string(key.getId()), tupleType);
}

// For t : (Tuple Int Int), true for
//   (>= (bag.count ((_ tuple.project 0) t)
//                  (bag.map (lambda ((t (Tuple Int Int)))
//                             ((_ tuple.project 1) t))
//                           X))
//       1)
// and false for (> ((_ tuple.select 0) t) 3). Callers test it before they
// substitute for var: Node::substitute is syntactic.
bool BagsRewriter::bindsVariable(const Node& body, const Node& var) const
{
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

// For t : (Tuple Int Int), true for ((_ tuple.select 0) t) and false for
//   (bag.map (lambda ((t (Tuple Int Int))) ((_ tuple.select 0) t)) X)
bool BagsRewriter::occursFree(const Node& n, const Node& v) const
{
  if (!expr::hasSubterm(n, v))
  {
    return false;
  }
  std::unordered_set<Node> fvs;
  expr::getFreeVariables(n, fvs);
  return fvs.find(v) != fvs.end();
}

// the function array constant of (lambda ((t (Tuple Int Int))) true)
// ---> (lambda ((t (Tuple Int Int))) true); any other f ---> f
Node BagsRewriter::asLambda(const Node& f) const
{
  if (f.getKind() == Kind::FUNCTION_ARRAY_CONST)
  {
    Node lambda = uf::FunctionConst::toLambda(f);
    if (!lambda.isNull())
    {
      return lambda;
    }
  }
  return f;
}

// For fn = (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 1) s) 3)),
//   (tuple a b) ---> (> ((_ tuple.select 1) (tuple a b)) 3)
// For a declared fn ---> (fn x); on a capture ---> null.
Node BagsRewriter::applyFunction(const Node& fn, const Node& x) const
{
  Node f = asLambda(fn);
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    TNode var = f[0][0];
    if (var == x)
    {
      return f[1];
    }
    if (bindsVariable(f[1], var) || bindsVariable(x, var))
    {
      // substitute is syntactic: an inner binder of var would be replaced
      // too (also refused when x binds var, stricter than needed)
      return Node::null();
    }
    // a binder in f's body of a free variable of x would capture it
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
  return d_nm->mkNode(Kind::APPLY_UF, fn, x);
}

// (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t)))
// ---> (t, (tuple ((_ tuple.select 1) t)))
// h : (-> (Tuple Int Int) (Tuple Int)) ---> (row_N, (h row_N)), also for a
// function array constant, which is not read through asLambda
std::pair<Node, Node> BagsRewriter::lambdaOf(const Node& f) const
{
  if (f.getKind() == Kind::LAMBDA && f[0].getNumChildren() == 1)
  {
    return std::make_pair(f[0][0], f[1]);
  }
  TypeNode domain = f.getType().getArgTypes()[0];
  Node t = rowVariable(domain);
  return std::make_pair(t, d_nm->mkNode(Kind::APPLY_UF, f, t));
}

// For t : (Tuple Int Int Int),
//   (> ((_ tuple.select 0) t) ((_ tuple.select 2) t)) ---> true, adds {0, 2}
//   (= t (tuple a b c)) ---> false
// and for t : (Nullable Int), (nullable.val t) ---> false. Binders are not
// looked at (callers test bindsVariable).
bool BagsRewriter::readPositions(const Node& body,
                                 const Node& var,
                                 std::set<uint32_t>& positions) const
{
  bool tuple = var.getType().isTuple();
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
      // t itself: the whole row
      return false;
    }
    if (tuple && cur.getKind() == Kind::APPLY_SELECTOR && cur[0] == var)
    {
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

// true for (lambda ((t (Tuple Int Int))) (tuple ((_ tuple.select 1) t))),
// false for a declared h : (-> (Tuple Int Int) (Tuple Int)): composing h
// would build (lambda ((t (Tuple Int Int))) (h t)), a lambda the input did
// not have.
bool BagsRewriter::composable(const Node& f) const
{
  Node l = asLambda(f);
  return l.getKind() == Kind::LAMBDA && l[0].getNumChildren() == 1;
}

// (t, (> ((_ tuple.select 0) t) 3))
// ---> (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
Node BagsRewriter::mkLambda(const Node& var, const Node& body) const
{
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, var), body);
}

// FILTER_MAP, for p = (lambda ((y Int)) (> y 0)) and
// f = (lambda ((z Int)) (+ z 1)):
//   (bag.filter p (bag.map f A))
//   ---> (bag.map f (bag.filter (lambda ((z Int)) (> (+ z 1) 0)) A))
BagsRewriteResponse BagsRewriter::rewriteFilterOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // it builds a lambda (see the constructor)
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node p = n[0];
  Node f = n[1][0];
  Node A = n[1][1];
  if (!composable(p) || !composable(f))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t = z, lf.second = (+ z 1)
  std::pair<Node, Node> lf = lambdaOf(f);
  Node t = lf.first;
  // (> (+ z 1) 0), or null on a capture
  Node body = applyFunction(p, lf.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node filtered = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(t, body), A);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, f, filtered);
  return BagsRewriteResponse(ret, Rewrite::FILTER_MAP);
}

// MAP_MAP, for f = (lambda ((z Int)) (* z 2)) and
// g = (lambda ((y Int)) (+ y 1)):
//   (bag.map f (bag.map g A))
//   ---> (bag.map (lambda ((y Int)) (* (+ y 1) 2)) A)
BagsRewriteResponse BagsRewriter::rewriteMapOfMap(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // it builds a lambda (see the constructor)
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node f = n[0];
  Node g = n[1][0];
  Node A = n[1][1];
  if (!composable(f) || !composable(g))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // t = y, lg.second = (+ y 1)
  std::pair<Node, Node> lg = lambdaOf(g);
  Node t = lg.first;
  // (* (+ y 1) 2), or null on a capture
  Node body = applyFunction(f, lg.second);
  if (body.isNull())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, body), A);
  return BagsRewriteResponse(ret, Rewrite::MAP_MAP);
}

// PROJECT_TO_MAP, for X : (Bag (Tuple Int Int)) and its row variable row_N:
//   ((_ table.project 1 0) X)
//   ---> (bag.map
//          (lambda ((row_N (Tuple Int Int))) ((_ tuple.project 1 0) row_N))
//          X)
BagsRewriteResponse BagsRewriter::postRewriteProject(const TNode& n) const
{
  if (!d_higherOrder)
  {
    // it builds a lambda (see the constructor)
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Assert(n.getKind() == Kind::TABLE_PROJECT);
  Node A = n[0];
  TypeNode elementType = A.getType().getBagElementType();
  ProjectOp projectOp = n.getOperator().getConst<ProjectOp>();
  Node op = d_nm->mkConst(Kind::TUPLE_PROJECT_OP, projectOp);
  // ((_ tuple.project 1 0) row_N)
  Node t = rowVariable(elementType);
  Node projection = d_nm->mkNode(Kind::TUPLE_PROJECT, op, t);
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(t, projection), A);
  return BagsRewriteResponse(ret, Rewrite::PROJECT_TO_MAP);
}

// For f's body over t : (Tuple Int Int Int):
//   (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)) ---> 2 0
//   ((_ tuple.project 2 0) t) ---> 2 0
//   (tuple ((_ tuple.select 1) t) ((_ tuple.select 1) t)) ---> 1 1
//   (tuple ((_ tuple.select 0) t) 7) ---> empty
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
    return body.getOperator().getConst<ProjectOp>().getIndices();
  }
  // a row x that is not a tuple has no columns
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple()
      || !x.getType().isTuple())
  {
    return out;
  }
  for (const Node& c : body)
  {
    // (+ ((_ tuple.select 0) x) 1) or 7 as a component ---> empty
    if (c.getKind() != Kind::APPLY_SELECTOR || c[0] != x)
    {
      return std::vector<uint32_t>();
    }
    out.push_back(datatypes::utils::indexOf(c.getOperator()));
  }
  return out;
}

// AGGREGATE_MAP, for
//   f = (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//         (tuple ((_ tuple.select 0) t)
//                (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t)))):
//   ((_ table.aggr 0)
//     f
//     (tuple 0 0)
//     (bag.map
//       (lambda ((t (Tuple Int Int)))
//         (tuple ((_ tuple.select 1) t) ((_ tuple.select 0) t)))
//       X))
//   ---> ((_ table.aggr 1)
//          (lambda ((x (Tuple Int Int)) (acc (Tuple Int Int)))
//            (tuple ((_ tuple.select 1) x)
//                   (+ ((_ tuple.select 1) acc) ((_ tuple.select 0) x))))
//          (tuple 0 0)
//          X)
BagsRewriteResponse BagsRewriter::rewriteAggregateOfMap(const TNode& n) const
{
  // No higher-order test: the new lambda replaces f, a lambda already.
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
  // Each group column k of the map, by g's term ck:
  //   ((_ tuple.select 2) gv) ---> 2 goes to JK
  //   (+ ((_ tuple.select 0) gv) 42) ---> computed
  //   7 ---> dropped: it splits no group
  Node gv = g[0][0];
  std::vector<uint32_t> K = n.getOperator().getConst<ProjectOp>().getIndices();
  std::vector<uint32_t> JK;
  std::vector<Node> computed;
  for (uint32_t k : K)
  {
    if (k >= g[1].getNumChildren())
    {
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
    // (+ ((_ tuple.select 0) gv) 42) needs 0 in JK, as deptno + 42 beside
    // deptno
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
  // 2 0 2 ---> 0 2
  std::sort(JK.begin(), JK.end());
  JK.erase(std::unique(JK.begin(), JK.end()), JK.end());
  TypeNode rowType = X.getType().getBagElementType();
  if (!rowType.isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // The map and X are two bags, which cvc5 may fold in different orders: the
  // step must give one value in any order.
  std::set<uint32_t> same(K.begin(), K.end());
  if (!orderIndependentStep(f, same, nonNullColumns(n[2])))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // the new step: (lambda ((x R) (acc A)) f's body[t := (g x)]), x = row_N
  Node x = rowVariable(rowType);
  Node y = f[0][1];
  Node gx = applyFunction(n[2][0], x);
  // give up on a capture: gx null, x bound in f's body, or x = acc
  if (gx.isNull() || bindsVariable(f[1], x) || x == y)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node body = f[1].substitute(TNode(f[0][0]), TNode(gx));
  Node lambda = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, y), body);
  Node op = d_nm->mkConst(Kind::TABLE_AGGREGATE_OP, ProjectOp(JK));
  std::vector<Node> children{op, lambda, i, X};
  Node ret = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_MAP);
}

bool BagsRewriter::orderIndependentStep(const Node& f,
                                        const std::set<uint32_t>& same,
                                        const std::set<uint32_t>& nonNull) const
{
  // (tuple e0 .. em): each ei on its own, with ((_ tuple.select i) acc)
  Node l = asLambda(f);
  if (l.getKind() != Kind::LAMBDA || l[0].getNumChildren() != 2)
  {
    return false;
  }
  Node x = l[0][0];
  Node acc = l[0][1];
  // free((+ ((_ tuple.select 1) x) 1)) = true
  auto free = [&](const Node& e) { return !occursFree(e, acc); };
  // valueOf((nullable.some v)) = v, valueOf(t) = (nullable.val t)
  auto valueOf = [&](const Node& t) {
    if (t.getKind() == Kind::APPLY_CONSTRUCTOR && t.getNumChildren() == 1)
    {
      return t[0];
    }
    const DType& dt = t.getType().getDType();
    size_t si = dt[0].getNumArgs() == 1 ? 0 : 1;
    return d_nm->mkNode(Kind::APPLY_SELECTOR, dt[si][0].getSelector(), t);
  };
  // compares((< a b), a, b) = true, also for <=, >, >=, str.<, str.<=,
  // either way round, up to rewriting; false without a rewriter
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
  // combines(c, a, b) = true for c
  //   (nullable.some (+ (nullable.val a) (nullable.val b)))
  //   (ite (< (nullable.val a) (nullable.val b)) a b)
  //   (ite (< (nullable.val a) (nullable.val b)) b a)
  auto combines = [&](const Node& c, const Node& a, const Node& b) {
    if (c.getKind() == Kind::APPLY_CONSTRUCTOR && c.getNumChildren() == 1)
    {
      Node sum = d_nm->mkNode(Kind::ADD, {valueOf(a), valueOf(b)});
      TypeNode t = c[0].getType();
      if (d_rewriter == nullptr || t != sum.getType())
      {
        return false;
      }
      Node r = d_rewriter->rewrite(c[0].eqNode(sum));
      return r.isConst() && r.getConst<bool>();
    }
    if (c.getKind() != Kind::ITE
        || !((c[1] == a && c[2] == b) || (c[1] == b && c[2] == a)))
    {
      return false;
    }
    Node va = valueOf(a);
    Node vb = valueOf(b);
    return compares(c[0], va, vb);
  };
  // nullTested((= (as nullable.null (Nullable Int)) t)) = t, also either way
  // round; null for any other c
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
  // sumOf((+ own ((_ tuple.select 1) x) 1), own) = true: own exactly once
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
  // column(e, own): whether e, the new value of own, a component
  // ((_ tuple.select q) acc) or acc, gives one value in any order. Below, v
  // and a read no accumulator.
  std::function<bool(const Node&, const Node&)> column;
  column = [&](const Node& e, const Node& own) {
    if (free(e))
    {
      // for same = {0}: 7 and ((_ tuple.select 0) x) ---> true, and
      // ((_ tuple.select 1) x), the last row's, ---> false
      std::set<uint32_t> read;
      return !occursFree(e, x)
             || (readPositions(e, x, read)
                 && std::includes(
                     same.begin(), same.end(), read.begin(), read.end()));
    }
    if (e == own)
    {
      // own ---> true
      return true;
    }
    {
      // for own = ((_ tuple.select 1) acc):
      //   (+ own ((_ tuple.select 0) acc)) ---> false
      Node mark = NodeManager::mkBoundVar("own", own.getType());
      if (occursFree(e.substitute(TNode(own), TNode(mark)), acc))
      {
        return false;
      }
    }
    // (+ own 1), (nullable.some (+ (nullable.val own) v)) ---> true
    TypeNode ownType = own.getType();
    bool nullable = ownType.isNullable();
    if (sumOf(e, own)
        || (nullable && e.getKind() == Kind::APPLY_CONSTRUCTOR
            && e.getNumChildren() == 1 && sumOf(e[0], valueOf(own))))
    {
      return true;
    }
    if (e.getKind() != Kind::ITE)
    {
      return false;
    }
    if (free(e[0]))
    {
      // SQL's SUM, MIN or MAX of a nullable a ---> true:
      //   (ite (= (as nullable.null (Nullable Int)) a)
      //        own
      //        (ite (= (as nullable.null (Nullable Int)) own) a C))
      // for C the sum, minimum or maximum of a and own (see combines)
      Node a = nullTested(e[0]);
      if (nullable && !a.isNull() && e[1] == own && free(a)
          && a.getType() == ownType && e[2].getKind() == Kind::ITE
          && nullTested(e[2][0]) == own && e[2][1] == a
          && combines(e[2][2], a, own))
      {
        return true;
      }
      // (ite c own u) and (ite c u own) ---> column(u, own), as SQL's COUNT of
      // a nullable column 1:
      //   (ite (= (as nullable.null (Nullable Int)) ((_ tuple.select 1) x))
      //        own
      //        (+ own 1))
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
    // MAX and MIN: (ite (> v own) v own), (ite (< own v) own v) ---> true
    for (size_t s = 1; s < 3; s++)
    {
      if (e[3 - s] == own && free(e[s]) && compares(e[0], e[s], own))
      {
        return true;
      }
    }
    // SQL's SUM, MIN or MAX of an a that is never null (nonNullTerm), whose
    // null test was decided and removed:
    //   (ite (= (as nullable.null (Nullable Int)) own) a C)
    // With a nullable a, this could depend on the order.
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
    // (tuple e0 .. em): each ei with ((_ tuple.select i) acc) as own
    for (size_t q = 0, w = body.getNumChildren(); q < w; q++)
    {
      if (!column(body[q], datatypes::TupleUtils::nthElementOfTuple(acc, q)))
      {
        return false;
      }
    }
    return true;
  }
  // any other body: one column, own = acc
  return column(body, acc);
}

// For X : (Bag (Tuple Int Int)) with the key {0},
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
//       (tuple ((_ tuple.select 0) t) (+ ((_ tuple.select 1) acc) 1)))
//     (tuple 0 0)
//     X)
//   ---> (bag.map (lambda ((t (Tuple Int Int)))
//                   (tuple ((_ tuple.select 0) t)
//                          (+ ((_ tuple.select 1) (tuple 0 0)) 1)))
//                 X)
// and null when K holds no key of X.
Node BagsRewriter::keyedAggregateRows(const Node& A) const
{
  const std::vector<uint32_t>& K =
      A.getOperator().getConst<ProjectOp>().getIndices();
  Node f = asLambda(A[0]);
  // for an empty K, see AGGREGATE_NO_KEYS
  if (K.empty() || f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2)
  {
    return Node::null();
  }
  // the key {0} inside K = 0: keyed
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
  // f's body with acc := i: (+ ((_ tuple.select 1) (tuple 0 0)) 1)
  Node body = f[1].substitute(TNode(f[0][1]), TNode(A[1]));
  return d_nm->mkNode(Kind::BAG_MAP, mkLambda(f[0][0], body), A[2]);
}

// (Tuple Int Int) ---> accrow_N, for N the id of
// (as bag.empty (Bag (Tuple Int Int))); not row_N, so a lambda binds both
Node BagsRewriter::accumulatorVariable(TypeNode type) const
{
  Node key = d_nm->mkConst(EmptyBag(d_nm->mkBagType(type)));
  return mkRewriterVar(
      d_nm, "accumulator", key, "accrow_" + std::to_string(key.getId()), type);
}

// The keys of
//   (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
//   (lambda ((t (Tuple Int Int))) (> ((_ tuple.select 0) t) 3))
// are one node, (lambda ((b0 (Tuple Int Int))) (> ((_ tuple.select 0) b0) 3))
// with the atom in the arithmetic rewriter's form, b0 the placeholder of
// depth 0. A free r becomes the placeholder of its sort, so the key of
//   (lambda ((t (Tuple Int Int)))
//     (= ((_ tuple.select 0) t) ((_ tuple.select 0) r)))
// does not depend on the name of r. Cached in d_alphaKeys.
Node BagsRewriter::alphaKey(const Node& f) const
{
  std::unordered_map<Node, Node>::iterator it = d_alphaKeys.find(f);
  if (it != d_alphaKeys.end())
  {
    return it->second;
  }
  std::unordered_map<TNode, Node> bound;
  Node key = alphaKeyScope(f, bound, 0);
  d_alphaKeys[f] = key;
  return key;
}

// For
//   (lambda ((s (Tuple Int Int)))
//     (bag.map (lambda ((u (Tuple Int Int)))
//                (tuple ((_ tuple.select 0) s) ((_ tuple.select 1) u)))
//              Y))
// ---> the same lambda with b0 for s and b1 for u, bk the placeholder of
// depth k. The inner lambda alone ---> b0 for u, and for s, free there, the
// placeholder of (Tuple Int Int). Y stays.
Node BagsRewriter::alphaKeyScope(TNode root,
                                 std::unordered_map<TNode, Node>& bound,
                                 size_t depth) const
{
  std::unordered_map<TNode, Node> cache;
  std::vector<TNode> todo{root};
  while (!todo.empty())
  {
    TNode n = todo.back();
    if (cache.count(n))
    {
      todo.pop_back();
      continue;
    }
    // s bound around n ---> its placeholder; r free ---> the placeholder of
    // its sort
    if (n.getKind() == Kind::BOUND_VARIABLE)
    {
      std::unordered_map<TNode, Node>::iterator b = bound.find(n);
      if (b != bound.end())
      {
        cache[n] = b->second;
      }
      else
      {
        Node zero = d_nm->mkConstInt(Rational(0));
        cache[n] = mkRewriterVar(d_nm, "alpha-free", zero, n.getType());
      }
      todo.pop_back();
      continue;
    }
    // a constant, or a table such as Y ---> itself
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
    if (n.isClosure())
    {
      // (lambda ((s ..) (acc ..)) e) at depth d
      // ---> (lambda ((b_d ..) (b_d+1 ..)) e'), e' converted at depth d + 2
      todo.pop_back();
      size_t nvars = n[0].getNumChildren();
      std::vector<Node> vars;
      std::vector<std::pair<TNode, Node>> saved;
      for (size_t i = 0; i < nvars; i++)
      {
        TNode v = n[0][i];
        Node index = d_nm->mkConstInt(Rational(depth + i));
        Node p = mkRewriterVar(d_nm, "alpha-bound", index, v.getType());
        // an outer binder of v, shadowed here: restored after the body
        std::unordered_map<TNode, Node>::iterator b = bound.find(v);
        saved.push_back({v, b != bound.end() ? b->second : Node::null()});
        bound[v] = p;
        vars.push_back(p);
      }
      std::vector<Node> children;
      if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(n.getOperator());
      }
      children.push_back(d_nm->mkNode(Kind::BOUND_VAR_LIST, vars));
      for (size_t i = 1, nc = n.getNumChildren(); i < nc; i++)
      {
        children.push_back(alphaKeyScope(n[i], bound, depth + nvars));
      }
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
    // the operator too: (lambda ((f (-> Int Int))) (f 0)) ---> (b0 0) as body
    bool parameterized = n.getMetaKind() == kind::metakind::PARAMETERIZED;
    Node op = parameterized ? n.getOperator() : Node::null();
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
    // changed counts the operator: keeping (f 0) would leave f's name in the
    // key, and canonicalLambda would never reach a fixed point
    std::vector<Node> children;
    bool changed = false;
    if (parameterized)
    {
      children.push_back(cache[op]);
      changed = cache[op] != op;
    }
    size_t first = children.size();
    for (const Node& c : n)
    {
      Node cc = cache[c];
      changed = changed || cc != c;
      children.push_back(cc);
    }
    switch (n.getKind())
    {
      // (+ s 1) and (+ 1 s) ---> one key: renaming changes node ids, hence
      // the rewriter's order of the arguments
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
      // for integers a and b, (>= (- a b) 0) and (not (>= (- b a) 1)) ---> one
      // key: the arithmetic rewriter orients atoms by node id, which renaming
      // changes. Also (not (not c)), left by rewriting an atom.
      built = d_rewriter->rewrite(built);
    }
    if (k == Kind::ITE && built.getKind() == Kind::ITE
        && built[0].getKind() == Kind::NOT)
    {
      // (ite (not c) a b) ---> (ite c b a), as the Boolean rewriter writes it
      built = d_nm->mkNode(Kind::ITE, built[0][0], built[2], built[1]);
    }
    cache[n] = built;
  }
  return cache[root];
}

// For t : (Tuple Int Int), at any depth,
//   (ite (= ((_ tuple.select 0) t) ((_ tuple.select 1) t))
//        ((_ tuple.select 1) t)
//        ((_ tuple.select 0) t))
//   ---> ((_ tuple.select 0) t)
// sqleq's null-aware MIN and MAX steps leave such ites.
Node BagsRewriter::simplifyIteSame(const Node& body) const
{
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
    if (n.getNumChildren() == 0)
    {
      cache[n] = n;
      todo.pop_back();
      continue;
    }
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
    // (ite (= a b) b a) ---> a, (ite (= a b) a b) ---> b
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

// CANONICAL_VARIABLE, for N the id of f's alpha key:
//   (lambda ((s (Tuple Int Int))) (> ((_ tuple.select 0) s) 3))
//   ---> (lambda ((t_N (Tuple Int Int))) (> ((_ tuple.select 0) t_N) 3))
//   (lambda ((s Int) (b Int)) (+ s b))
//   ---> (lambda ((t_N Int) (acc_N Int)) (+ t_N acc_N))
// Nested lambdas have different keys, so canonical names never shadow.
Node BagsRewriter::canonicalLambda(const Node& f) const
{
  Assert(f.getKind() == Kind::LAMBDA);
  {
    // (ite (= a b) b a) in the body ---> a, first (see simplifyIteSame)
    Node simpler = simplifyIteSame(f[1]);
    if (simpler != f[1])
    {
      return canonicalLambda(d_nm->mkNode(Kind::LAMBDA, f[0], simpler));
    }
  }
  size_t arity = f[0].getNumChildren();
  std::vector<Node> vars(f[0].begin(), f[0].end());
  Node key = alphaKey(f);
  // one variable per (key, k, sort): lambdas with one key get the same ones
  std::vector<Node> canonical;
  for (size_t k = 0; k < arity; k++)
  {
    Node cache = d_nm->mkNode(Kind::SEXPR, key, d_nm->mkConstInt(Rational(k)));
    // N in the name: a printed problem binds by name, and a lambda and a
    // variable free in it with one name would capture it
    std::string name = (k == 0 ? "t_" : "acc_") + std::to_string(key.getId());
    canonical.push_back(
        mkRewriterVar(d_nm, "canonical", cache, name, vars[k].getType()));
  }
  // the fixed point: the renamed lambda, rewritten, has the same key
  if (canonical == vars)
  {
    return f;
  }
  // a canonical variable already in the body: renaming would capture it
  Node body = f[1];
  for (size_t k = 0; k < arity; k++)
  {
    if (canonical[k] != vars[k] && expr::hasSubterm(body, canonical[k]))
    {
      return f;
    }
  }
  Node newBody = body.substitute(
      vars.begin(), vars.end(), canonical.begin(), canonical.end());
  return d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, canonical), newBody);
}

// AGGREGATE_SORT_OUTPUT, for X : (Bag (Tuple Int Int)):
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
//            (tuple 0 0) X))
// The copies of group columns come first, by column; the others by what they
// compute, or in their order when one reads another's accumulator.
BagsRewriteResponse BagsRewriter::rewriteAggregateSortOutput(
    const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
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
  Node x = f[0][0];
  Node y = f[0][1];
  size_t m = f[1].getNumChildren();
  // sort keys: ((_ tuple.select 0) x), group column 0 ---> (0, 0); another
  // column q ---> (1, an id of what it computes) when every e_q reads only
  // its own ((_ tuple.select q) y), else (1, q)
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
      order.push_back({{0, datatypes::utils::indexOf(c.getOperator())}, q});
    }
    else if (independent)
    {
      // the alpha key of (lambda ((x R) (v S)) e_q[((_ tuple.select q) y) :=
      // v]) with i_q: the same for the same column of any aggregate
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
      order.push_back({{1, q}, q});
    }
  }
  // stable: two copies of one group column keep their order
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
    // sorted already, as the rule's own result
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<uint32_t> inverse(m);  // old position -> new position
  for (uint32_t q = 0; q < m; q++)
  {
    inverse[sigma[q]] = q;
  }
  TypeNode oldType = f[1].getType();
  std::vector<TypeNode> types;
  for (uint32_t q = 0; q < m; q++)
  {
    types.push_back(oldType.getTupleTypes()[sigma[q]]);
  }
  TypeNode newType = d_nm->mkTupleType(types);
  // acc = accrow_N; give up when it is x or occurs in the body but as y
  Node acc = accumulatorVariable(newType);
  if (acc == x || (acc != y && expr::hasSubterm(f[1], acc)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // y := (tuple ((_ tuple.select 1) acc) ((_ tuple.select 0) acc)) in the
  // example
  std::vector<Node> oldAcc;
  for (uint32_t p = 0; p < m; p++)
  {
    oldAcc.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, inverse[p]));
  }
  Node unsortedAcc = datatypes::TupleUtils::constructTupleFromElements(
      oldType, oldAcc, 0, m - 1);
  Node body = f[1].substitute(TNode(y), TNode(unsortedAcc));
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
  std::vector<Node> children{n.getOperator(), lambda, newI, X};
  Node sortedAggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  // (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)) in the example, a
  // bijection, so the map keeps every multiplicity
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

// FOLD_TUPLE, for X : (Bag (Tuple Int)):
//   (bag.fold (lambda ((t (Tuple Int)) (acc (Tuple Int Int)))
//               (tuple (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t))
//                      (+ ((_ tuple.select 1) acc) 1)))
//             (tuple 0 0) X)
//   ---> (tuple (bag.fold (lambda ((t (Tuple Int)) (a Int))
//                           (+ a ((_ tuple.select 0) t)))
//                         0 X)
//               (bag.fold (lambda ((t (Tuple Int)) (a Int)) (+ a 1)) 0 X))
BagsRewriteResponse BagsRewriter::rewriteFoldOfTuple(const TNode& n) const
{
  Node f = n[0];
  Node i = n[1];
  Node X = n[2];
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
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  std::vector<Node> components;
  for (size_t k = 0; k < m; k++)
  {
    // e_0 = (+ ((_ tuple.select 0) acc) ((_ tuple.select 0) t)) reads acc only
    // through its own component, with no inner binder of acc
    std::set<uint32_t> positions;
    if (!readPositions(body[k], acc, positions) || bindsVariable(body[k], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // e_1 reading ((_ tuple.select 0) acc) ---> no rule
    for (uint32_t pos : positions)
    {
      if (pos != k)
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
    // a = accrow_N; give up when it is x or occurs in e_k
    TypeNode type = body[k].getType();
    Node a = accumulatorVariable(type);
    if (a == x || expr::hasSubterm(body[k], a))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // e_1 = (+ ((_ tuple.select 1) acc) 1) ---> (+ a 1)
    Node selected = datatypes::TupleUtils::nthElementOfTuple(acc, k);
    Node step = body[k].substitute(TNode(selected), TNode(a));
    if (expr::hasSubterm(step, acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    // (bag.fold (lambda ((t (Tuple Int)) (a Int)) (+ a 1)) 0 X)
    Node lambda = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, a), step);
    Node seed = datatypes::TupleUtils::nthElementOfTuple(i, k);
    components.push_back(d_nm->mkNode(Kind::BAG_FOLD, lambda, seed, X));
  }
  Node ret = datatypes::TupleUtils::constructTupleFromElements(
      n.getType(), components, 0, m - 1);
  return BagsRewriteResponse(ret, Rewrite::FOLD_TUPLE);
}

// SETOF_PROJECTION_SORT, for Y : (Bag (Tuple Int Int Int)):
//   (bag.setof
//     (bag.map (lambda ((t (Tuple Int Int Int)))
//                (tuple ((_ tuple.select 2) t) ((_ tuple.select 0) t)))
//              Y))
//   ---> (bag.map (lambda ((r (Tuple Int Int)))
//                   (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
//          (bag.setof
//            (bag.map (lambda ((t (Tuple Int Int Int)))
//                       (tuple ((_ tuple.select 0) t) ((_ tuple.select 2) t)))
//                     Y)))
// The outer map is injective, so it commutes with bag.setof.
BagsRewriteResponse BagsRewriter::rewriteSetofOfMap(const TNode& n) const
{
  Node f = asLambda(n[0][0]);
  Node Y = n[0][1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 1)
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node var = f[0][0];
  Node body = f[1];
  if (body.getKind() != Kind::APPLY_CONSTRUCTOR || !body.getType().isTuple())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  {
    // J = 2 0 in the example; empty when f is no projection
    std::vector<uint32_t> J = projectionIndices(f);
    if (!J.empty())
    {
      // 2 0 ---> 0 2, and 1 1 ---> 1
      std::vector<uint32_t> sorted = J;
      std::sort(sorted.begin(), sorted.end());
      sorted.erase(std::unique(sorted.begin(), sorted.end()), sorted.end());
      if (sorted != J)
      {
        // g: the projection onto 0 2 in the example
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
        // unsort, in the example:
        //   (lambda ((r (Tuple Int Int)))
        //     (tuple ((_ tuple.select 1) r) ((_ tuple.select 0) r)))
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

// For c, b : Bool,
//   (ite c (nullable.some b) (as nullable.null (Nullable Bool)))
//   ---> (ite c b false)
// nested ites likewise; a variable of sort (Nullable Bool) ---> null.
Node BagsRewriter::truthOf(const Node& X) const
{
  if (X.getKind() == Kind::APPLY_CONSTRUCTOR)
  {
    // (nullable.some b) ---> b, (as nullable.null (Nullable Bool)) ---> false
    return X.getNumChildren() == 1 ? X[0] : d_nm->mkConst(false);
  }
  if (X.getKind() == Kind::ITE)
  {
    Node a = truthOf(X[1]);
    Node b = truthOf(X[2]);
    if (a.isNull() || b.isNull())
    {
      return Node::null();
    }
    return d_nm->mkNode(Kind::ITE, X[0], a, b);
  }
  return Node::null();
}

// FILTER_NULLABLE_TRUTH, for t : (Tuple Int (Nullable Int)) and
//   X = (ite (nullable.is_some ((_ tuple.select 1) t))
//            (nullable.some (> (nullable.val ((_ tuple.select 1) t)) 3))
//            (as nullable.null (Nullable Bool))),
//   (and (nullable.is_some X) (nullable.val X) (> ((_ tuple.select 0) t) 0))
//   ---> (and (ite (nullable.is_some ((_ tuple.select 1) t))
//                  (> (nullable.val ((_ tuple.select 1) t)) 3)
//                  false)
//             (> ((_ tuple.select 0) t) 0))
Node BagsRewriter::normalizeTruth(const Node& body) const
{
  std::vector<Node> conjuncts;
  if (body.getKind() == Kind::AND)
  {
    conjuncts.insert(conjuncts.end(), body.begin(), body.end());
  }
  else
  {
    conjuncts.push_back(body);
  }
  // vals = {X} for the conjunct (nullable.val X)
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
  std::vector<Node> out;
  bool changed = false;
  std::set<Node> done;
  for (const Node& c : conjuncts)
  {
    // X for c = (nullable.val X) or c = (nullable.is_some X)
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
        // only with (nullable.is_some X) present: a lone (nullable.val X) is
        // unspecified for a null X, so it is not t
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
    out.push_back(c);
  }
  if (!changed)
  {
    return body;
  }
  return out.size() == 1 ? out[0] : d_nm->mkNode(Kind::AND, out);
}

// AGGREGATE_DEAD_COLUMNS, for X : (Bag (Tuple Int Int)) and
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
//            (tuple 0 0) X))
// The sum, column 1, is dead: neither the map nor a filter in between reads
// it, nor does the step of another column.
BagsRewriteResponse BagsRewriter::rewriteAggregateDeadColumns(
    const TNode& n) const
{
  // n = (bag.map h A) or (bag.map h (bag.filter P A))
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
  // read = {0, 2} in the example: the columns that h and P read
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
  // reads[1] = {1} and reads[2] = {2} in the example
  std::vector<std::set<uint32_t>> reads(m);
  for (size_t q = 0; q < m; q++)
  {
    if (!readPositions(f[1][q], acc, reads[q]) || bindsVariable(f[1][q], acc))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
  }
  // column 1 is dead in the example: not read, e_1 reads only acc's column
  // 1, and no other e_o reads it
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
  // columns 0 2 ---> 0 1, of sort (Tuple Int Int), in the example
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
    // every column dead: no aggregate of empty rows
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // acc2 = accrow_N and r2 = row_N of newType; give up when they occur
  // already
  TypeNode newType = d_nm->mkTupleType(types);
  Node acc2 = accumulatorVariable(newType);
  Node r2 = rowVariable(newType);
  if (acc2 == x || expr::hasSubterm(f[1], acc2) || expr::hasSubterm(h[1], r2)
      || (!P.isNull() && expr::hasSubterm(P[1], r2)))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  // reindex(e_2, acc, acc2) = (+ ((_ tuple.select 1) acc2) 1) in the example
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
  Node f2 = d_nm->mkNode(
      Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, x, acc2), body);
  Node i2 = datatypes::TupleUtils::constructTupleFromElements(
      newType, init, 0, init.size() - 1);
  std::vector<Node> children{Y.getOperator(), f2, i2, X};
  Node aggr = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  Node h2body = reindex(h[1], h[0][0], r2);
  if (occursFree(h2body, h[0][0]))
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node below = aggr;
  if (!P.isNull())
  {
    Node p2body = reindex(P[1], P[0][0], r2);
    if (occursFree(p2body, P[0][0]))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    below = d_nm->mkNode(Kind::BAG_FILTER, mkLambda(r2, p2body), aggr);
  }
  Node ret = d_nm->mkNode(Kind::BAG_MAP, mkLambda(r2, h2body), below);
  return BagsRewriteResponse(ret, Rewrite::AGGREGATE_DEAD_COLUMNS);
}

// For t : (Tuple Int Int),
//   (lambda ((t (Tuple Int Int)))
//     (and (= ((_ tuple.select 1) t) 5) (> ((_ tuple.select 0) t) 3)))
//   ---> {1 -> 5}
std::map<uint32_t, Node> BagsRewriter::fixedColumns(const Node& p) const
{
  std::map<uint32_t, Node> fixed;
  Node lambda = asLambda(p);
  if (lambda.getKind() != Kind::LAMBDA || lambda[0].getNumChildren() != 1)
  {
    return fixed;
  }
  Node t = lambda[0][0];
  if (!t.getType().isTuple())
  {
    // over a (Bag (Nullable Int)), (= (nullable.val t) 5) ---> {}
    return fixed;
  }
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
    // also (= 5 ((_ tuple.select 1) t)); of two constants for one column,
    // the later (then no row passes)
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

// For fixed = {1 -> 5},
//   (tuple ((_ tuple.select 0) t) ((_ tuple.select 1) t) 0)
//   ---> (tuple ((_ tuple.select 0) t) 5 0)
Node BagsRewriter::readFixed(const Node& body,
                             const Node& var,
                             const std::map<uint32_t, Node>& fixed) const
{
  // with an inner binder of var, body is kept: substitute is syntactic
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

BagsRewriteResponse BagsRewriter::rewriteAggregateConstantColumns(
    const TNode& n) const
{
  // AGGREGATE_CONSTANT_COLUMNS, for X : (Bag (Tuple Int Int)):
  //   ((_ table.aggr 0)
  //     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int)))
  //       (tuple ((_ tuple.select 0) t)
  //              7
  //              (+ ((_ tuple.select 2) acc) ((_ tuple.select 1) t))))
  //     (tuple 0 0 0)
  //     X)
  //   ---> (bag.map
  //          (lambda ((r (Tuple Int Int)))
  //            (tuple ((_ tuple.select 0) r) 7 ((_ tuple.select 1) r)))
  //          ((_ table.aggr 0)
  //            (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int)))
  //              (tuple ((_ tuple.select 0) t)
  //                     (+ ((_ tuple.select 1) acc) ((_ tuple.select 1) t))))
  //            (tuple 0 0)
  //            X))
  // and, every column a constant,
  //   ((_ table.aggr 0)
  //     (lambda ((t (Tuple Int Int)) (acc (Tuple Int))) (tuple 7))
  //     (tuple 0)
  //     X)
  //   ---> (bag.map (lambda ((r (Tuple Int))) (tuple 7))
  //                 (bag.setof ((_ table.project 0) X)))
  std::map<uint32_t, Node> constant = aggregateConstants(n);
  if (constant.empty())
  {
    return BagsRewriteResponse(n, Rewrite::NONE);
  }
  Node f = n[0];
  Node acc = f[0][1];
  size_t w = f[1].getNumChildren();
  // at = {0 -> 0, 2 -> 1} in the first example
  std::map<uint32_t, uint32_t> at;
  std::vector<TypeNode> types;
  for (uint32_t q = 0; q < w; q++)
  {
    if (constant.count(q))
    {
      continue;
    }
    // a staying step that reads a leaving column ---> no rule
    std::set<uint32_t> read;
    if (!readPositions(f[1][q], acc, read))
    {
      return BagsRewriteResponse(n, Rewrite::NONE);
    }
    for (uint32_t c : read)
    {
      if (constant.count(c))
      {
        return BagsRewriteResponse(n, Rewrite::NONE);
      }
    }
    at[q] = types.size();
    types.push_back(f[1][q].getType());
  }
  Node rows;
  if (at.empty())
  {
    const std::vector<uint32_t>& K =
        n.getOperator().getConst<ProjectOp>().getIndices();
    Node op = d_nm->mkConst(Kind::TABLE_PROJECT_OP, ProjectOp(K));
    std::vector<Node> children{op, n[2]};
    rows = d_nm->mkNode(Kind::BAG_SETOF,
                        d_nm->mkNode(Kind::TABLE_PROJECT, children));
  }
  else
  {
    TypeNode accType = d_nm->mkTupleType(types);
    Node acc2 = NodeManager::mkBoundVar("acc", accType);
    std::vector<Node> from, to, cells(at.size()), seeds(at.size());
    for (const std::pair<const uint32_t, uint32_t>& c : at)
    {
      from.push_back(datatypes::TupleUtils::nthElementOfTuple(acc, c.first));
      to.push_back(datatypes::TupleUtils::nthElementOfTuple(acc2, c.second));
    }
    for (const std::pair<const uint32_t, uint32_t>& c : at)
    {
      cells[c.second] = f[1][c.first].substitute(
          from.begin(), from.end(), to.begin(), to.end());
      seeds[c.second] = n[1][c.first];
    }
    Node body = datatypes::TupleUtils::constructTupleFromElements(
        accType, cells, 0, cells.size() - 1);
    Node seed = datatypes::TupleUtils::constructTupleFromElements(
        accType, seeds, 0, seeds.size() - 1);
    Node f2 = d_nm->mkNode(
        Kind::LAMBDA, d_nm->mkNode(Kind::BOUND_VAR_LIST, f[0][0], acc2), body);
    std::vector<Node> children{n.getOperator(), f2, seed, n[2]};
    rows = d_nm->mkNode(Kind::TABLE_AGGREGATE, children);
  }
  Node r = rowVariable(rows.getType().getBagElementType());
  std::vector<Node> cols;
  for (uint32_t q = 0; q < w; q++)
  {
    cols.push_back(constant.count(q)
                       ? constant[q]
                       : datatypes::TupleUtils::nthElementOfTuple(r, at[q]));
  }
  Node m = mkLambda(r,
                    datatypes::TupleUtils::constructTupleFromElements(
                        n.getType().getBagElementType(), cols, 0, w - 1));
  return BagsRewriteResponse(d_nm->mkNode(Kind::BAG_MAP, m, rows),
                             Rewrite::AGGREGATE_CONSTANT_COLUMNS);
}

// For X : (Bag (Tuple Int Int)),
//   ((_ table.aggr 0)
//     (lambda ((t (Tuple Int Int)) (acc (Tuple Int Int Int Int)))
//       (tuple ((_ tuple.select 0) t) 7 ((_ tuple.select 2) acc)
//              (+ ((_ tuple.select 3) acc) 1)))
//     (tuple 0 0 4 0) X)
//   ---> {1 -> 7, 2 -> 4}
std::map<uint32_t, Node> BagsRewriter::aggregateConstants(const Node& A) const
{
  std::map<uint32_t, Node> constants;
  Node f = A[0];
  Node i = A[1];
  if (f.getKind() != Kind::LAMBDA || f[0].getNumChildren() != 2
      || !isTupleTerm(f[1]) || !isTupleTerm(i)
      || i.getNumChildren() != f[1].getNumChildren())
  {
    return constants;
  }
  Node x = f[0][0];
  Node acc = f[0][1];
  for (size_t q = 0, m = f[1].getNumChildren(); q < m; q++)
  {
    Node c = f[1][q];
    if (c.isConst() && !occursFree(c, x) && !occursFree(c, acc))
    {
      // 7 ---> 7
      constants[q] = c;
    }
    else if (c == datatypes::TupleUtils::nthElementOfTuple(acc, q)
             && i[q].isConst())
    {
      // ((_ tuple.select 2) acc) from 4 ---> 4
      constants[q] = i[q];
    }
  }
  return constants;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal
