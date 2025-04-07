/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory rewriter.
 */

#include "theory/sets/theory_sets_rewriter.h"

#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "expr/elim_shadow_converter.h"
#include "options/sets_options.h"
#include "theory/bags/bags_utils.h"
#include "theory/datatypes/tuple_utils.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/rels_utils.h"
#include "theory/sets/set_reduction.h"
#include "theory/sets/theory_sets_rels.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
namespace theory {
namespace sets {

TheorySetsRewriter::TheorySetsRewriter(NodeManager* nm,
                                       bool cardEnabled,
                                       bool relsEnabled)
    : TheoryRewriter(nm), d_cardEnabled(cardEnabled), d_relsEnabled(relsEnabled)
{
  // Needs to be a subcall in DSL reconstruction since set.is_empty is used
  // as a premise to test emptiness of a set.
  registerProofRewriteRule(ProofRewriteRule::SETS_INSERT_ELIM,
                           TheoryRewriteCtx::PRE_DSL);
  registerProofRewriteRule(ProofRewriteRule::SETS_EVAL_OP,
                           TheoryRewriteCtx::POST_DSL);
}

Node TheorySetsRewriter::rewriteViaRule(ProofRewriteRule id, const Node& n)
{
  switch (id)
  {
    case ProofRewriteRule::SETS_INSERT_ELIM:
    {
      if (n.getKind() == Kind::SET_INSERT)
      {
        NodeManager* nm = nodeManager();
        size_t setNodeIndex = n.getNumChildren() - 1;
        Node elems = n[setNodeIndex];
        for (size_t i = 0; i < setNodeIndex; ++i)
        {
          size_t ii = (setNodeIndex-i)-1;
          Node singleton = nm->mkNode(Kind::SET_SINGLETON, n[ii]);
          elems = nm->mkNode(Kind::SET_UNION, singleton, elems);
        }
        return elems;
      }
    }
    break;
    case ProofRewriteRule::SETS_EVAL_OP:
    {
      if (n.getNumChildren() != 2 || !n[0].isConst() || !n[1].isConst())
      {
        return Node::null();
      }
      Kind k = n.getKind();
      if (k == Kind::SET_INTER)
      {
        std::set<Node> left = NormalForm::getElementsFromNormalConstant(n[0]);
        std::set<Node> right = NormalForm::getElementsFromNormalConstant(n[1]);
        std::set<Node> newSet;
        std::set_intersection(left.begin(),
                              left.end(),
                              right.begin(),
                              right.end(),
                              std::inserter(newSet, newSet.begin()));
        return NormalForm::elementsToSet(newSet, n.getType());
      }
      if (k == Kind::SET_MINUS)
      {
        std::set<Node> left = NormalForm::getElementsFromNormalConstant(n[0]);
        std::set<Node> right = NormalForm::getElementsFromNormalConstant(n[1]);
        std::set<Node> newSet;
        std::set_difference(left.begin(),
                            left.end(),
                            right.begin(),
                            right.end(),
                            std::inserter(newSet, newSet.begin()));
        return NormalForm::elementsToSet(newSet, n.getType());
      }
      if (k == Kind::SET_UNION)
      {
        std::set<Node> left = NormalForm::getElementsFromNormalConstant(n[0]);
        std::set<Node> right = NormalForm::getElementsFromNormalConstant(n[1]);
        std::set<Node> newSet;
        std::set_union(left.begin(),
                       left.end(),
                       right.begin(),
                       right.end(),
                       std::inserter(newSet, newSet.begin()));
        return NormalForm::elementsToSet(newSet, n.getType());
      }
    }
    break;
    default: break;
  }
  return Node::null();
}

bool TheorySetsRewriter::checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  if (setTerm.getKind() == Kind::SET_EMPTY)
  {
    return false;
  }

  if (setTerm.getKind() == Kind::SET_SINGLETON)
  {
    return elementTerm == setTerm[0];
  }

  Assert(setTerm.getKind() == Kind::SET_UNION
         && setTerm[0].getKind() == Kind::SET_SINGLETON)
      << "kind was " << setTerm.getKind() << ", term: " << setTerm;

  return elementTerm == setTerm[0][0]
         || checkConstantMembership(elementTerm, setTerm[1]);
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = nodeManager();
  Kind kind = node.getKind();
  Trace("sets-postrewrite") << "Process: " << node << std::endl;

  if(node.isConst()) {
    Trace("sets-rewrite-nf")
        << "Sets::rewrite: no rewrite (constant) " << node << std::endl;
    // Dare you touch the const and mangle it to something else.
    return RewriteResponse(REWRITE_DONE, node);
  }

  switch(kind) {
    case Kind::SET_MEMBER:
    {
      if (node[0].isConst() && node[1].isConst())
      {
        // both are constants
        TNode S = preRewrite(node[1]).d_node;
        bool isMember = checkConstantMembership(node[0], S);
        return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
      }
      else if (node[1].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      }
      else if (node[1].getKind() == Kind::SET_SINGLETON)
      {
        return RewriteResponse(REWRITE_AGAIN_FULL,
                               nm->mkNode(Kind::EQUAL, node[0], node[1][0]));
      }
      else if (node[1].getKind() == Kind::SET_UNION
               || node[1].getKind() == Kind::SET_INTER
               || node[1].getKind() == Kind::SET_MINUS)
      {
        Node ret = rewriteMembershipBinaryOp(node);
        return RewriteResponse(REWRITE_AGAIN_FULL, ret);
      }
      break;
    }  // Kind::SET_MEMBER

    case Kind::SET_SUBSET:
    {
      Assert(false)
          << "TheorySets::postRrewrite(): Subset is handled in preRewrite.";

      // but in off-chance we do end up here, let us do our best

      // rewrite (A subset-or-equal B) as (A union B = B)
      TNode A = node[0];
      TNode B = node[1];
      return RewriteResponse(
          REWRITE_AGAIN_FULL,
          nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::SET_UNION, A, B), B));
    }  // Kind::SET_SUBSET

    case Kind::EQUAL:
    {
      // rewrite: t = t with true (t term)
      // rewrite: c = c' with c different from c' false (c, c' constants)
      // otherwise: sort them
      if (node[0] == node[1])
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning true" << std::endl;
        return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning false" << std::endl;
        return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      }
      else if (node[0] > node[1])
      {
        Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }

    case Kind::SET_MINUS:
    {
      if (node[0] == node[1])
      {
        Node newNode = nm->mkConst(EmptySet(node[0].getType()));
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      else if (node[0].getKind() == Kind::SET_EMPTY
               || node[1].getKind() == Kind::SET_EMPTY)
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << node[0] << std::endl;
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Node newNode = rewriteViaRule(ProofRewriteRule::SETS_EVAL_OP, node);
        Assert(newNode.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }  // Kind::SET_MINUS

    case Kind::SET_INTER:
    {
      if (node[0] == node[1])
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << node[0] << std::endl;
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[1].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_AGAIN, node[1]);
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Node newNode = rewriteViaRule(ProofRewriteRule::SETS_EVAL_OP, node);
        Assert(newNode.isConst() && newNode.getType() == node.getType());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      else if (node[0] > node[1])
      {
        Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      // we don't merge non-constant intersections
      break;
    }  // Kind::INTERSECTION

    case Kind::SET_UNION:
    {
      // NOTE: case where it is CONST is taken care of at the top
      if (node[0] == node[1])
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << node[0] << std::endl;
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_AGAIN, node[1]);
      }
      else if (node[1].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Node newNode = rewriteViaRule(ProofRewriteRule::SETS_EVAL_OP, node);
        Assert(newNode.isConst());
        Trace("sets-rewrite")
            << "Sets::rewrite: UNION_CONSTANT_MERGE: " << newNode << std::endl;
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      else if (node[0] > node[1])
      {
        Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      // we don't merge non-constant unions
      break;
    }  // Kind::SET_UNION
    case Kind::SET_COMPLEMENT:
    {
      Node univ = nodeManager()->mkNullaryOperator(node[0].getType(),
                                                   Kind::SET_UNIVERSE);
      return RewriteResponse(
          REWRITE_AGAIN, nodeManager()->mkNode(Kind::SET_MINUS, univ, node[0]));
  }
  case Kind::SET_CARD:
  {
    // if cardinality not enabled, do not rewrite
    if (!d_cardEnabled)
    {
      return RewriteResponse(REWRITE_DONE, node);
    }
    if(node[0].isConst()) {
      std::set<Node> elements = NormalForm::getElementsFromNormalConstant(node[0]);
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConstInt(Rational(elements.size())));
    }
    else if (node[0].getKind() == Kind::SET_SINGLETON)
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstInt(Rational(1)));
    }
    else if (node[0].getKind() == Kind::SET_UNION)
    {
      Node ret = nodeManager()->mkNode(
          Kind::SUB,
          nodeManager()->mkNode(
              Kind::ADD,
              nodeManager()->mkNode(Kind::SET_CARD, node[0][0]),
              nodeManager()->mkNode(Kind::SET_CARD, node[0][1])),
          nodeManager()->mkNode(
              Kind::SET_CARD,
              nodeManager()->mkNode(Kind::SET_INTER, node[0][0], node[0][1])));
      return RewriteResponse(REWRITE_DONE, ret );
    }
    else if (node[0].getKind() == Kind::SET_MINUS)
    {
      Node ret = nodeManager()->mkNode(
          Kind::SUB,
          nodeManager()->mkNode(Kind::SET_CARD, node[0][0]),
          nodeManager()->mkNode(
              Kind::SET_CARD,
              nodeManager()->mkNode(Kind::SET_INTER, node[0][0], node[0][1])));
      return RewriteResponse(REWRITE_DONE, ret );
    }
    break;
  }

  case Kind::SET_CHOOSE:
  {
    if (node[0].getKind() == Kind::SET_SINGLETON)
    {
      //(= (choose (singleton x)) x) is a tautology
      // we return x for (choose (singleton x))
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }
    break;
  }  // Kind::SET_CHOOSE
  case Kind::SET_IS_EMPTY:
  {
    if (node[0].isConst())
    {
      // (set.is_empty c) ---> true if c is emptyset
      // (set.is_empty c) ---> false if c is a constant that is not the emptyset
      return RewriteResponse(
          REWRITE_DONE,
          nodeManager()->mkConst(node[0].getKind() == Kind::SET_EMPTY));
    }
    // (set.is_empty x) ----> (= x (as set.empty (Set T))).
    Node eq = nodeManager()->mkNode(
        Kind::EQUAL,
        node[0],
        nodeManager()->mkConst(EmptySet(node[0].getType())));
    return RewriteResponse(REWRITE_AGAIN, eq);
  }
  case Kind::SET_IS_SINGLETON:
  {
    Kind nk = node[0].getKind();
    if (nk == Kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(false));
    }
    if (nk == Kind::SET_SINGLETON)
    {
      //(= (is_singleton (singleton x)) is a tautology
      // we return true for (is_singleton (singleton x))
      return RewriteResponse(REWRITE_DONE, nodeManager()->mkConst(true));
    }
    break;
  }  // Kind::SET_IS_SINGLETON

  case Kind::SET_COMPREHENSION: return postRewriteComprehension(node); break;

  case Kind::SET_MAP: return postRewriteMap(node);
  case Kind::SET_FILTER: return postRewriteFilter(node);
  case Kind::SET_ALL: return postRewriteAll(node);
  case Kind::SET_SOME: return postRewriteSome(node);
  case Kind::SET_FOLD: return postRewriteFold(node);
  case Kind::RELATION_TABLE_JOIN:
  case Kind::RELATION_TRANSPOSE:
  case Kind::RELATION_PRODUCT:
  case Kind::RELATION_JOIN:
  case Kind::RELATION_TCLOSURE:
  case Kind::RELATION_IDEN:
  case Kind::RELATION_JOIN_IMAGE:
  case Kind::RELATION_GROUP:
  case Kind::RELATION_AGGREGATE:
  case Kind::RELATION_PROJECT:
    // maybe a relation kind?
    if (d_relsEnabled)
    {
      return postRewriteRelations(node);
    }
    break;
  default: break;
  }

  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheorySetsRewriter::postRewriteRelations(TNode node)
{
  NodeManager* nm = nodeManager();
  Kind kind = node.getKind();
  switch (kind)
  {
    case Kind::RELATION_TABLE_JOIN: return postRewriteTableJoin(node); break;
    case Kind::RELATION_TRANSPOSE:
    {
      if (node[0].getKind() == Kind::RELATION_TRANSPOSE)
      {
        return RewriteResponse(REWRITE_AGAIN, node[0][0]);
      }

      if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst())
      {
        std::set<Node> new_tuple_set;
        std::set<Node> tuple_set =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node>::iterator tuple_it = tuple_set.begin();

        while (tuple_it != tuple_set.end())
        {
          new_tuple_set.insert(TupleUtils::reverseTuple(*tuple_it));
          ++tuple_it;
        }
        Node new_node =
            NormalForm::elementsToSet(new_tuple_set, node.getType());
        Assert(new_node.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }
      if (node[0].getKind() != Kind::RELATION_TRANSPOSE)
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << node << std::endl;
        return RewriteResponse(REWRITE_DONE, node);
      }
      break;
    }

    case Kind::RELATION_PRODUCT:
    {
      Trace("sets-rels-postrewrite")
          << "Sets::postRewrite processing " << node << std::endl;
      if (node[0].getKind() == Kind::SET_EMPTY
          || node[1].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Trace("sets-rels-postrewrite")
            << "Sets::postRewrite processing **** " << node << std::endl;
        std::set<Node> new_tuple_set;
        std::set<Node> left =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node> right =
            NormalForm::getElementsFromNormalConstant(node[1]);
        std::set<Node>::iterator left_it = left.begin();
        int left_len = (*left_it).getType().getTupleLength();
        TypeNode tn = node.getType().getSetElementType();
        while (left_it != left.end())
        {
          Trace("rels-debug")
              << "Sets::postRewrite processing left_it = " << *left_it
              << std::endl;
          std::vector<Node> left_tuple;
          left_tuple.push_back(tn.getDType()[0].getConstructor());
          for (int i = 0; i < left_len; i++)
          {
            left_tuple.push_back(TupleUtils::nthElementOfTuple(*left_it, i));
          }
          std::set<Node>::iterator right_it = right.begin();
          int right_len = (*right_it).getType().getTupleLength();
          while (right_it != right.end())
          {
            Trace("rels-debug")
                << "Sets::postRewrite processing right_it = " << *right_it
                << std::endl;
            std::vector<Node> right_tuple;
            for (int j = 0; j < right_len; j++)
            {
              right_tuple.push_back(
                  TupleUtils::nthElementOfTuple(*right_it, j));
            }
            std::vector<Node> new_tuple;
            new_tuple.insert(
                new_tuple.end(), left_tuple.begin(), left_tuple.end());
            new_tuple.insert(
                new_tuple.end(), right_tuple.begin(), right_tuple.end());
            Node composed_tuple =
                nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, new_tuple);
            new_tuple_set.insert(composed_tuple);
            ++right_it;
          }
          ++left_it;
        }
        Node new_node =
            NormalForm::elementsToSet(new_tuple_set, node.getType());
        Assert(new_node.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }
      break;
    }

    case Kind::RELATION_JOIN:
    {
      if (node[0].getKind() == Kind::SET_EMPTY
          || node[1].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst() && node[1].isConst())
      {
        Trace("sets-rels-postrewrite")
            << "Sets::postRewrite processing " << node << std::endl;
        std::set<Node> new_tuple_set;
        std::set<Node> left =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node> right =
            NormalForm::getElementsFromNormalConstant(node[1]);
        std::set<Node>::iterator left_it = left.begin();
        int left_len = (*left_it).getType().getTupleLength();
        TypeNode tn = node.getType().getSetElementType();
        while (left_it != left.end())
        {
          std::vector<Node> left_tuple;
          left_tuple.push_back(tn.getDType()[0].getConstructor());
          for (int i = 0; i < left_len - 1; i++)
          {
            left_tuple.push_back(TupleUtils::nthElementOfTuple(*left_it, i));
          }
          std::set<Node>::iterator right_it = right.begin();
          int right_len = (*right_it).getType().getTupleLength();
          while (right_it != right.end())
          {
            if (TupleUtils::nthElementOfTuple(*left_it, left_len - 1)
                == TupleUtils::nthElementOfTuple(*right_it, 0))
            {
              std::vector<Node> right_tuple;
              for (int j = 1; j < right_len; j++)
              {
                right_tuple.push_back(
                    TupleUtils::nthElementOfTuple(*right_it, j));
              }
              std::vector<Node> new_tuple;
              new_tuple.insert(
                  new_tuple.end(), left_tuple.begin(), left_tuple.end());
              new_tuple.insert(
                  new_tuple.end(), right_tuple.begin(), right_tuple.end());
              Node composed_tuple =
                  nodeManager()->mkNode(Kind::APPLY_CONSTRUCTOR, new_tuple);
              new_tuple_set.insert(composed_tuple);
            }
            ++right_it;
          }
          ++left_it;
        }
        Node new_node =
            NormalForm::elementsToSet(new_tuple_set, node.getType());
        Assert(new_node.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }

      break;
    }

    case Kind::RELATION_TCLOSURE:
    {
      if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst())
      {
        std::set<Node> rel_mems =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node> tc_rel_mems = RelsUtils::computeTC(rel_mems, node);
        Node new_node = NormalForm::elementsToSet(tc_rel_mems, node.getType());
        Assert(new_node.isConst());
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }
      else if (node[0].getKind() == Kind::RELATION_TCLOSURE)
      {
        return RewriteResponse(REWRITE_AGAIN, node[0]);
      }
      else if (node[0].getKind() != Kind::RELATION_TCLOSURE)
      {
        Trace("sets-postrewrite")
            << "Sets::postRewrite returning " << node << std::endl;
        return RewriteResponse(REWRITE_DONE, node);
      }
      break;
    }

    case Kind::RELATION_IDEN:
    {
      if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst())
      {
        std::set<Node> iden_rel_mems;
        std::set<Node> rel_mems =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node>::iterator rel_mems_it = rel_mems.begin();

        while (rel_mems_it != rel_mems.end())
        {
          Node fst_mem = TupleUtils::nthElementOfTuple(*rel_mems_it, 0);
          iden_rel_mems.insert(
              RelsUtils::constructPair(node, fst_mem, fst_mem));
          ++rel_mems_it;
        }

        Node new_node =
            NormalForm::elementsToSet(iden_rel_mems, node.getType());
        Assert(new_node.isConst());
        Trace("rels-postrewrite")
            << "Rels::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }
      else
      {
        Trace("rels-postrewrite")
            << "Rels::postRewrite miss to handle term " << node << std::endl;
      }
      break;
    }

    case Kind::RELATION_JOIN_IMAGE:
    {
      unsigned int min_card =
          node[1].getConst<Rational>().getNumerator().getUnsignedInt();
      Trace("rels-postrewrite") << "Rels::postRewrite  " << node
                                << " with min_card = " << min_card << std::endl;

      if (min_card == 0)
      {
        return RewriteResponse(
            REWRITE_DONE,
            nm->mkNullaryOperator(node.getType(), Kind::SET_UNIVERSE));
      }
      else if (node[0].getKind() == Kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE,
                               nm->mkConst(EmptySet(node.getType())));
      }
      else if (node[0].isConst())
      {
        std::set<Node> has_checked;
        std::set<Node> join_img_mems;
        std::set<Node> rel_mems =
            NormalForm::getElementsFromNormalConstant(node[0]);
        std::set<Node>::iterator rel_mems_it = rel_mems.begin();

        while (rel_mems_it != rel_mems.end())
        {
          Node fst_mem = TupleUtils::nthElementOfTuple(*rel_mems_it, 0);
          if (has_checked.find(fst_mem) != has_checked.end())
          {
            ++rel_mems_it;
            continue;
          }
          has_checked.insert(fst_mem);
          std::set<Node> existing_mems;
          std::set<Node>::iterator rel_mems_it_snd = rel_mems.begin();
          while (rel_mems_it_snd != rel_mems.end())
          {
            Node fst_mem_snd =
                TupleUtils::nthElementOfTuple(*rel_mems_it_snd, 0);
            if (fst_mem == fst_mem_snd)
            {
              existing_mems.insert(
                  TupleUtils::nthElementOfTuple(*rel_mems_it_snd, 1));
            }
            ++rel_mems_it_snd;
          }
          if (existing_mems.size() >= min_card)
          {
            const DType& dt = node.getType().getSetElementType().getDType();
            join_img_mems.insert(nm->mkNode(
                Kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), fst_mem));
          }
          ++rel_mems_it;
        }
        Node new_node =
            NormalForm::elementsToSet(join_img_mems, node.getType());
        Assert(new_node.isConst());
        Trace("rels-postrewrite")
            << "Rels::postRewrite returning " << new_node << std::endl;
        return RewriteResponse(REWRITE_DONE, new_node);
      }
      else
      {
        Trace("rels-postrewrite")
            << "Rels::postRewrite miss to handle term " << node << std::endl;
      }
      break;
    }

    case Kind::RELATION_GROUP: return postRewriteGroup(node);
    case Kind::RELATION_AGGREGATE: return postRewriteAggregate(node);
    case Kind::RELATION_PROJECT: return postRewriteProject(node);
    default: break;
  }

  return RewriteResponse(REWRITE_DONE, node);
}

Node TheorySetsRewriter::rewriteMembershipBinaryOp(const Node& node)
{
  Assert(node.getKind() == Kind::SET_MEMBER);
  Assert(node[1].getKind() == Kind::SET_UNION
         || node[1].getKind() == Kind::SET_INTER
         || node[1].getKind() == Kind::SET_MINUS);
  NodeManager* nm = nodeManager();
  std::vector<Node> children;
  for (size_t i = 0, nchild = node[1].getNumChildren(); i < nchild; i++)
  {
    Node nc = nm->mkNode(Kind::SET_MEMBER, node[0], node[1][i]);
    if (node[1].getKind() == Kind::SET_MINUS && i == 1)
    {
      nc = nc.negate();
    }
    children.push_back(nc);
  }
  return nm->mkNode(node[1].getKind() == Kind::SET_UNION ? Kind::OR : Kind::AND,
                    children);
}

// static
RewriteResponse TheorySetsRewriter::preRewrite(TNode node) {
  NodeManager* nm = nodeManager();
  Kind k = node.getKind();
  if (k == Kind::EQUAL)
  {
    if(node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
  }
  else if (k == Kind::SET_INSERT)
  {
    Node ret = rewriteViaRule(ProofRewriteRule::SETS_INSERT_ELIM, node);
    return RewriteResponse(REWRITE_AGAIN, ret);
  }
  else if (k == Kind::SET_SUBSET)
  {
    // rewrite (A subset-or-equal B) as (A union B = B)
    return RewriteResponse(
        REWRITE_AGAIN,
        nm->mkNode(Kind::EQUAL,
                   nm->mkNode(Kind::SET_UNION, node[0], node[1]),
                   node[1]));
  }

  // could have an efficient normalizer for union here

  return RewriteResponse(REWRITE_DONE, node);
}

RewriteResponse TheorySetsRewriter::postRewriteComprehension(TNode n)
{
  Node ne = ElimShadowNodeConverter::eliminateShadow(n);
  if (ne != n)
  {
    return RewriteResponse(REWRITE_AGAIN_FULL, ne);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheorySetsRewriter::postRewriteTableJoin(TNode n)
{
  Assert(n.getKind() == Kind::RELATION_TABLE_JOIN);

  Node A = n[0];
  Node B = n[1];
  TypeNode tupleType = n.getType().getSetElementType();
  if (A.isConst() && B.isConst())
  {
    auto [aIndices, bIndices] = bags::BagsUtils::splitTableJoinIndices(n);

    std::set<Node> elementsA = NormalForm::getElementsFromNormalConstant(A);
    std::set<Node> elementsB = NormalForm::getElementsFromNormalConstant(B);
    std::set<Node> newSet;

    for (const auto& a : elementsA)
    {
      for (const auto& b : elementsB)
      {
        bool notMatched = false;
        for (size_t i = 0; i < aIndices.size(); i++)
        {
          Node aElement = TupleUtils::nthElementOfTuple(a, aIndices[i]);
          Node bElement = TupleUtils::nthElementOfTuple(b, bIndices[i]);
          if (aElement != bElement)
          {
            notMatched = true;
          }
        }
        if (notMatched)
        {
          continue;
        }
        Node element = TupleUtils::concatTuples(tupleType, a, b);
        newSet.insert(element);
      }
    }

    Node ret = NormalForm::elementsToSet(newSet, n.getType());

    return RewriteResponse(REWRITE_AGAIN_FULL, ret);
  }
  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheorySetsRewriter::postRewriteMap(TNode n)
{
  Assert(n.getKind() == Kind::SET_MAP);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
    {
      TypeNode rangeType = n[0].getType().getRangeType();
      // (set.map f (as set.empty (Set T1)) = (as set.empty (Set T2))
      Node ret = nm->mkConst(EmptySet(nm->mkSetType(rangeType)));
      return RewriteResponse(REWRITE_DONE, ret);
    }
    case Kind::SET_SINGLETON:
    {
      // (set.map f (set.singleton x)) = (set.singleton (f x))
      Node mappedElement = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = nm->mkNode(Kind::SET_SINGLETON, mappedElement);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case Kind::SET_UNION:
    {
      // (set.map f (set.union A B)) = (set.union (set.map f A) (set.map f B))
      Node a = nm->mkNode(Kind::SET_MAP, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::SET_MAP, n[0], n[1][1]);
      Node ret = nm->mkNode(Kind::SET_UNION, a, b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteFilter(TNode n)
{
  Assert(n.getKind() == Kind::SET_FILTER);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
    {
      // (set.filter p (as set.empty (Set T)) = (as set.empty (Set T))
      return RewriteResponse(REWRITE_DONE, n[1]);
    }
    case Kind::SET_SINGLETON:
    {
      // (set.filter p (set.singleton x)) =
      //       (ite (p x) (set.singleton x) (as set.empty (Set T)))
      Node empty = nm->mkConst(EmptySet(n.getType()));
      Node condition = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      Node ret = nm->mkNode(Kind::ITE, condition, n[1], empty);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case Kind::SET_UNION:
    {
      // (set.filter p (set.union A B)) =
      //   (set.union (set.filter p A) (set.filter p B))
      Node a = nm->mkNode(Kind::SET_FILTER, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::SET_FILTER, n[0], n[1][1]);
      Node ret = nm->mkNode(Kind::SET_UNION, a, b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteAll(TNode n)
{
  Assert(n.getKind() == Kind::SET_ALL);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
    {
      // (set.all p (as set.empty (Set T)) = true)
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    case Kind::SET_SINGLETON:
    {
      // (set.all p (set.singleton x)) = (p x)
      Node ret = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case Kind::SET_UNION:
    {
      // (set.all p (set.union A B)) =
      //   (and (set.all p A) (set.all p B))
      Node a = nm->mkNode(Kind::SET_ALL, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::SET_ALL, n[0], n[1][1]);
      Node ret = a.andNode(b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    default:
    {
      // (set.all p A) is rewritten as (set.filter p A) = A
      Node filter = nm->mkNode(Kind::SET_FILTER, n[0], n[1]);
      Node all = filter.eqNode(n[1]);
      return RewriteResponse(REWRITE_AGAIN_FULL, all);
    }
  }
}

RewriteResponse TheorySetsRewriter::postRewriteSome(TNode n)
{
  Assert(n.getKind() == Kind::SET_SOME);
  NodeManager* nm = nodeManager();
  Kind k = n[1].getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
    {
      // (set.some p (as set.empty (Set T)) = false)
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
    }
    case Kind::SET_SINGLETON:
    {
      // (set.some p (set.singleton x)) = (p x)
      Node ret = nm->mkNode(Kind::APPLY_UF, n[0], n[1][0]);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case Kind::SET_UNION:
    {
      // (set.some p (set.union A B)) =
      //   (or (set.some p A) (set.some p B))
      Node a = nm->mkNode(Kind::SET_SOME, n[0], n[1][0]);
      Node b = nm->mkNode(Kind::SET_SOME, n[0], n[1][1]);
      Node ret = a.orNode(b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    default:
    {
      // (set.some p A) is rewritten as (distinct (set.filter p A) set.empty))
      Node filter = nm->mkNode(Kind::SET_FILTER, n[0], n[1]);
      Node empty = nm->mkConst(EmptySet(n[1].getType()));
      Node some = filter.eqNode(empty).notNode();
      return RewriteResponse(REWRITE_AGAIN_FULL, some);
    }
  }
}

RewriteResponse TheorySetsRewriter::postRewriteFold(TNode n)
{
  Assert(n.getKind() == Kind::SET_FOLD);
  NodeManager* nm = nodeManager();
  Node f = n[0];
  Node t = n[1];
  Kind k = n[2].getKind();
  switch (k)
  {
    case Kind::SET_EMPTY:
    {
      // ((set.fold f t (as set.empty (Set T))) = t
      return RewriteResponse(REWRITE_DONE, t);
    }
    case Kind::SET_SINGLETON:
    {
      // (set.fold f t (set.singleton x)) = (f x t)
      Node x = n[2][0];
      Node f_x_t = nm->mkNode(Kind::APPLY_UF, f, x, t);
      return RewriteResponse(REWRITE_AGAIN_FULL, f_x_t);
    }
    case Kind::SET_UNION:
    {
      // (set.fold f t (set.union B C)) = (set.fold f (set.fold f t A) B))
      Node A = n[2][0];
      Node B = n[2][1];
      Node foldA = nm->mkNode(Kind::SET_FOLD, f, t, A);
      Node fold = nm->mkNode(Kind::SET_FOLD, f, foldA, B);
      return RewriteResponse(REWRITE_AGAIN_FULL, fold);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteGroup(TNode n)
{
  Assert(n.getKind() == Kind::RELATION_GROUP);
  Node A = n[0];
  Kind k = A.getKind();
  if (k == Kind::SET_EMPTY || k == Kind::SET_SINGLETON)
  {
    NodeManager* nm = nodeManager();
    // - ((_ rel.group n1 ... nk) (as set.empty (Relation T))) =
    //    (rel.singleton (as set.empty (Relation T) ))
    // - ((_ rel.group n1 ... nk) (set.singleton x)) =
    //      (set.singleton (set.singleton x))
    Node singleton = nm->mkNode(Kind::SET_SINGLETON, A);
    return RewriteResponse(REWRITE_AGAIN_FULL, singleton);
  }
  if (A.isConst())
  {
    Node evaluation = RelsUtils::evaluateGroup(n);
    return RewriteResponse(REWRITE_AGAIN_FULL, evaluation);
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheorySetsRewriter::postRewriteAggregate(TNode n)
{
  Assert(n.getKind() == Kind::RELATION_AGGREGATE);
  if (n[1].isConst() && n[2].isConst())
  {
    Node ret = RelsUtils::evaluateRelationAggregate(n);
    if (ret != n)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }

  return RewriteResponse(REWRITE_DONE, n);
}

RewriteResponse TheorySetsRewriter::postRewriteProject(TNode n)
{
  Assert(n.getKind() == Kind::RELATION_PROJECT);
  if (n[0].isConst())
  {
    Node ret = SetReduction::reduceProjectOperator(n);
    if (ret != n)
    {
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
  }
  return RewriteResponse(REWRITE_DONE, n);
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal
