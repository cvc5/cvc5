/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/datatypes/tuple_utils.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/rels_utils.h"
#include "theory/sets/set_reduction.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory::datatypes;

namespace cvc5::internal {
namespace theory {
namespace sets {

bool TheorySetsRewriter::checkConstantMembership(TNode elementTerm, TNode setTerm)
{
  if (setTerm.getKind() == kind::SET_EMPTY)
  {
    return false;
  }

  if (setTerm.getKind() == kind::SET_SINGLETON)
  {
    return elementTerm == setTerm[0];
  }

  Assert(setTerm.getKind() == kind::SET_UNION
         && setTerm[0].getKind() == kind::SET_SINGLETON)
      << "kind was " << setTerm.getKind() << ", term: " << setTerm;

  return elementTerm == setTerm[0][0]
         || checkConstantMembership(elementTerm, setTerm[1]);
}

// static
RewriteResponse TheorySetsRewriter::postRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();
  Kind kind = node.getKind();
  Trace("sets-postrewrite") << "Process: " << node << std::endl;

  if(node.isConst()) {
    Trace("sets-rewrite-nf")
        << "Sets::rewrite: no rewrite (constant) " << node << std::endl;
    // Dare you touch the const and mangle it to something else.
    return RewriteResponse(REWRITE_DONE, node);
  }

  switch(kind) {
    case kind::SET_MEMBER:
    {
      if (node[0].isConst() && node[1].isConst())
      {
        // both are constants
        TNode S = preRewrite(node[1]).d_node;
        bool isMember = checkConstantMembership(node[0], S);
        return RewriteResponse(REWRITE_DONE, nm->mkConst(isMember));
      }
      else if (node[1].getKind() == kind::SET_EMPTY)
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
      }
      else if (node[1].getKind() == kind::SET_SINGLETON)
      {
        return RewriteResponse(REWRITE_AGAIN_FULL,
                               nm->mkNode(kind::EQUAL, node[0], node[1][0]));
      }
      else if (node[1].getKind() == kind::SET_UNION
               || node[1].getKind() == kind::SET_INTER
               || node[1].getKind() == kind::SET_MINUS)
      {
        std::vector<Node> children;
        for (unsigned i = 0; i < node[1].getNumChildren(); i++)
        {
          Node nc = nm->mkNode(kind::SET_MEMBER, node[0], node[1][i]);
          if (node[1].getKind() == kind::SET_MINUS && i == 1)
          {
            nc = nc.negate();
          }
          children.push_back(nc);
        }
        return RewriteResponse(
            REWRITE_AGAIN_FULL,
            nm->mkNode(
                node[1].getKind() == kind::SET_UNION ? kind::OR : kind::AND,
                children));
      }
      break;
    }  // kind::SET_MEMBER

    case kind::SET_SUBSET:
    {
      Assert(false)
          << "TheorySets::postRrewrite(): Subset is handled in preRewrite.";

      // but in off-chance we do end up here, let us do our best

      // rewrite (A subset-or-equal B) as (A union B = B)
      TNode A = node[0];
      TNode B = node[1];
      return RewriteResponse(
          REWRITE_AGAIN_FULL,
          nm->mkNode(kind::EQUAL, nm->mkNode(kind::SET_UNION, A, B), B));
    }  // kind::SET_SUBSET

  case kind::EQUAL: {
    //rewrite: t = t with true (t term)
    //rewrite: c = c' with c different from c' false (c, c' constants)
    //otherwise: sort them
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning true" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
    else if (node[0].isConst() && node[1].isConst()) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning false" << std::endl;
      return RewriteResponse(REWRITE_DONE, nm->mkConst(false));
    }
    else if (node[0] > node[1]) {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }

  case kind::SET_MINUS:
  {
    if (node[0] == node[1])
    {
      Node newNode = nm->mkConst(EmptySet(node[0].getType()));
      Trace("sets-postrewrite")
          << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    else if (node[0].getKind() == kind::SET_EMPTY
             || node[1].getKind() == kind::SET_EMPTY)
    {
      Trace("sets-postrewrite")
          << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[1].getKind() == kind::SET_UNIVERSE)
    {
      return RewriteResponse(
          REWRITE_AGAIN,
          NodeManager::currentNM()->mkConst(EmptySet(node[1].getType())));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_difference(left.begin(),
                          left.end(),
                          right.begin(),
                          right.end(),
                          std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
      Assert(newNode.isConst());
      Trace("sets-postrewrite")
          << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    break;
  }  // kind::SET_MINUS

  case kind::SET_INTER:
  {
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[0].getKind() == kind::SET_EMPTY
             || node[1].getKind() == kind::SET_UNIVERSE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[1].getKind() == kind::SET_EMPTY
             || node[0].getKind() == kind::SET_UNIVERSE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[1]);
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_intersection(left.begin(), left.end(), right.begin(), right.end(),
                            std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
      Assert(newNode.isConst() && newNode.getType() == node.getType());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << newNode << std::endl;
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    else if (node[0] > node[1])
    {
      Node newNode = nm->mkNode(node.getKind(), node[1], node[0]);
      return RewriteResponse(REWRITE_DONE, newNode);
    }
    // we don't merge non-constant intersections
    break;
  }  // kind::INTERSECTION

  case kind::SET_UNION:
  {
    // NOTE: case where it is CONST is taken care of at the top
    if(node[0] == node[1]) {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node[0] << std::endl;
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[0].getKind() == kind::SET_EMPTY
             || node[1].getKind() == kind::SET_UNIVERSE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[1]);
    }
    else if (node[1].getKind() == kind::SET_EMPTY
             || node[0].getKind() == kind::SET_UNIVERSE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node> newSet;
      std::set_union(left.begin(), left.end(), right.begin(), right.end(),
                          std::inserter(newSet, newSet.begin()));
      Node newNode = NormalForm::elementsToSet(newSet, node.getType());
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
  }  // kind::SET_UNION
  case kind::SET_COMPLEMENT:
  {
    Node univ = NodeManager::currentNM()->mkNullaryOperator(node[0].getType(),
                                                            kind::SET_UNIVERSE);
    return RewriteResponse(
        REWRITE_AGAIN,
        NodeManager::currentNM()->mkNode(kind::SET_MINUS, univ, node[0]));
  }
  case kind::SET_CARD:
  {
    if(node[0].isConst()) {
      std::set<Node> elements = NormalForm::getElementsFromNormalConstant(node[0]);
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConstInt(Rational(elements.size())));
    }
    else if (node[0].getKind() == kind::SET_SINGLETON)
    {
      return RewriteResponse(REWRITE_DONE, nm->mkConstInt(Rational(1)));
    }
    else if (node[0].getKind() == kind::SET_UNION)
    {
      Node ret = NodeManager::currentNM()->mkNode(
          kind::SUB,
          NodeManager::currentNM()->mkNode(
              kind::ADD,
              NodeManager::currentNM()->mkNode(kind::SET_CARD, node[0][0]),
              NodeManager::currentNM()->mkNode(kind::SET_CARD, node[0][1])),
          NodeManager::currentNM()->mkNode(
              kind::SET_CARD,
              NodeManager::currentNM()->mkNode(
                  kind::SET_INTER, node[0][0], node[0][1])));
      return RewriteResponse(REWRITE_DONE, ret );
    }
    else if (node[0].getKind() == kind::SET_MINUS)
    {
      Node ret = NodeManager::currentNM()->mkNode(
          kind::SUB,
          NodeManager::currentNM()->mkNode(kind::SET_CARD, node[0][0]),
          NodeManager::currentNM()->mkNode(
              kind::SET_CARD,
              NodeManager::currentNM()->mkNode(
                  kind::SET_INTER, node[0][0], node[0][1])));
      return RewriteResponse(REWRITE_DONE, ret );
    }
    break;
  }

  case kind::SET_CHOOSE:
  {
    if (node[0].getKind() == SET_SINGLETON)
    {
      //(= (choose (singleton x)) x) is a tautology
      // we return x for (choose (singleton x))
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }
    break;
  }  // kind::SET_CHOOSE
  case kind::SET_IS_SINGLETON:
  {
    if (node[0].getKind() == SET_SINGLETON)
    {
      //(= (is_singleton (singleton x)) is a tautology
      // we return true for (is_singleton (singleton x))
      return RewriteResponse(REWRITE_AGAIN,
                             NodeManager::currentNM()->mkConst(true));
    }
    break;
  }  // kind::SET_IS_SINGLETON

  case SET_COMPREHENSION: return postRewriteComprehension(node); break;

  case SET_MAP: return postRewriteMap(node);
  case SET_FILTER: return postRewriteFilter(node);
  case SET_FOLD: return postRewriteFold(node);

  case kind::RELATION_TRANSPOSE:
  {
    if (node[0].getKind() == kind::RELATION_TRANSPOSE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }

    if (node[0].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst())
    {
      std::set<Node> new_tuple_set;
      std::set<Node> tuple_set = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node>::iterator tuple_it = tuple_set.begin();

      while(tuple_it != tuple_set.end()) {
        new_tuple_set.insert(TupleUtils::reverseTuple(*tuple_it));
        ++tuple_it;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    if (node[0].getKind() != kind::RELATION_TRANSPOSE)
    {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node << std::endl;
      return RewriteResponse(REWRITE_DONE, node);
    }
    break;
  }

  case kind::RELATION_PRODUCT:
  {
    Trace("sets-rels-postrewrite") << "Sets::postRewrite processing " <<  node << std::endl;
    if (node[0].getKind() == kind::SET_EMPTY
        || node[1].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      Trace("sets-rels-postrewrite") << "Sets::postRewrite processing **** " <<  node << std::endl;
      std::set<Node> new_tuple_set;
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node>::iterator left_it = left.begin();
      int left_len = (*left_it).getType().getTupleLength();
      TypeNode tn = node.getType().getSetElementType();
      while(left_it != left.end()) {
        Trace("rels-debug") << "Sets::postRewrite processing left_it = " <<  *left_it << std::endl;
        std::vector<Node> left_tuple;
        left_tuple.push_back(tn.getDType()[0].getConstructor());
        for(int i = 0; i < left_len; i++) {
          left_tuple.push_back(TupleUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          Trace("rels-debug") << "Sets::postRewrite processing right_it = " <<  *right_it << std::endl;
          std::vector<Node> right_tuple;
          for(int j = 0; j < right_len; j++) {
            right_tuple.push_back(TupleUtils::nthElementOfTuple(*right_it,j));
          }
          std::vector<Node> new_tuple;
          new_tuple.insert(new_tuple.end(), left_tuple.begin(), left_tuple.end());
          new_tuple.insert(new_tuple.end(), right_tuple.begin(), right_tuple.end());
          Node composed_tuple = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, new_tuple);
          new_tuple_set.insert(composed_tuple);
          ++right_it;
        }
        ++left_it;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    break;
  }

  case kind::RELATION_JOIN:
  {
    if (node[0].getKind() == kind::SET_EMPTY
        || node[1].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst() && node[1].isConst())
    {
      Trace("sets-rels-postrewrite") << "Sets::postRewrite processing " <<  node << std::endl;
      std::set<Node> new_tuple_set;
      std::set<Node> left = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> right = NormalForm::getElementsFromNormalConstant(node[1]);
      std::set<Node>::iterator left_it = left.begin();
      int left_len = (*left_it).getType().getTupleLength();
      TypeNode tn = node.getType().getSetElementType();
      while(left_it != left.end()) {
        std::vector<Node> left_tuple;
        left_tuple.push_back(tn.getDType()[0].getConstructor());
        for(int i = 0; i < left_len - 1; i++) {
          left_tuple.push_back(TupleUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          if(TupleUtils::nthElementOfTuple(*left_it,left_len-1) == TupleUtils::nthElementOfTuple(*right_it,0)) {
            std::vector<Node> right_tuple;
            for(int j = 1; j < right_len; j++) {
              right_tuple.push_back(
                  TupleUtils::nthElementOfTuple(*right_it,j));
            }
            std::vector<Node> new_tuple;
            new_tuple.insert(new_tuple.end(), left_tuple.begin(), left_tuple.end());
            new_tuple.insert(new_tuple.end(), right_tuple.begin(), right_tuple.end());
            Node composed_tuple = NodeManager::currentNM()->mkNode(kind::APPLY_CONSTRUCTOR, new_tuple);
            new_tuple_set.insert(composed_tuple);
          }
          ++right_it;
        }
        ++left_it;
      }
      Node new_node = NormalForm::elementsToSet(new_tuple_set, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }

    break;
  }

  case kind::RELATION_TCLOSURE:
  {
    if (node[0].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst())
    {
      std::set<Node> rel_mems = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node> tc_rel_mems = RelsUtils::computeTC(rel_mems, node);
      Node new_node = NormalForm::elementsToSet(tc_rel_mems, node.getType());
      Assert(new_node.isConst());
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    else if (node[0].getKind() == kind::RELATION_TCLOSURE)
    {
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    }
    else if (node[0].getKind() != kind::RELATION_TCLOSURE)
    {
      Trace("sets-postrewrite") << "Sets::postRewrite returning " << node << std::endl;
      return RewriteResponse(REWRITE_DONE, node);
    }
    break;
  }

  case kind::RELATION_IDEN:
  {
    if (node[0].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst())
    {
      std::set<Node> iden_rel_mems;
      std::set<Node> rel_mems = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node>::iterator rel_mems_it = rel_mems.begin();

      while( rel_mems_it != rel_mems.end() ) {
        Node fst_mem = TupleUtils::nthElementOfTuple( *rel_mems_it, 0);
        iden_rel_mems.insert(RelsUtils::constructPair(node, fst_mem, fst_mem));
        ++rel_mems_it;
      }

      Node new_node = NormalForm::elementsToSet(iden_rel_mems, node.getType());
      Assert(new_node.isConst());
      Trace("rels-postrewrite") << "Rels::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    else
    {
      Trace("rels-postrewrite") << "Rels::postRewrite miss to handle term " << node << std::endl;
    }
    break;
  }

  case kind::RELATION_JOIN_IMAGE:
  {
    unsigned int min_card = node[1].getConst<Rational>().getNumerator().getUnsignedInt();
    Trace("rels-postrewrite") << "Rels::postRewrite  " << node << " with min_card = " << min_card << std::endl;

    if( min_card == 0) {
      return RewriteResponse(
          REWRITE_DONE,
          nm->mkNullaryOperator(node.getType(), kind::SET_UNIVERSE));
    }
    else if (node[0].getKind() == kind::SET_EMPTY)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(EmptySet(node.getType())));
    }
    else if (node[0].isConst())
    {
      std::set<Node> has_checked;
      std::set<Node> join_img_mems;
      std::set<Node> rel_mems = NormalForm::getElementsFromNormalConstant(node[0]);
      std::set<Node>::iterator rel_mems_it = rel_mems.begin();

      while( rel_mems_it != rel_mems.end() ) {
        Node fst_mem = TupleUtils::nthElementOfTuple( *rel_mems_it, 0);
        if( has_checked.find( fst_mem ) != has_checked.end() ) {
          ++rel_mems_it;
          continue;
        }
        has_checked.insert( fst_mem );
        std::set<Node> existing_mems;
        std::set<Node>::iterator rel_mems_it_snd = rel_mems.begin();
        while( rel_mems_it_snd != rel_mems.end() ) {
          Node fst_mem_snd = TupleUtils::nthElementOfTuple( *rel_mems_it_snd, 0);
          if( fst_mem == fst_mem_snd ) {
            existing_mems.insert(
                TupleUtils::nthElementOfTuple( *rel_mems_it_snd, 1) );
          }
          ++rel_mems_it_snd;
        }
        if( existing_mems.size() >= min_card ) {
          const DType& dt = node.getType().getSetElementType().getDType();
          join_img_mems.insert(
              nm->mkNode(APPLY_CONSTRUCTOR, dt[0].getConstructor(), fst_mem));
        }
        ++rel_mems_it;
      }
      Node new_node = NormalForm::elementsToSet(join_img_mems, node.getType());
      Assert(new_node.isConst());
      Trace("rels-postrewrite") << "Rels::postRewrite returning " << new_node << std::endl;
      return RewriteResponse(REWRITE_DONE, new_node);
    }
    else
    {
      Trace("rels-postrewrite") << "Rels::postRewrite miss to handle term " << node << std::endl;
    }
    break;
  }

  case RELATION_GROUP: return postRewriteGroup(node);
  case RELATION_AGGREGATE: return postRewriteAggregate(node);
  case RELATION_PROJECT: return postRewriteProject(node);
  default: break;
  }

  return RewriteResponse(REWRITE_DONE, node);
}


// static
RewriteResponse TheorySetsRewriter::preRewrite(TNode node) {
  NodeManager* nm = NodeManager::currentNM();
  Kind k = node.getKind();
  if (k == kind::EQUAL)
  {
    if(node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, nm->mkConst(true));
    }
  }
  else if (k == kind::SET_INSERT)
  {
    size_t setNodeIndex =  node.getNumChildren()-1;
    Node insertedElements = nm->mkNode(SET_SINGLETON, node[0]);

    for (size_t i = 1; i < setNodeIndex; ++i)
    {
      Node singleton = nm->mkNode(SET_SINGLETON, node[i]);
      insertedElements =
          nm->mkNode(kind::SET_UNION, insertedElements, singleton);
    }
    return RewriteResponse(
        REWRITE_AGAIN,
        nm->mkNode(kind::SET_UNION, insertedElements, node[setNodeIndex]));
  }
  else if (k == kind::SET_SUBSET)
  {
    // rewrite (A subset-or-equal B) as (A union B = B)
    return RewriteResponse(
        REWRITE_AGAIN,
        nm->mkNode(kind::EQUAL,
                   nm->mkNode(kind::SET_UNION, node[0], node[1]),
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

RewriteResponse TheorySetsRewriter::postRewriteMap(TNode n)
{
  Assert(n.getKind() == kind::SET_MAP);
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n[1].getKind();
  switch (k)
  {
    case SET_EMPTY:
    {
      TypeNode rangeType = n[0].getType().getRangeType();
      // (set.map f (as set.empty (Set T1)) = (as set.empty (Set T2))
      Node ret = nm->mkConst(EmptySet(nm->mkSetType(rangeType)));
      return RewriteResponse(REWRITE_DONE, ret);
    }
    case SET_SINGLETON:
    {
      // (set.map f (set.singleton x)) = (set.singleton (f x))
      Node mappedElement = nm->mkNode(APPLY_UF, n[0], n[1][0]);
      Node ret = nm->mkNode(SET_SINGLETON, mappedElement);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case SET_UNION:
    {
      // (set.map f (set.union A B)) = (set.union (set.map f A) (set.map f B))
      Node a = nm->mkNode(SET_MAP, n[0], n[1][0]);
      Node b = nm->mkNode(SET_MAP, n[0], n[1][1]);
      Node ret = nm->mkNode(SET_UNION, a, b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteFilter(TNode n)
{
  Assert(n.getKind() == kind::SET_FILTER);
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n[1].getKind();
  switch (k)
  {
    case SET_EMPTY:
    {
      // (set.filter p (as set.empty (Set T)) = (as set.empty (Set T))
      return RewriteResponse(REWRITE_DONE, n[1]);
    }
    case SET_SINGLETON:
    {
      // (set.filter p (set.singleton x)) =
      //       (ite (p x) (set.singleton x) (as set.empty (Set T)))
      Node empty = nm->mkConst(EmptySet(n.getType()));
      Node condition = nm->mkNode(APPLY_UF, n[0], n[1][0]);
      Node ret = nm->mkNode(ITE, condition, n[1], empty);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }
    case SET_UNION:
    {
      // (set.filter p (set.union A B)) =
      //   (set.union (set.filter p A) (set.filter p B))
      Node a = nm->mkNode(SET_FILTER, n[0], n[1][0]);
      Node b = nm->mkNode(SET_FILTER, n[0], n[1][1]);
      Node ret = nm->mkNode(SET_UNION, a, b);
      return RewriteResponse(REWRITE_AGAIN_FULL, ret);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteFold(TNode n)
{
  Assert(n.getKind() == kind::SET_FOLD);
  NodeManager* nm = NodeManager::currentNM();
  Node f = n[0];
  Node t = n[1];
  Kind k = n[2].getKind();
  switch (k)
  {
    case SET_EMPTY:
    {
      // ((set.fold f t (as set.empty (Set T))) = t
      return RewriteResponse(REWRITE_DONE, t);
    }
    case SET_SINGLETON:
    {
      // (set.fold f t (set.singleton x)) = (f x t)
      Node x = n[2][0];
      Node f_x_t = nm->mkNode(APPLY_UF, f, x, t);
      return RewriteResponse(REWRITE_AGAIN_FULL, f_x_t);
    }
    case SET_UNION:
    {
      // (set.fold f t (set.union B C)) = (set.fold f (set.fold f t A) B))
      Node A = n[2][0];
      Node B = n[2][1];
      Node foldA = nm->mkNode(SET_FOLD, f, t, A);
      Node fold = nm->mkNode(SET_FOLD, f, foldA, B);
      return RewriteResponse(REWRITE_AGAIN_FULL, fold);
    }

    default: return RewriteResponse(REWRITE_DONE, n);
  }
}

RewriteResponse TheorySetsRewriter::postRewriteGroup(TNode n)
{
  Assert(n.getKind() == kind::RELATION_GROUP);
  Node A = n[0];
  Kind k = A.getKind();
  if (k == SET_EMPTY || k == SET_SINGLETON)
  {
    NodeManager* nm = NodeManager::currentNM();
    // - ((_ rel.group n1 ... nk) (as set.empty (Relation T))) =
    //    (rel.singleton (as set.empty (Relation T) ))
    // - ((_ rel.group n1 ... nk) (set.singleton x)) =
    //      (set.singleton (set.singleton x))
    Node singleton = nm->mkNode(SET_SINGLETON, A);
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
  Assert(n.getKind() == kind::RELATION_AGGREGATE);
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
  Assert(n.getKind() == RELATION_PROJECT);
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
