/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Kshitij Bansal, Paul Meng
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sets theory rewriter.
 */

#include "theory/sets/theory_sets_rewriter.h"

#include "expr/attribute.h"
#include "expr/dtype_cons.h"
#include "options/sets_options.h"
#include "theory/sets/normal_form.h"
#include "theory/sets/rels_utils.h"
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {
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
    else if (node[1].getKind() == kind::SET_MINUS && node[1][0] == node[0])
    {
      // (setminus A (setminus A B)) = (intersection A B)
      Node intersection = nm->mkNode(SET_INTER, node[0], node[1][1]);
      return RewriteResponse(REWRITE_AGAIN, intersection);
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
  }  // kind::INTERSECION

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
      return RewriteResponse(
          REWRITE_DONE, nm->mkConst(CONST_RATIONAL, Rational(elements.size())));
    }
    else if (node[0].getKind() == kind::SET_SINGLETON)
    {
      return RewriteResponse(REWRITE_DONE,
                             nm->mkConst(CONST_RATIONAL, Rational(1)));
    }
    else if (node[0].getKind() == kind::SET_UNION)
    {
      Node ret = NodeManager::currentNM()->mkNode(
          kind::MINUS,
          NodeManager::currentNM()->mkNode(
              kind::PLUS,
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
          kind::MINUS,
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

  case SET_MAP: return postRewriteMap(node);

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
        new_tuple_set.insert(RelsUtils::reverseTuple(*tuple_it));
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
          left_tuple.push_back(RelsUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          Trace("rels-debug") << "Sets::postRewrite processing right_it = " <<  *right_it << std::endl;
          std::vector<Node> right_tuple;
          for(int j = 0; j < right_len; j++) {
            right_tuple.push_back(RelsUtils::nthElementOfTuple(*right_it,j));
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
          left_tuple.push_back(RelsUtils::nthElementOfTuple(*left_it,i));
        }
        std::set<Node>::iterator right_it = right.begin();
        int right_len = (*right_it).getType().getTupleLength();
        while(right_it != right.end()) {
          if(RelsUtils::nthElementOfTuple(*left_it,left_len-1) == RelsUtils::nthElementOfTuple(*right_it,0)) {
            std::vector<Node> right_tuple;
            for(int j = 1; j < right_len; j++) {
              right_tuple.push_back(RelsUtils::nthElementOfTuple(*right_it,j));
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
        Node fst_mem = RelsUtils::nthElementOfTuple( *rel_mems_it, 0);
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
        Node fst_mem = RelsUtils::nthElementOfTuple( *rel_mems_it, 0);
        if( has_checked.find( fst_mem ) != has_checked.end() ) {
          ++rel_mems_it;
          continue;
        }
        has_checked.insert( fst_mem );
        std::set<Node> existing_mems;
        std::set<Node>::iterator rel_mems_it_snd = rel_mems.begin();
        while( rel_mems_it_snd != rel_mems.end() ) {
          Node fst_mem_snd = RelsUtils::nthElementOfTuple( *rel_mems_it_snd, 0);
          if( fst_mem == fst_mem_snd ) {
            existing_mems.insert( RelsUtils::nthElementOfTuple( *rel_mems_it_snd, 1) );
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

  default:
    break;
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
    TypeNode elementType = node[setNodeIndex].getType().getSetElementType();
    Node insertedElements = nm->mkSingleton(elementType, node[0]);

    for (size_t i = 1; i < setNodeIndex; ++i)
    {
      Node singleton = nm->mkSingleton(elementType, node[i]);
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

RewriteResponse TheorySetsRewriter::postRewriteMap(TNode n)
{
  Assert(n.getKind() == kind::SET_MAP);
  NodeManager* nm = NodeManager::currentNM();
  Kind k = n[1].getKind();
  TypeNode rangeType = n[0].getType().getRangeType();
  switch (k)
  {
    case SET_EMPTY:
    {
      // (set.map f (as set.empty (Set T1)) = (as set.empty (Set T2))
      Node ret = nm->mkConst(EmptySet(nm->mkSetType(rangeType)));
      return RewriteResponse(REWRITE_DONE, ret);
    }
    case SET_SINGLETON:
    {
      // (set.map f (set.singleton x)) = (set.singleton (f x))
      Node mappedElement = nm->mkNode(APPLY_UF, n[0], n[1][0]);
      Node ret = nm->mkSingleton(rangeType, mappedElement);
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

}  // namespace sets
}  // namespace theory
}  // namespace cvc5
