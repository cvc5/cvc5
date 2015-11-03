/*********************                                                        */
/*! \file expr_patterns.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Expr patterns.
 **
 ** Expr patterns.
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"

namespace CVC4 {
namespace expr {
namespace pattern {

/** Boolean operators */
static Node AND(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::AND, a, b);
}

static Node OR(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b);
}

static Node OR(TNode a, TNode b, TNode c) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b, c);
}

static Node NOT(TNode a) {
  return NodeManager::currentNM()->mkNode(kind::NOT, a);
}

/** Theory operators */
static Node MEMBER(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::MEMBER, a, b);
}

static Node SINGLETON(TNode a) {
  return NodeManager::currentNM()->mkNode(kind::SINGLETON, a);
}

static Node EQUAL(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::EQUAL, a, b);
}

static Node CARD(TNode a) {
  return NodeManager::currentNM()->mkNode(kind::CARD, a);
}

}/* CVC4::expr::pattern namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
