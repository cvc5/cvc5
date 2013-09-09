/*********************                                                        */
/*! \file expr_patterns.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Expr patterns.
 **
 ** Expr patterns.
 **/

#include "cvc4_private.h"

#pragma once

namespace CVC4 {
namespace expr {
namespace pattern {

static Node AND(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::AND, a, b);
}

static Node OR(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b);
}

static Node OR(TNode a, TNode b, TNode c) {
  return NodeManager::currentNM()->mkNode(kind::OR, a, b, c);
}

static Node IN(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::IN, a, b);
}

static Node EQUAL(TNode a, TNode b) {
  return NodeManager::currentNM()->mkNode(kind::EQUAL, a, b);
}

static Node NOT(TNode a) {
  return NodeManager::currentNM()->mkNode(kind::NOT, a);
}

}/* CVC4::expr::pattern namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
