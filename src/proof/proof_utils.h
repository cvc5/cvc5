/*********************                                                        */
/*! \file proof_utils.h
** \verbatim
** Original author: Liana Hadarean
** Major contributors: none
** Minor contributors (to current version): none
** This file is part of the CVC4 project.
** Copyright (c) 2009-2014  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief [[ Add one-line brief description here ]]
**
** [[ Add lengthier description here ]]
** \todo document this file
**/

#include "cvc4_private.h"

#pragma once 

#include <set>
#include <vector>
#include <sstream>
#include "expr/node_manager.h"

namespace CVC4 {

typedef __gnu_cxx::hash_set<Expr, ExprHashFunction> ExprSet;
  
namespace utils {

  inline std::string toLFSCKind(Kind kind) {
    switch(kind) {
      // core kinds
    case kind::OR : return "or";
    case kind::AND: return "and";
    case kind::XOR: return "xor";
    case kind::EQUAL: return "=";
    case kind::IFF: return "iff";
    case kind::IMPLIES: return "impl";
    case kind::NOT: return "not";

      // bit-vector kinds
    case kind::BITVECTOR_AND :
      return "bvand"; 
    case kind::BITVECTOR_OR :
      return "bvor"; 
    case kind::BITVECTOR_XOR :
      return "bvxor"; 
    case kind::BITVECTOR_NAND :
      return "bvnand"; 
    case kind::BITVECTOR_NOR :
      return "bvnor"; 
    case kind::BITVECTOR_XNOR :
      return "bvxnor"; 
    case kind::BITVECTOR_COMP :
      return "bvcomp"; 
    case kind::BITVECTOR_MULT :
      return "bvmul";
    case kind::BITVECTOR_PLUS :
      return "bvadd"; 
    case kind::BITVECTOR_SUB :
      return "bvsub";
    case kind::BITVECTOR_UDIV :
      return "bvudiv";
    case kind::BITVECTOR_UREM :
      return "bvurem"; 
    case kind::BITVECTOR_SDIV :
      return "bvsdiv"; 
    case kind::BITVECTOR_SREM :
      return "bvsrem";
    case kind::BITVECTOR_SMOD :
      return "bvsmod"; 
    case kind::BITVECTOR_SHL :
      return "bvshl"; 
    case kind::BITVECTOR_LSHR :
      return "bvlshr";
    case kind::BITVECTOR_ASHR :
      return "bvashr";
    case kind::BITVECTOR_CONCAT :
      return "concat"; 
    case kind::BITVECTOR_NEG :
      return "bvneg"; 
    case kind::BITVECTOR_NOT :
      return "bvnot"; 
    case kind::BITVECTOR_ROTATE_LEFT :
      return "rotate_left"; 
    case kind::BITVECTOR_ROTATE_RIGHT :
      return "rotate_right";
    case kind::BITVECTOR_ULT :
      return "bvult"; 
    case kind::BITVECTOR_ULE :
      return "bvule"; 
    case kind::BITVECTOR_UGT :
      return "bvugt";
    case kind::BITVECTOR_UGE :
      return "bvuge";
    case kind::BITVECTOR_SLT :
      return "bvslt"; 
    case kind::BITVECTOR_SLE :
      return "bvsle"; 
    case kind::BITVECTOR_SGT :
      return "bvsgt"; 
    case kind::BITVECTOR_SGE :
      return "bvsge"; 
    case kind::BITVECTOR_EXTRACT :
      return "extract"; 
    case kind::BITVECTOR_REPEAT :
      return "repeat"; 
    case kind::BITVECTOR_ZERO_EXTEND :
      return "zero_extend";
    case kind::BITVECTOR_SIGN_EXTEND :
      return "sign_extend";
    default:
      Unreachable();
    }
  }


  inline unsigned getExtractHigh(Expr node) {
    return node.getOperator().getConst<BitVectorExtract>().high;
  }

  inline unsigned getExtractLow(Expr node) {
    return node.getOperator().getConst<BitVectorExtract>().low;
  }

  inline unsigned getSize(Type type) {
    BitVectorType bv(type); 
    return bv.getSize();
  }


  inline unsigned getSize(Expr node) {
    Assert (node.getType().isBitVector());
    return getSize(node.getType());
  }

  inline Expr mkTrue() {
    return NodeManager::currentNM()->toExprManager()->mkConst<bool>(true);
  }

  inline Expr mkFalse() {
    return NodeManager::currentNM()->toExprManager()->mkConst<bool>(false);
  }
  inline BitVector mkBitVectorOnes(unsigned size) {
    Assert(size > 0); 
    return BitVector(1, Integer(1)).signExtend(size - 1); 
  }

  inline Expr mkExpr(Kind k , Expr expr) {
    return NodeManager::currentNM()->toExprManager()->mkExpr(k, expr);
  }
  inline Expr mkExpr(Kind k , Expr e1, Expr e2) {
    return NodeManager::currentNM()->toExprManager()->mkExpr(k, e1, e2);
  }
  inline Expr mkExpr(Kind k , std::vector<Expr>& children) {
    return NodeManager::currentNM()->toExprManager()->mkExpr(k, children);
  }
  
  
  inline Expr mkOnes(unsigned size) {
    BitVector val = mkBitVectorOnes(size); 
    return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(val); 
  }

  inline Expr mkConst(unsigned size, unsigned int value) {
    BitVector val(size, value);
    return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(val); 
  }

  inline Expr mkConst(const BitVector& value) {
    return NodeManager::currentNM()->toExprManager()->mkConst<BitVector>(value);
  }

  inline Expr mkOr(const std::vector<Expr>& nodes) {
    std::set<Expr> all;
    all.insert(nodes.begin(), nodes.end());
    Assert(all.size() != 0 ); 

    if (all.size() == 1) {
      // All the same, or just one
      return nodes[0];
    }
  
  
    NodeBuilder<> disjunction(kind::OR);
    std::set<Expr>::const_iterator it = all.begin();
    std::set<Expr>::const_iterator it_end = all.end();
    while (it != it_end) {
      disjunction << Node::fromExpr(*it);
      ++ it;
    }

    Node res = disjunction;
    return res.toExpr(); 
  }/* mkOr() */

                 
  inline Expr mkAnd(const std::vector<Expr>& conjunctions) {
    std::set<Expr> all;
    all.insert(conjunctions.begin(), conjunctions.end());

    if (all.size() == 0) {
      return mkTrue(); 
    }
  
    if (all.size() == 1) {
      // All the same, or just one
      return conjunctions[0];
    }
  

    NodeBuilder<> conjunction(kind::AND);
    std::set<Expr>::const_iterator it = all.begin();
    std::set<Expr>::const_iterator it_end = all.end();
    while (it != it_end) {
      conjunction << Node::fromExpr(*it);
      ++ it;
    }

    Node res = conjunction; 
    return res.toExpr();
  }/* mkAnd() */

  inline Expr mkSortedExpr(Kind kind, const std::vector<Expr>& children) {
    std::set<Expr> all;
    all.insert(children.begin(), children.end());

    if (all.size() == 0) {
      return mkTrue(); 
    }
  
    if (all.size() == 1) {
      // All the same, or just one
      return children[0];
    }
  

    NodeBuilder<> res(kind);
    std::set<Expr>::const_iterator it = all.begin();
    std::set<Expr>::const_iterator it_end = all.end();
    while (it != it_end) {
      res << Node::fromExpr(*it);
      ++ it;
    }

    return ((Node)res).toExpr();
  }/* mkSortedNode() */

  inline const bool getBit(Expr expr, unsigned i) {
    Assert (i < utils::getSize(expr) && 
	    expr.isConst()); 
    Integer bit = expr.getConst<BitVector>().extract(i, i).getValue();
    return (bit == 1u); 
  }


}
}
