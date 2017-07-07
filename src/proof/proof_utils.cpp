/*********************                                                        */
/*! \file proof_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Guy Katz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "proof/proof_utils.h"
#include "theory/theory.h"

namespace CVC4 {
namespace utils {

void collectAtoms(TNode node, std::set<Node>& seen) {
  if (seen.find(node) != seen.end())
    return;
  if (theory::Theory::theoryOf(node) != theory::THEORY_BOOL || node.isVar()) {
      seen.insert(node);
      return;
  }

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectAtoms(node[i], seen);
  }
}

std::string toLFSCKind(Kind kind) {
  switch(kind) {
    // core kinds
  case kind::OR : return "or";
  case kind::AND: return "and";
  case kind::XOR: return "xor";
  case kind::EQUAL: return "=";
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
  case kind::BITVECTOR_UDIV_TOTAL :
    return "bvudiv";
  case kind::BITVECTOR_UREM :
  case kind::BITVECTOR_UREM_TOTAL :
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

std::string toLFSCKindTerm(Expr node) {
  Kind k = node.getKind();
  if( k==kind::EQUAL ){
    if( node[0].getType().isBoolean() ){
      return "iff";
    }else{
      return "=";
    }
  }else{
    return toLFSCKind( k );
  }
}

} /* namespace CVC4::utils */
} /* namespace CVC4 */
