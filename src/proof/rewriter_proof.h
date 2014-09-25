/*********************                                                        */
/*! \file rewriter_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter proof
 **
 ** Rewriter proof
 **/

#include "cvc4_private.h"

#ifndef __CVC4__BITVECTOR__PROOF_H
#define __CVC4__BITVECTOR__PROOF_H

#include <iostream>
#include <ext/hash_map>
#include <sstream>
#include "expr/expr.h"

namespace CVC4 {

enum RewriteTag {
  BvXorZero,
  BvXorOne,
  BvNotIdemp,
  BVNorEliminate,
  // Build-in rewrites for LFSC
  TermIdentity, // (rw t t) 
  TransitivityRewrite, // (rw t1 t2) (rw t2 t3) => (rw t1 t3)
  // BinaryOpIdentity, // (rw a a') (rw b b') => (rw (op a b) (op a' b'))
  // UnaryOpIdentity,
  // PredicateIdentity,
  //  EqIndentity
  IntentityOpRewrite,
  IdentityRewrite
};

class RewriteRule {
  RewriteTag tag;
  Expr from;
  Expr to;
public:
  RewriteRule(RewriteTag t, Expr from, Expr to)
    : tag(t)
    , from(from)
    , to(to)
    , id(++RewriteRule::d_idCount)
  {}
  
  // copy constructor copies the id
  RewriteRule(const RewriteRule& other)
    : tag(other.tag)
    , from(other.from)
    , to(other.to)
    , id(other.id)
  {}
  bool operator==(const RewriteRule& other) const {
    return tag == other.tag && from == other.from && to == other.to; 
  }
};

typedef unsigned RewriteId;

template< RewriteTag T> 
class RewriteRuleProof {
  Expr from;
  Expr to;
  std::vector<RewriteId> args;
public:
   RewriteRuleProof(Expr from, Expr to)
    : tag(t)
    , from(from)
    , to(to)
    , id(RewriterProof::newId())
  {
    build();
  }

  void build();
  void printLFSC(ostream& os, ostream& paren);
};


typedef __gnu_cxx::hash_map<Expr, RewriteRule, ExprHashFunction> RewriteMap; 
typedef std::vector<RewriteRule> RewriteStack;

class RewriterProof {
  static std::string toLFSCRewriteName(RewriteRule& rw);

  RewriteStack d_rewriteStack;
  RewriteMap d_rewriteMap;

  bool hasRewrite(Expr from) const;
  RewriteRule& getRewrite(Expr from);
  /** 
   * If it doesn't already exist, creates an identity
   * rewrite (Rewrite t t)
   * 
   * @param from 
   * 
   * @return the rewrite id
   */
  RewriteId addIdentityRewrite(Expr from);
  /** 
   * If it doesn't already exist, create a rewrite
   * that assuming each child rewrites to t' establishes
   * the operation rewrites to the op over t'
   * 
   * @param from 
   * 
   * @return 
   */
  RewriteId addIdentityOpRewrite(Expr from);
  /** 
   * If it doesn't already exist create a transitivity rewrite
   * 
   * @param from 
   * @param to 
   * 
   * @return 
   */
  RewriteId addTransRewrite(Expr t1, Expr t2, Expr t3);
public:
  RewriterProof();
  void finalizeRewrite(Expr from, Expr to);
  void pushRewriteRule(Expr from, Expr to, RewriteTag tag);
  virtual void printRewriteProof(Expr formula, ostream& os, ostream& paren) = 0;
};

class LFSCRewriterProof: public RewriterProof {
public:
  LFSCRewriterProof()
    : RewriterProof()
  {}
  virtual void printRewriteProof(Expr formula, ostream& os, ostream& paren);
}; 


template<> inline
void RewriteRule<IdentityRewrite>::printLFSC(ostream& os, ostream& paren) {
  ProofManager* pm = ProofManager::currentPM();
  Assert (to == from);
  os << "(@ "<<rewriteName(id) <<" ";
  os << "(rw_term_id ";
  pm->getTheoryProof()->printSort(from.getType(), os);
  os <<" ";
  pm->getTheoryProof()->printLetTerm(from, os);
  paren<<")";
}


template<> inline
void RewriteRule<IndentityOpRewrite>::printLFSC(ostream& os, ostream& paren) {
  Assert (from.getNumChildren() != 0 &&
          from.getNumChildren() == to.getNumChildren() &&
          from.getKind() == to.getKind());

  ProofManager* pm = ProofManager::currentPM();
  
  if (from.getNumChildren() == 1) {
    os << "(@ " << rewriteName(id);
    if (from.getType().isBoolean()) {
      os << " (rw_pred1_id ";
    } else {
      os <<" (rw_op1_id ";
    }

    RewriteId t_id = getRewriteId(from[0]);
    pm->getTheoryProof()->printSort(from.getType(), os);
    os << " _ _ ";
    os << << rewriteName(t_id) << toLFSCBVKind(from.getKind()) <<")";
  }

  // FIXME this will not always hold...
  Assert (from.getNumChildren() == 2);

  
  RewriteId t1_id = getRewriteId(from[0]);
  RewriteId t2_id = getRewriteId(from[1]);
  
  os << "(@ " << rewriteName(id);


  if (from.getKind() == kind::EQUAL) {
    os << " (rw_eq_id ";
  } else if (from.getType().isBoolean()) {
    // FIXME this will fail soon
    if (from[0].getType().isBoolean()) {
      //      os << " (rw_formula
    }
    Assert (!from[0].getType().isBoolean());
    os << " (rw_pred2_id ";
  } else {
    os <<" (rw_op2_id ";
  }
  
  pm->getTheoryProof()->printSort(from.getType(), os);
  os << " _ _ _ _ ";
  os << rewriteName(t1_id) <<" ";
  os << rewriteName(t2_id) <<" ";
  os << toLFSCKind(from.getKind()) <<")";

  paren <<")";
}


template<> inline
void RewriteRule<BvXorZero>::printLFSC(ostream& os, ostream& paren) {
  Assert (from.getKind() == kind::BITVECTOR_XOR);
  Expr t1 = from[0];
  Expr t2 = from[1];
  unsigned size = utils::getSize(from);
  RewriteId t1_id = getRewriteId(t1);
  RewriteId t2_id = getRewriteId(t2);
  os <<"(@ " << rewriteName(id) <<" (xor_zero "<< size <<" " << _ _ _ _ <<rewriteName(t1_id) <<" " << rewriteName(t2_id) <<")";
  paren <<")"
}

template<> inline
void RewriteRule<BvXorOne>::printLFSC(ostream& os, ostream& paren) {
  Assert (from.getKind() == kind::BITVECTOR_XOR);
  Expr t1 = from[0];
  Expr t2 = from[1];
  unsigned size = utils::getSize(from);
  RewriteId t1_id = getRewriteId(t1);
  RewriteId t2_id = getRewriteId(t2);
  os <<"(@ " << rewriteName(id) <<" (xor_one "<< size <<" " << _ _ _ _ <<rewriteName(t1_id) <<" " << rewriteName(t2_id) <<")";
  paren <<")"
}




}/* CVC4 namespace */

#endif /* __CVC4__REWRITER__PROOF_H */
