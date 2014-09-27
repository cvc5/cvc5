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
  // Build-in rewrites for LFSC
  IdentityRewrite, // (rw t t) 
  IndentityOpRewrite,
  TransitivityRewrite, // (rw t1 t2) (rw t2 t3) => (rw t1 t3)


  // Bit-vector rewrites
  BvXorZero,
  BvXorOne,
  BvNotIdemp,
  BvXnorEliminate
};

/** 
 * A triple summarizing a rewrite rule.
 * 
 */
struct Rewrite {
  Expr from;
  Expr to;

  Rewrite(Expr from, Expr to)
    : from(from)
    , to(to)
  {}
  
   Rewrite(const Rewrite& other)
    : from(other.from)
    , to(other.to)
   {}
  bool operator==(const Rewrite& other) const {
    return from == other.from && to == other.to; 
  }
};

struct RewriteHashFunction {
  size_t operator()(const Rewrite& rw) const {
    // Compute individual hash values for two data members and combine them using XOR and bit shifting
    return ((ExprHashFunction()(rw.from) ^ (ExprHashFunction()(rw.to) << 1)) >> 1);
  }
};

typedef unsigned RewriteId;

/** 
 * All rewrite proofs have a tag and 
 * proves that from rewrites to to.
 * 
 */
class RewriteProof {
protected:
  Expr d_from;
  Expr d_to;
  RewriteTag d_tag;
  RewriteId d_id;
public:
  RewriteProof(RewriteTag tag, Expr from, Expr to);
  RewriteProof(RewriteTag tag);
 
  Expr from() {Assert (!d_from.isNull()); return d_from;}
  Expr to() { Assert (!d_to.isNull()); return d_to;}
  RewriteTag tag() { return d_tag;}
  unsigned id() { return d_id;}
  virtual void printLFSC(std::ostream& os, std::ostream& paren) = 0;
};


typedef __gnu_cxx::hash_map<Rewrite, RewriteProof*, RewriteHashFunction> RewriteMap; 
typedef std::vector<RewriteProof*> IdToRewriteProof;
typedef std::vector<RewriteProof*> RewriteStack;

class RewriterProof {
  static unsigned d_rewriteIdCount;
  friend class RewriteProof;
  
  RewriteMap d_rewriteMap;
  RewriteStack d_rewriteStack;
  IdToRewriteProof d_rewriteProofs;
  
  RewriteProof* getRewrite(RewriteId id);
  RewriteProof* getRewrite(Expr from, Expr to);
  bool hasRewrite(Expr from, Expr to);
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
  void registerRewriteProof(RewriteProof* proof);
  static unsigned newId() { return d_rewriteIdCount++; }
  static std::string rewriteName(unsigned id);
public:
  RewriterProof();
  ~RewriterProof();
  void finalizeRewrite(Expr from, Expr to);
  void pushRewriteRule(Expr from, Expr to, RewriteTag tag);
  virtual void printRewrittenAssertios(std::ostream& os, std::ostream& paren) = 0;
};

class LFSCRewriterProof: public RewriterProof {
  static std::string rewriteTagToString(RewriteTag tag);
  void printRewriteProof(Expr formula, std::ostream& os, std::ostream& paren) {}
public:
  LFSCRewriterProof()
    : RewriterProof()
  {}
  void printRewrittenAssertios(std::ostream& os, std::ostream& paren);
}; 

class IdentityRewriteProof : public RewriteProof {
public:
  IdentityRewriteProof(Expr expr)
    : RewriteProof(IdentityRewrite, expr, expr)
  {}
  virtual void printLFSC(std::ostream& os, std::ostream& paren);  
};

class IdentityOpRewriteProof : public RewriteProof {
public:
  IdentityOpRewriteProof(Expr f, Expr t)
    : RewriteProof(IndentityOpRewrite, f, t)
  {}
  virtual void printLFSC(std::ostream& os, std::ostream& paren);  
};


/** 
 * Rewrites a unary operator so it needs one rewrite proof
 * argument.
 * 
 */
class BvRewriteOp1Proof : public RewriteProof {
  RewriteProof* pf1;
public:
  BvRewriteOp1Proof(RewriteTag tag, RewriteProof* p1);
  virtual void printLFSC(std::ostream& os, std::ostream& paren);  
};

/** 
 * Rewrites a binary operator so it needs two rewrite proof
 * arguments.
 * 
 */
class BvRewriteOp2Proof : public RewriteProof {
  RewriteProof* pf1;
  RewriteProof* pf2;
public:
  BvRewriteOp2Proof(RewriteTag tag, RewriteProof* pf1, RewriteProof* pf2);
  virtual void printLFSC(std::ostream& os, std::ostream& paren);  
};


class TransitivityRewriteProof : public RewriteProof {
  RewriteProof* pf1;
  RewriteProof* pf2;
public:
  TransitivityRewriteProof(RewriteProof* pf1, RewriteProof* pf2);
  virtual void printLFSC(std::ostream& os, std::ostream& paren);  
};






}/* CVC4 namespace */

#endif /* __CVC4__REWRITER__PROOF_H */
