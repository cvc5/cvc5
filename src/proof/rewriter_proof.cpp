/*********************                                                        */
/*! \file rewriter_proof.cpp
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

#include "proof/rewriter_proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "proof/proof_utils.h"

using namespace CVC4;

unsigned RewriterProof::d_rewriteIdCount = 0;


RewriterProof::RewriterProof()
  : d_rewriteMap()
  , d_rewriteStack()
  , d_rewriteProofs()
{}

RewriterProof::~RewriterProof() {
  Assert (d_rewriteStack.empty());
  for (unsigned i = 0; i < d_rewriteProofs.size(); ++i) {
    delete d_rewriteProofs[i];
  }
}

void RewriterProof::finalizeRewrite(Expr from, Expr to) {
  Debug("proof-rewrite") << "RewriterProof::finalizeRewriteProof: " << from <<" => " << to<<"\n"; 
  Assert (from != to);
  if (d_rewriteStack.empty()) {
    // this means that we need to do an identity op rewrite
    Assert (from.getNumChildren() == to.getNumChildren() &&
            from.getKind() == to.getKind());
    Assert (from.getNumChildren() > 0);

    // make sure we have the corresponding children proofs
    for (unsigned i = 0; i < from.getNumChildren(); ++i) {
      if (hasRewrite(from[i], to[i]))
          continue;

      Assert (from[i] == to[i]);
      RewriteProof* pf = new IdentityRewriteProof(from[i]);
    }
    RewriteProof* pf = new IdentityOpRewriteProof(from, to);
    return;
  }
  
  // we don't need to add a separate rewrite proof for this
  if (d_rewriteStack.size() == 1) {
    RewriteProof* rule = d_rewriteStack[0];
    Assert (rule->from() == from && rule->to() == to);
    return;
  }

  RewriteProof* prev = d_rewriteStack[0];
  Assert (prev->from() == from);
  for (unsigned i = 1; i < d_rewriteStack.size(); ++i) {
    RewriteProof* curr = d_rewriteStack[i];
    RewriteProof* trans = new TransitivityRewriteProof(prev, curr);
    prev = curr;
  }
  Assert (prev->to() == to);
}

void RewriterProof::pushRewriteRule(Expr from, Expr to, RewriteTag tag) {
  Debug("proof-rewrite") << "RewriterProof::pushRewriteRule " << tag <<"\n";
  Debug("proof-rewrite") << "      " << from <<" => " << to<<"\n"; 
  RewriteProof* pf = NULL;
  switch (tag) {
  case BvXnorEliminate:
  case BvXorZero:
  case BvXorOne:
    // FIXME will this always be identity?
    // if yes can change the "leaf" rewrites
    pf = new BvRewriteOp2Proof(tag, new IdentityRewriteProof(from[0]),
                                    new IdentityRewriteProof(from[1]));
    break;
  case BvNotIdemp:
    pf = new BvRewriteOp1Proof(tag, new IdentityRewriteProof(from[0]));
    break;
  default:
    Unreachable("Should not push this rewrite rule: ", tag);
  }
  Assert (pf != NULL);
  d_rewriteStack.push_back(pf);
}

void RewriterProof::registerRewriteProof(RewriteProof* proof) {
  Debug("proof-rewrite") << "RewriterProof::registerRewriteProof " << proof->tag() <<"\n";
  Debug("proof-rewrite") << "      " << proof->from() <<" => " << proof->to()<<"\n"; 

  Assert (d_rewriteProofs.size() == proof->id());
  d_rewriteProofs.push_back(proof);
  Rewrite rw (proof->from(), proof->to());
  Assert (d_rewriteMap.find(rw) == d_rewriteMap.end());
  d_rewriteMap[rw] = proof;
}

bool RewriterProof::hasRewrite(Expr from, Expr to) {
  return d_rewriteMap.find(Rewrite(from, to)) != d_rewriteMap.end();
}

 
RewriteProof* RewriterProof::getRewrite(RewriteId id) {
  Assert (id < d_rewriteProofs.size());
  return d_rewriteProofs[id];
}
 
RewriteProof* RewriterProof::getRewrite(Expr from, Expr to) {
  Assert (hasRewrite(from, to));
  return d_rewriteMap[Rewrite(from, to)];
}
 
std::string RewriterProof::rewriteName(unsigned id) {
  std::ostringstream os;
  os << "rw"<<id;
  return os.str();
}

std::string LFSCRewriterProof::rewriteTagToString(RewriteTag tag) {
  switch(tag) {
  case BvXorZero:
    return "bv_xor_zero";
  case BvXorOne:
    return "bv_xor_one";
  case BvNotIdemp:
    return "bv_not_idemp";
  case BvXnorEliminate:
    return "bv_xnor_eliminate";
  default:
    Unreachable("Unknown rewrite rule", tag);    
  }
  Unreachable("Unknown rewrite rule", tag);
}

void LFSCRewriterProof::printRewrittenAssertios(std::ostream& os, std::ostream& paren) {
  
}

RewriteProof::RewriteProof(RewriteTag tag, Expr from, Expr to)
  : d_from(from)
  , d_to(to)
  , d_tag(tag)
  , d_id(RewriterProof::newId()) {
  ProofManager::currentPM()->getRewriterProof()->registerRewriteProof(this); 
}

RewriteProof::RewriteProof(RewriteTag tag)
  : d_tag(tag)
  , d_id(RewriterProof::newId()) {
  ProofManager::currentPM()->getRewriterProof()->registerRewriteProof(this); 
}



void IdentityRewriteProof::printLFSC(std::ostream& os, std::ostream& paren) {
  ProofManager* pm = ProofManager::currentPM();
  Assert (d_to == d_from);
  os << "(@ "<<RewriterProof::rewriteName(d_id) <<" ";
  if (d_from.getType().isBoolean()) {
    os << " (rw_formula_id ";
  } else {
    os << " (rw_term_id ";
    pm->getTheoryProofEngine()->printSort(d_from.getType(), os);
    os <<" ";
  }

  pm->getTheoryProofEngine()->printLetTerm(d_from, os);
  paren<<")";
}

void IdentityOpRewriteProof::printLFSC(std::ostream& os, std::ostream& paren) {
  Assert (d_from.getNumChildren() != 0 &&
          d_from.getNumChildren() == d_to.getNumChildren() &&
          d_from.getKind() == d_to.getKind());

  ProofManager* pm = ProofManager::currentPM();
  RewriterProof* rp = pm->getRewriterProof();
  
  if (d_from.getNumChildren() == 1) {
    os << "(@ " << RewriterProof::rewriteName(d_id);
    if (d_from.getType().isBoolean()) {
      // if it's boolean it's either a predicate or a formula
      if (d_from[0].getType().isBoolean()) {
        os << " (rw_formula_op1_id ";
      } else {
        os << " (rw_pred1_id ";
      }
    } else {
      os <<" (rw_op1_id ";
    }
    RewriteId t_id = rp->getRewrite(d_from[0], d_to[0])->id();
    pm->getTheoryProofEngine()->printSort(d_from.getType(), os);
    os << " _ _ ";
    os << RewriterProof::rewriteName(t_id) << utils::toLFSCKind(d_from.getKind()) <<")";
    return;
  }

  // FIXME this will not always hold...
  Assert (d_from.getNumChildren() == 2);

  
  RewriteId t1_id = rp->getRewrite(d_from[0], d_to[0])->id();
  RewriteId t2_id = rp->getRewrite(d_from[1], d_to[1])->id();
  
  os << "(@ " << RewriterProof::rewriteName(d_id);


  if (d_from.getKind() == kind::EQUAL) {
    os << " (rw_eq_id ";
  } else if (d_from.getType().isBoolean()) {
    if (d_from[0].getType().isBoolean()) {
      os << " (rw_formula_op2_id ";
    } else {
      os << " (rw_pred2_id ";
    }
  } else {
    os <<" (rw_op2_id ";
  }
  
  pm->getTheoryProofEngine()->printSort(d_from.getType(), os);
  os << " _ _ _ _ ";
  os << RewriterProof::rewriteName(t1_id) <<" ";
  os << RewriterProof::rewriteName(t2_id) <<" ";
  os << utils::toLFSCKind(d_from.getKind()) <<")";

  paren <<")";
}


BvRewriteOp2Proof::BvRewriteOp2Proof(RewriteTag tag, RewriteProof* p1, RewriteProof* p2)
  : RewriteProof(BvXorOne)
  , pf1(p1)
  , pf2(p2)
{

  // this is mostly for debugging purposes
  switch(tag) {
  case BvXorOne: 
    d_from = utils::mkExpr(kind::BITVECTOR_XOR, pf1->from(), pf2->from());
    d_to = utils::mkExpr(kind::BITVECTOR_NOT, pf1->to());
    break;
  case BvXorZero:
    d_from = utils::mkExpr(kind::BITVECTOR_XOR, pf1->from(), pf2->from());
    d_to = pf1->to();
    break;

  case BvXnorEliminate:
    d_from = utils::mkExpr(kind::BITVECTOR_XNOR, pf1->from(), pf2->from());
    d_to = utils::mkExpr(kind::BITVECTOR_NOT, utils::mkExpr(kind::BITVECTOR_XOR, pf1->to(), pf2->to()));
    break;
  default:
    Unreachable("Unknown rewrite tag", tag);
  }
}

void BvRewriteOp2Proof::printLFSC(std::ostream& os, std::ostream& paren) {
  Assert (d_from.getKind() == kind::BITVECTOR_XOR);
  RewriteId t1_id = pf1->id();
  RewriteId t2_id = pf2->id();
  unsigned size = utils::getSize(d_from);
  os <<"(@ " << RewriterProof::rewriteName(d_id) <<" "<< LFSCRewriterProof::rewriteTagToString(d_tag) << " " << size <<" _ _ _ _ "<<RewriterProof::rewriteName(t1_id) <<" " << RewriterProof::rewriteName(t2_id) <<")";
  paren <<")";
}

BvRewriteOp1Proof::BvRewriteOp1Proof(RewriteTag tag, RewriteProof* p1)
  : RewriteProof(tag)
  , pf1(p1)
{
  switch(tag) {
  case BvNotIdemp:
    d_from = utils::mkExpr(kind::BITVECTOR_NOT, utils::mkExpr(kind::BITVECTOR_NOT, pf1->from()));
    d_to = pf1->to();
    break;
  default:
    Unreachable("Unknown rewrite tag", tag);
  }
}

void BvRewriteOp1Proof::printLFSC(std::ostream& os, std::ostream& paren) {
  RewriteId rw1_id = pf1->id();
  unsigned size = utils::getSize(d_from);
  os <<"(@ " << RewriterProof::rewriteName(d_id) <<" "<< LFSCRewriterProof::rewriteTagToString(d_tag) <<" "<< size <<" _ _ "<<RewriterProof::rewriteName(rw1_id) <<")";
  paren <<")";
}

        
TransitivityRewriteProof::TransitivityRewriteProof(RewriteProof* p1, RewriteProof* p2)
  : RewriteProof(TransitivityRewrite)
  , pf1(p1)
  , pf2(p2)
{
  d_from = pf1->from();
  Assert (pf1->to() == pf2->from());
  d_to = pf2->to();
}

void TransitivityRewriteProof::printLFSC(std::ostream& os, std::ostream& paren) {
  os <<"(@ " << RewriterProof::rewriteName(d_id); 
  if (d_from.getType().isBoolean()) {
    os << " (rw_formula_trans _ _ _ ";
  } else {
    os << " (rw_term_trans ";
    ProofManager::currentPM()->getTheoryProofEngine()->printSort(d_from.getType(), os);
    os <<" _ _ _ ";
  }
  RewriteId id1 = pf1->id();
  RewriteId id2 = pf2->id();
  os << RewriterProof::rewriteName(id1) <<" " << RewriterProof::rewriteName(id2) <<")";
  paren<<")";
}

