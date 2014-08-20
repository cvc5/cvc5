/*********************                                                        */
/*! \file uf_proof.cpp
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

#include "proof/theory_proof.h"
#include "proof/proof_manager.h"
#include "proof/bitvector_proof.h"
#include "theory/bv/theory_bv.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;

BitVectorProof::BitVectorProof(theory::bv::TheoryBV* bv, TheoryProofEngine* proofEngine)
  : TheoryProof(bv, proofEngine)
  , d_resolutionProof()
  , d_cnfProof()
{}
  


void LFSCBitVectorProof::printTerm(Expr term, std::ostream& os) {
  // TODO print bit-vector term
  os << "bvterm "; 
}

void LFSCBitVectorProof::printTheoryLemmaProof(std::vector<Expr>& lemma, std::ostream& os, std::ostream& paren) {
  os << ";; TODO print bit-vector lemma proof \n";
  os << "(clausify_false trust)\n"; 
}
void LFSCBitVectorProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  os << ";; TODO print bit-vector declarations \n";
}
void LFSCBitVectorProof::printBitblasting(std::ostream& os, std::ostream& paren) {
  os << ";; TODO print bit-blasting \n";
}
