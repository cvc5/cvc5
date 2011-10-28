/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for CnfProofs.
 **
 ** A manager for CnfProofs.
 **
 ** 
 **/

#ifndef __CVC4__CNF_PROOF_H
#define __CVC4__CNF_PROOF_H

#include <iostream> 
namespace CVC4 {
namespace prop {
class CnfStream;
}
class CnfProof {
  CVC4::prop::CnfStream* d_cnfStream;
public:
  CnfProof(CVC4::prop::CnfStream* cnfStream);
};

} /* CVC4 namespace*/ 
#endif /* __CVC4__CNF_PROOF_H */
