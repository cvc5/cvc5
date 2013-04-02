/*********************                                                        */
/*! \file cnf_proof.h
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A manager for CnfProofs.
 **
 ** A manager for CnfProofs.
 **
 ** 
 **/

#include "cvc4_private.h"

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

} /* CVC4 namespace */
#endif /* __CVC4__CNF_PROOF_H */
