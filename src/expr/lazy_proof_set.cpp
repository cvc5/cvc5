/*********************                                                        */
/*! \file lazy_proof_set.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof set utility
 **/

#include "expr/lazy_proof_set.h"

namespace CVC4 {

LazyCDProofSet::LazyCDProofSet(ProofNodeManager* pnm,
                               context::Context* c,
                               std::string namePrefix)
    : d_pnm(pnm),
      d_contextUse(c ? c : &d_context),
      d_pfs(d_contextUse),
      d_namePrefix(namePrefix)
{
}

LazyCDProof* LazyCDProofSet::allocateProof(bool isCd)
{
  std::stringstream ss;
  ss << d_namePrefix << "_" << d_pfs.size();
  std::shared_ptr<LazyCDProof> pf = std::make_shared<LazyCDProof>(
      d_pnm, nullptr, isCd ? d_contextUse : nullptr, ss.str());
  d_pfs.push_back(pf);
  return pf.get();
}

}  // namespace CVC4
