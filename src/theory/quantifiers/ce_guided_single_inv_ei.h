/*********************                                                        */
/*! \file ce_guided_single_inv_ei.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for inferring entailments for cegqi
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_ENTAILMENT_INFERENCE_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_ENTAILMENT_INFERENCE_H


#include "theory/quantifiers/ce_guided_single_inv.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
class CegEntailmentInfer {
private:
  QuantifiersEngine * d_qe;
  SingleInvocationPartition * d_sip;
public:
  CegEntailmentInfer( QuantifiersEngine * qe, SingleInvocationPartition * sip );
  virtual ~CegEntailmentInfer(){}
  
  bool getEntailedConjecture( Node& conj, Node& exp );
};


}
}
}

#endif
