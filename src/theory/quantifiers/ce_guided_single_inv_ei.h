/*********************                                                        */
/*! \file ce_guided_single_inv_ei.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
