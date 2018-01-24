/*********************                                                        */
/*! \file sygus_sampler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_sampler
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H

#include <map>
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** SygusSampler
 * 
 */
class SygusSampler 
{
public:
  SygusSampler( QuantifiersEngine * qe, Node f, unsigned nsamples );
  ~SygusSampler(){}
  /** register */
  void registerTerm( Node n );
private:
  /** reference to quantifier engine */
  QuantifiersEngine * d_qe;
  /** samples */
  std::vector< std::vector< Node > > d_samples;
};


} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_SAMPLER_H */
