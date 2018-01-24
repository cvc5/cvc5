/*********************                                                        */
/*! \file sygus_sampler.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sygus_sampler
 **/

#include "theory/quantifiers/sygus_sampler.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
SygusSampler::SygusSampler( QuantifiersEngine * qe, Node f, unsigned nsamples ) : d_qe( qe ) {
  
  
  
  for( unsigned i=0; i<nsamples; i++ )
  {
    std::vector< Node > sample_pt;
  }
}

void SygusSampler::registerTerm( Node n )
{
  
}

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */
