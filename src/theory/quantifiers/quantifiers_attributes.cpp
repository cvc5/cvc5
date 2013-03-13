/*********************                                                        */
/*! \file quantifiers_attributes.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds <andrew.j.reynolds@gmail.com>
 ** Major contributors: Morgan Deters <mdeters@cs.nyu.edu>
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of QuantifiersAttributes class
 **/

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void QuantifiersAttributes::setUserAttribute( const std::string& attr, Node n ){
  if( n.getKind()==FORALL ){
    if( attr=="axiom" ){
      Trace("quant-attr") << "Set axiom " << n << std::endl;
      AxiomAttribute aa;
      n.setAttribute( aa, true );
    }else if( attr=="conjecture" ){
      Trace("quant-attr") << "Set conjecture " << n << std::endl;
      ConjectureAttribute ca;
      n.setAttribute( ca, true );
    }
  }else{
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      setUserAttribute( attr, n[i] );
    }
  }
}
