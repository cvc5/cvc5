/*********************                                                        */
/*! \file quantifiers_attributes.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of QuantifiersAttributes class
 **/

#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void QuantifiersAttributes::setUserAttribute( const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value ){
  Trace("quant-attr-debug") << "Set " << attr << " " << n << std::endl;
  if( n.getKind()==FORALL ){
    if( attr=="axiom" ){
      Trace("quant-attr") << "Set axiom " << n << std::endl;
      AxiomAttribute aa;
      n.setAttribute( aa, true );
    }else if( attr=="conjecture" ){
      Trace("quant-attr") << "Set conjecture " << n << std::endl;
      ConjectureAttribute ca;
      n.setAttribute( ca, true );
    }else if( attr=="quant-inst-max-level" ){
      Assert( node_values.size()==1 );
      uint64_t lvl = node_values[0].getConst<Rational>().getNumerator().getLong();
      Trace("quant-attr") << "Set instantiation level " << n << " to " << lvl << std::endl;
      QuantInstLevelAttribute qila;
      n.setAttribute( qila, lvl );
    }else if( attr=="rr-priority" ){
      Assert( node_values.size()==1 );
      uint64_t lvl = node_values[0].getConst<Rational>().getNumerator().getLong();
      Trace("quant-attr") << "Set rewrite rule priority " << n << " to " << lvl << std::endl;
      RrPriorityAttribute rrpa;
      n.setAttribute( rrpa, lvl );
    }
  }else{
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      setUserAttribute( attr, n[i], node_values, str_value );
    }
  }
}
