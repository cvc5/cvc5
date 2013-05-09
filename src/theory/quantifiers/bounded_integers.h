/*********************                                                        */
/*! \file bounded_integers.h
** \verbatim
** Original author: Andrew Reynolds
** This file is part of the CVC4 project.
** Copyright (c) 2009-2013  New York University and The University of Iowa
** See the file COPYING in the top-level source directory for licensing
** information.\endverbatim
**
** \brief This class manages integer bounds for quantifiers
**/

#include "cvc4_private.h"

#ifndef __CVC4__BOUNDED_INTEGERS_H
#define __CVC4__BOUNDED_INTEGERS_H


#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class BoundedIntegers : public QuantifiersModule
{
private:
  std::map< Node, std::map< Node, Node > > d_lowers;
  std::map< Node, std::map< Node, Node > > d_uppers;
  std::map< Node, std::map< Node, bool > > d_set;
  void hasFreeVar( Node f, Node n );
  void process( Node f, Node n, bool pol );
  void processLiteral( Node f, Node lit, bool pol );
public:
  BoundedIntegers( QuantifiersEngine* qe );

  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node n );
  Node getNextDecisionRequest();
};

}
}
}

#endif