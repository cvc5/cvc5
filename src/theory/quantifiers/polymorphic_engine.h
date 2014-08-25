/*********************                                                        */
/*! \file polymorphic_engine.h
 ** \verbatim
 ** Original author: Francois Bobot
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef __CVC4__POLYMORPHIC_ENGINE_H
#define __CVC4__POLYMORPHIC_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantInfo;

class PolymorphicEngine : public QuantifiersModule
{
  std::vector< Node > d_lemma;
public:
  PolymorphicEngine( context::Context* c, QuantifiersEngine* qe );
  /** Quantifiers Module intereface */
  bool needsCheck(Theory::Effort e);
  void check( Theory::Effort e, unsigned quant_e );
  void registerQuantifier( Node q );
  void assertNode( Node n );
  std::string identify() const { return "PolymorphicEngine"; }
};

}
}
}

#endif
