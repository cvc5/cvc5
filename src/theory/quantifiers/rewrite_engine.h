/*********************                                                        */
/*! \file rewrite_engine.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
**/

#include "cvc4_private.h"

#ifndef __CVC4__REWRITE_ENGINE_H
#define __CVC4__REWRITE_ENGINE_H

#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class RewriteEngine : public QuantifiersModule
{
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
  std::vector< Node > d_rr_quant;
  std::map< Node, Node > d_rr_guard;
  Node d_true;
  /** explicitly provided patterns */
  std::map< Node, std::vector< inst::Trigger* > > d_rr_triggers;
  double getPriority( Node f );
private:
  int checkRewriteRule( Node f );
public:
  RewriteEngine( context::Context* c, QuantifiersEngine* qe );

  void check( Theory::Effort e );
  void registerQuantifier( Node f );
  void assertNode( Node n );
};

}
}
}

#endif
