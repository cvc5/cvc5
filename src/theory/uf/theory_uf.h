/*********************                                                        */
/** theory_uf.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/


#ifndef __CVC4__THEORY__THEORY_UF_H
#define __CVC4__THEORY__THEORY_UF_H

#include "expr/node.h"
#include "theory/theory.h"
#include "theory/output_channel.h"
#include "context/context.h"
#include "theory/uf/ecdata.h"

namespace CVC4 {
namespace theory {

class TheoryUF : public Theory {
private:
  context::Context* d_context;
  context::CDList<Node> d_pending;
  context::CDList<Node> d_disequality;
  context::CDO<unsigned> d_currentPendingIdx;

public:
  void setup(const Node& n);
  
  void check(OutputChannel& out, Effort level= FULL_EFFORT);

  void propagate(OutputChannel& out, Effort level= FULL_EFFORT){}

  void explain(OutputChannel& out,
               const Node& n,
               Effort level = FULL_EFFORT){}

private:
  bool equiv(Node x, Node y);
  void ccUnion(ECData* ecX, ECData* ecY);
  ECData* ccFind(ECData* x);

  void merge();
  //TODO put back in theory


};

} /* CVC4::theory namespace */
} /* CVC4 namespace */


#endif /* __CVC4__THEORY__THEORY_UF_H */
