/*********************                                                        */
/*! \file theory_arrays.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of arrays.
 **
 ** Theory of arrays.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H
#define __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H

#include "theory/theory.h"

#include <iostream>

namespace CVC4 {
namespace theory {
namespace arrays {

class TheoryArrays : public Theory {
public:
  TheoryArrays(int id, context::Context* c, OutputChannel& out);
  ~TheoryArrays();
  void preRegisterTerm(TNode n) { }
  void registerTerm(TNode n) { }

  RewriteResponse preRewrite(TNode in, bool topLevel) {
    Debug("arrays-rewrite") << "pre-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  RewriteResponse postRewrite(TNode in, bool topLevel) {
    Debug("arrays-rewrite") << "post-rewriting " << in
                            << " topLevel==" << topLevel << std::endl;
    return RewriteComplete(in);
  }

  void addSharedTerm(TNode t);
  void notifyEq(TNode eq);
  void check(Effort e);
  void propagate(Effort e) { }
  void explain(TNode n, Effort e) { }
  void shutdown() { }
  std::string identify() const { return std::string("TheoryArrays"); }
};/* class TheoryArrays */

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARRAYS__THEORY_ARRAYS_H */
