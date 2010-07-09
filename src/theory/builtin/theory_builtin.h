/*********************                                                        */
/*! \file theory_builtin.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Built-in theory.
 **
 ** Built-in theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H

#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltin : public Theory {
  /** rewrite a DISTINCT expr */
  static Node blastDistinct(TNode in);

public:
  TheoryBuiltin(int id, context::Context* c, OutputChannel& out) : Theory(id, c, out) { }
  ~TheoryBuiltin() { }
  void preRegisterTerm(TNode n) { Unreachable(); }
  void registerTerm(TNode n) { Unreachable(); }
  void check(Effort e) { Unreachable(); }
  void propagate(Effort e) { Unreachable(); }
  void explain(TNode n, Effort e) { Unreachable(); }
  void shutdown() { }
  RewriteResponse preRewrite(TNode n, bool topLevel);
  std::string identify() const { return std::string("TheoryBuiltin"); }
};/* class TheoryBuiltin */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H */
