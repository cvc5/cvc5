/*********************                                                        */
/*! \file theory_sets.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2013-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory.
 **
 ** Sets theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SETS__THEORY_SETS_H
#define __CVC4__THEORY__SETS__THEORY_SETS_H

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;

class TheorySets : public Theory {
private:
  friend class TheorySetsPrivate;
  TheorySetsPrivate* d_internal;
public:

  /**
   * Constructs a new instance of TheorySets w.r.t. the provided
   * contexts.
   */
  TheorySets(context::Context* c,
               context::UserContext* u,
               OutputChannel& out,
               Valuation valuation,
               const LogicInfo& logicInfo);

  ~TheorySets();

  void check(Effort);

  void propagate(Effort);

  Node explain(TNode);

  std::string identify() const { return "THEORY_SETS"; }

  void preRegisterTerm(TNode node);

};/* class TheorySets */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_H */
