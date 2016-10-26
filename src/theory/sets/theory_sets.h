/*********************                                                        */
/*! \file theory_sets.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Kshitij Bansal, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
class TheorySetsScrutinize;

class TheorySets : public Theory {
private:
  friend class TheorySetsPrivate;
  friend class TheorySetsScrutinize;
  friend class TheorySetsRels;
  TheorySetsPrivate* d_internal;
public:

  /**
   * Constructs a new instance of TheorySets w.r.t. the provided
   * contexts.
   */
  TheorySets(context::Context* c, context::UserContext* u, OutputChannel& out,
             Valuation valuation, const LogicInfo& logicInfo);

  ~TheorySets();

  void addSharedTerm(TNode);

  void check(Effort);

  void collectModelInfo(TheoryModel*, bool fullModel);

  void computeCareGraph();

  Node explain(TNode);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  Node getModelValue(TNode);

  std::string identify() const { return "THEORY_SETS"; }

  void preRegisterTerm(TNode node);

  void presolve();

  void propagate(Effort);

  void setMasterEqualityEngine(eq::EqualityEngine* eq);
  
  bool isEntailed( Node n, bool pol );

};/* class TheorySets */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SETS__THEORY_SETS_H */
