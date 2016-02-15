/*********************                                                        */
/*! \file theory_sets_rels.h
 ** \verbatim
 ** Original author: Paul Meng
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Extension to Sets theory.
 **/

#ifndef SRC_THEORY_SETS_THEORY_SETS_RELS_H_
#define SRC_THEORY_SETS_THEORY_SETS_RELS_H_

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsRels {

public:
  TheorySetsRels(context::Context* c,
                 context::UserContext* u,
                 eq::EqualityEngine*);

  ~TheorySetsRels();

  void check(Theory::Effort);

private:

  /** True and false constant nodes */
  Node d_trueNode;
  Node d_falseNode;

  eq::EqualityEngine *d_eqEngine;

  // save all the relational terms seen so far
  context::CDHashSet <Node, NodeHashFunction> d_relsSaver;

  void assertMembership(TNode fact, TNode reason, bool polarity);

  Node reverseTuple(TNode tuple);
};

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */



#endif /* SRC_THEORY_SETS_THEORY_SETS_RELS_H_ */
