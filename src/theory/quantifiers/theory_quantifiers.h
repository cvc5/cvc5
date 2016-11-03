/*********************                                                        */
/*! \file theory_quantifiers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include <ext/hash_set>
#include <iostream>
#include <map>

#include "context/cdhashmap.h"
#include "theory/theory.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

namespace CVC4 {
class TheoryEngine;

namespace theory {

namespace quantifiers {

class ModelEngine;
class InstantiationEngine;

class TheoryQuantifiers : public Theory {
private:
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;
  /** number of instantiations */
  int d_numInstantiations;
  int d_baseDecLevel;

  eq::EqualityEngine* d_masterEqualityEngine;

private:
  void computeCareGraph();

public:
  TheoryQuantifiers(context::Context* c, context::UserContext* u,
                    OutputChannel& out, Valuation valuation,
                    const LogicInfo& logicInfo);
  ~TheoryQuantifiers();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);
  void addSharedTerm(TNode t);
  void notifyEq(TNode lhs, TNode rhs);
  void preRegisterTerm(TNode n);
  void presolve();
  void ppNotifyAssertions( std::vector< Node >& assertions );
  void check(Effort e);
  Node getNextDecisionRequest( unsigned& priority );
  Node getValue(TNode n);
  void collectModelInfo( TheoryModel* m, bool fullModel );
  void shutdown() { }
  std::string identify() const { return std::string("TheoryQuantifiers"); }
  void setUserAttribute(const std::string& attr, Node n, std::vector<Node> node_values, std::string str_value);
  eq::EqualityEngine* getMasterEqualityEngine() { return d_masterEqualityEngine; }
  bool ppDontRewriteSubterm(TNode atom) { return atom.getKind() == kind::FORALL || atom.getKind() == kind::EXISTS; }
private:
  void assertUniversal( Node n );
  void assertExistential( Node n );
};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */
