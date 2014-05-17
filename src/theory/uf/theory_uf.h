/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Dejan Jovanovic, Morgan Deters
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__UF__THEORY_UF_H
#define __CVC4__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
//#include "expr/attribute.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/symmetry_breaker.h"

#include "context/cdo.h"
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace uf {

class UfTermDb;
class StrongSolverTheoryUF;

class TheoryUF : public Theory {

  friend class StrongSolverTheoryUF;

public:

  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryUF& d_uf;
  public:
    NotifyClass(TheoryUF& uf): d_uf(uf) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_uf.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_uf.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_uf.propagate(predicate);
      } else {
       return d_uf.propagate(predicate.notNode());
      }
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("uf") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_uf.propagate(t1.eqNode(t2));
      } else {
        return d_uf.propagate(t1.eqNode(t2).notNode());
      }
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("uf") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_uf.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) {
      Debug("uf") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
      d_uf.eqNotifyNewClass(t);
    }

    void eqNotifyPreMerge(TNode t1, TNode t2) {
      Debug("uf") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << std::endl;
      d_uf.eqNotifyPreMerge(t1, t2);
    }

    void eqNotifyPostMerge(TNode t1, TNode t2) {
      Debug("uf") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << std::endl;
      d_uf.eqNotifyPostMerge(t1, t2);
    }

    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
      Debug("uf") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << std::endl;
      d_uf.eqNotifyDisequal(t1, t2, reason);
    }

  };/* class TheoryUF::NotifyClass */

  /** A callback class for ppRewrite().  See registerPpRewrite(), below. */
  class PpRewrite {
  public:
    virtual Node ppRewrite(TNode node) = 0;
    virtual ~PpRewrite() {}
  };/* class TheoryUF::PpRewrite */

private:

  /** The notify class */
  NotifyClass d_notify;

  /** The associated theory strong solver (or NULL if none) */
  StrongSolverTheoryUF* d_thss;

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict */
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /**
   * Should be called to propagate the literal. We use a node here
   * since some of the propagated literals are not kept anywhere.
   */
  bool propagate(TNode literal);

  /**
   * Explain why this literal is true by adding assumptions
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);

  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);

  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);

  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);

  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  /** a registry type for keeping Node-specific callbacks for ppRewrite() */
  typedef std::hash_map<Node, PpRewrite*, NodeHashFunction> RegisterPpRewrites;

  /** a collection of callbacks to issue while doing a ppRewrite() */
  RegisterPpRewrites d_registeredPpRewrites;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo);

  ~TheoryUF();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);
  void finishInit();

  void check(Effort);
  void preRegisterTerm(TNode term);
  Node explain(TNode n);

  void collectModelInfo( TheoryModel* m, bool fullModel );

  void ppStaticLearn(TNode in, NodeBuilder<>& learned);
  void presolve();

  void addSharedTerm(TNode n);
  void computeCareGraph();

  void propagate(Effort effort);
  Node getNextDecisionRequest();

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  std::string identify() const {
    return "THEORY_UF";
  }

  eq::EqualityEngine* getEqualityEngine() {
    return &d_equalityEngine;
  }

  StrongSolverTheoryUF* getStrongSolver() {
    return d_thss;
  }

  Node ppRewrite(TNode node);

  /**
   * Register a ppRewrite() callback on "op."  TheoryUF owns
   * the callback, and will delete it when it is destructed.
   */
  void registerPpRewrite(TNode op, PpRewrite* callback) {
    d_registeredPpRewrites.insert(std::make_pair(op, callback));
  }
};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */
