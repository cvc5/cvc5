/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): barrett
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BV__THEORY_BV_H
#define __CVC4__THEORY__BV__THEORY_BV_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdset.h"
#include "context/cdlist.h"
#include "theory/bv/equality_engine.h"
#include "theory/bv/slice_manager.h"

namespace CVC4 {
namespace theory {
namespace bv {

class TheoryBV : public Theory {

public:

  class EqualityNotify {
    TheoryBV& d_theoryBV;
  public:
    EqualityNotify(TheoryBV& theoryBV)
    : d_theoryBV(theoryBV) {}

    bool operator () (size_t triggerId) {
      return d_theoryBV.triggerEquality(triggerId);
    }
    void conflict(Node explanation) {
      std::set<TNode> assumptions;
      utils::getConjuncts(explanation, assumptions);
      d_theoryBV.d_out->conflict(utils::mkConjunction(assumptions));
    }
  };

  struct BVEqualitySettings {
    static inline bool descend(TNode node) {
      return node.getKind() == kind::BITVECTOR_CONCAT || node.getKind() == kind::BITVECTOR_EXTRACT;
    }

    /** Returns true if node1 has preference to node2 as a representative, otherwise node2 is used */
    static inline bool mergePreference(TNode node1, unsigned node1size, TNode node2, unsigned node2size) {
      if (node1.getKind() == kind::CONST_BITVECTOR) {
        Assert(node2.getKind() != kind::CONST_BITVECTOR);
        return true;
      }
      if (node2.getKind() == kind::CONST_BITVECTOR) {
        Assert(node1.getKind() != kind::CONST_BITVECTOR);
        return false;
      }
      if (node1.getKind() == kind::BITVECTOR_CONCAT) {
        Assert(node2.getKind() != kind::BITVECTOR_CONCAT);
        return true;
      }
      if (node2.getKind() == kind::BITVECTOR_CONCAT) {
        Assert(node1.getKind() != kind::BITVECTOR_CONCAT);
        return false;
      }
      return node2size < node1size;
    }
  };

  typedef EqualityEngine<TheoryBV, EqualityNotify, BVEqualitySettings> BvEqualityEngine;

private:

  /** Equality reasoning engine */
  BvEqualityEngine d_eqEngine;

  /** Slice manager */
  SliceManager<TheoryBV> d_sliceManager;

  /** Equality triggers indexed by ids from the equality manager */
  std::vector<Node> d_triggers;
  
  /** The context we are using */
  context::Context* d_context;

  /** The asserted stuff */
  context::CDSet<TNode, TNodeHashFunction> d_assertions;

  /** Asserted dis-equalities */
  context::CDList<TNode> d_disequalities;

  struct Normalization {
    context::CDList<Node> equalities;
    context::CDList< std::set<TNode> > assumptions;
    Normalization(context::Context* c, TNode eq)
    : equalities(c), assumptions(c) {
      equalities.push_back(eq);
      assumptions.push_back(std::set<TNode>());
    }
  };

  /** Map from equalities to their noramlization information */
  typedef __gnu_cxx::hash_map<TNode, Normalization*, TNodeHashFunction> NormalizationMap;
  NormalizationMap d_normalization;

  /** Called by the equality managere on triggers */
  bool triggerEquality(size_t triggerId);

  Node d_true;

public:

  TheoryBV(context::Context* c, OutputChannel& out, Valuation valuation)
  : Theory(THEORY_BV, c, out, valuation), 
    d_eqEngine(*this, c, "theory::bv::EqualityEngine"), 
    d_sliceManager(*this, c), 
    d_context(c),
    d_assertions(c), 
    d_disequalities(c)
  {
    d_true = utils::mkTrue();
  }

  BvEqualityEngine& getEqualityEngine() {
    return d_eqEngine;
  }

  void preRegisterTerm(TNode n);

  //void registerTerm(TNode n) { }

  void check(Effort e);

  //void presolve() { }

  void propagate(Effort e) { }

  void explain(TNode n);

  Node getValue(TNode n);

  std::string identify() const { return std::string("TheoryBV"); }
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BV__THEORY_BV_H */
