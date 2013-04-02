/*********************                                                        */
/*! \file ite_simplifier.h
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simplifications for ITE expressions
 **
 ** This module implements preprocessing phases designed to simplify ITE
 ** expressions.  Based on:
 ** Kim, Somenzi, Jin.  Efficient Term-ITE Conversion for SMT.  FMCAD 2009.
 ** Burch, Jerry.  Techniques for Verifying Superscalar Microprocessors.  DAC '96
 **/

#include "cvc4_private.h"

#ifndef __CVC4__ITE_SIMPLIFIER_H
#define __CVC4__ITE_SIMPLIFIER_H

#include <deque>
#include <vector>
#include <utility>

#include "expr/node.h"
#include "expr/command.h"
#include "prop/prop_engine.h"
#include "context/cdhashset.h"
#include "theory/theory.h"
#include "theory/substitutions.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"
#include "util/statistics_registry.h"
#include "util/hash.h"
#include "util/cache.h"
#include "util/ite_removal.h"

namespace CVC4 {

class ITESimplifier {
  Node d_true;
  Node d_false;

  std::hash_map<Node, bool, NodeHashFunction> d_containsTermITECache;
  bool containsTermITE(TNode e);

  std::hash_map<Node, bool, NodeHashFunction> d_leavesConstCache;
  bool leavesAreConst(TNode e, theory::TheoryId tid);
  bool leavesAreConst(TNode e)
    { return leavesAreConst(e, theory::Theory::theoryOf(e)); }

  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  typedef std::hash_map<TNode, Node, TNodeHashFunction> TNodeMap;

  typedef std::pair<Node, Node> NodePair;
  struct NodePairHashFunction {
    size_t operator () (const NodePair& pair) const {
      size_t hash = 0;
      hash = 0x9e3779b9 + NodeHashFunction().operator()(pair.first);
      hash ^= 0x9e3779b9 + NodeHashFunction().operator()(pair.second) + (hash << 6) + (hash >> 2);
      return hash;
    }
  };/* struct ITESimplifier::NodePairHashFunction */

  typedef std::hash_map<NodePair, Node, NodePairHashFunction> NodePairMap;


  NodePairMap d_simpConstCache;
  Node simpConstants(TNode simpContext, TNode iteNode, TNode simpVar);
  std::hash_map<TypeNode, Node, TypeNode::HashFunction> d_simpVars;
  Node getSimpVar(TypeNode t);

  NodeMap d_simpContextCache;
  Node createSimpContext(TNode c, Node& iteNode, Node& simpVar);

  Node simpITEAtom(TNode atom);

  NodeMap d_simpITECache;

public:
  Node simpITE(TNode assertion);

private:

  class CareSetPtr;
  class CareSetPtrVal {
    friend class ITESimplifier::CareSetPtr;
    ITESimplifier& d_iteSimplifier;
    unsigned d_refCount;
    std::set<Node> d_careSet;
    CareSetPtrVal(ITESimplifier& simp) : d_iteSimplifier(simp), d_refCount(1) {}
  };

  std::vector<CareSetPtrVal*> d_usedSets;
  void careSetPtrGC(CareSetPtrVal* val) {
    d_usedSets.push_back(val);
  }

  class CareSetPtr {
    CareSetPtrVal* d_val;
    CareSetPtr(CareSetPtrVal* val) : d_val(val) {}
  public:
    CareSetPtr() : d_val(NULL) {}
    CareSetPtr(const CareSetPtr& cs) {
      d_val = cs.d_val;
      if (d_val != NULL) {
        ++(d_val->d_refCount);
      }
    }
    ~CareSetPtr() {
      if (d_val != NULL && (--(d_val->d_refCount) == 0)) {
        d_val->d_iteSimplifier.careSetPtrGC(d_val);
      }
    }
    CareSetPtr& operator=(const CareSetPtr& cs) {
      if (d_val != cs.d_val) {
        if (d_val != NULL && (--(d_val->d_refCount) == 0)) {
          d_val->d_iteSimplifier.careSetPtrGC(d_val);
        }
        d_val = cs.d_val;
        if (d_val != NULL) {
          ++(d_val->d_refCount);
        }
      }
      return *this;
    }
    std::set<Node>& getCareSet() { return d_val->d_careSet; }
    static CareSetPtr mkNew(ITESimplifier& simp) {
      CareSetPtrVal* val = new CareSetPtrVal(simp);
      return CareSetPtr(val);
    }
    static CareSetPtr recycle(CareSetPtrVal* val) {
      Assert(val != NULL && val->d_refCount == 0);
      val->d_refCount = 1;
      return CareSetPtr(val);
    }
  };

  CareSetPtr getNewSet();

  typedef std::map<TNode, CareSetPtr> CareMap;
  void updateQueue(CareMap& queue, TNode e, CareSetPtr& careSet);
  Node substitute(TNode e, TNodeMap& substTable, TNodeMap& cache);

public:
  Node simplifyWithCare(TNode e);

  ITESimplifier() {
    d_true = NodeManager::currentNM()->mkConst<bool>(true);
    d_false = NodeManager::currentNM()->mkConst<bool>(false);
  }
  ~ITESimplifier() {}

};

}

#endif
