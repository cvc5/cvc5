/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Original author: Liana Hadarean 
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/lazy_bitblaster.h"
#include "theory/bv/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

class SubstitutionEx {
  struct SubstitutionElement {
    TNode to;
    Node reason;
    SubstitutionElement(TNode t, TNode r)
      : to(t)
      , reason(r)
    {}
  };

  struct SubstitutionStackElement {
    TNode node;
    bool childrenAdded;
    SubstitutionStackElement(TNode n, bool ca = false)
      : node(n)
        childrenAdded(ca)
    {}
  };

  typedef __gnu_cxx::hash_map<TNode, SubstitutionElement, TNodeHashFunction> Substitutions;
  typedef __gnu_cxx::hash_map<TNode, SubstitutionElement, TNodeHashFunction> SubstitutionsCache;

  Substitutions d_substitutions;
  SubstitutionsCache d_cache;
  bool d_cacheInvalid;

  Node getReason(TNode node) const;
  bool hasCache(TNode node) const;
  void storeCache(TNode from, TNode to, Node reason);
  Node applyInternal(TNode node);

public:
  SubstitutionEx()
    : d_substitutions()
    , d_cache()
    , d_cacheInvalid(true)
  {}

  void addSubstitution(TNode from, TNode to, TNode reason);
  Node apply(TNode node);
  Node explain(TNode node) const;


};


void SubstitutionEx::addSubstitution(TNode from, TNode to, TNode reason) {
  d_cacheInvalid = true;
  Assert (from != to);
  Assert (d_substitutions.find(from) == d_substitutions.end());
  d_substitutions[from] = SubstitutionElement(to, reason);
}

Node SubstitutionEx::apply(TNode node) {
  if (d_cacheInvalid) {
    d_cache.clear();
    d_cacheInvalid = false;
  }

  SubstitutionsCache::iterator it = d_cache.find(node);
  if (it != d_cache.end()) {
    return it->second.to;
  }

  Node result = internalApply(node); 
  return result;
}

Node SubstitutionEx::internalApply(TNode node) {
  if (d_substitutions.empty())
    return node;

  vector<SubstitutionStackElement> stack;
  stack.push_back(SubstitutionStackElement(node));

  while (!stack.empty()) {
    SubstitutionStackElement head = stack.back();
    stack.pop_back();
    
    TNode current = head.node;

    if (hasCache(current)) {
      continue;
    }

    // check if it has substitution
    Substitutions::const_iterator it = d_substitutions.find(current);
    if (it != d_substitutions.end()) {
      vector<Node> reasons;
      TNode to = it->node;
      reasons.push_back(it->reason);
      // check if the thing we subsituted to has substitutions
      TNode res = internalApply(to);
      // update reasons
      reasons.push_back(getReason(res));
      Node reason = utils::mkAnd(reasons);
      storeCache(current, res, reasons);
      continue;
    }
    
    // children already processed 
    if (head.childrenAdded) {
      NodeBuilder nb(current.getKind());
      std::vector<Node> reasons;
      
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        TNode op = current.getOperator();
        Assert (hasCache(op));
        nb << getCache(op);
        reasons.push_back(getReason(op));
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        Assert (hasCache(current[i]));
        nb << getCache(current[i]);
        reasons.push_back(getReasons(current[i]));
      }
      Node result = nb;
      Node subt_result = applyInternal(result);
      reasons.push_back(getReason(subst_result));
      Node reason = utils::mkAnd(reasons);
      storeCache(current, subt_result, reason);
      continue;
    } else {
      // add children to stack
      stack.push_back(SubstitutionStackElement(current, true));
      if (current.getMetaKind() == kind::metakind::PARAMETERIZED) {
        stack.push_back(SubstitutionStackElement(current.getOperator()));
      }
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        stack.push_back(SubstitutionStackElement(current[i]));
      }
    }
  }

  Assert(hasCache(node));
  return getCache(node);
}


Node SubstitutionEx::explain(TNode node) const {
  Assert(hasCache(node));
  return Rewriter::rewrite(getReason(node));
}

Node SubsitutionsEx::getReason(TNode node) const {
  Assert(hasCache(node));
  SubstitutionsCache::const_iterator it = d_cache.find(node);
  return it->second.reason;
}

bool SubstitutionEx::hasCache(TNode node) const {
  return d_cache.find(node) != d_cache.end();
}

void SubstitutionEx::storeCache(TNode from, TNode to, Node reason) {
  Assert (!hasCache(from));
  d_cache[from] = SubstitutionElement(to, reason);
}


bool AlgebraicSolver::check(Theory::Effort e) {
  if (!Theory::fullEffort(e))
    return true;

  
  Debug("bv-algebraic") << "AlgebraicSolver::check (" << e << ")\n";
  Assert(!options::bitvectorEagerBitblast()); 

  ++(d_statistics.d_numCallstoCheck);

  std::vector<TNode> facts;
  // Processing assertions from scratch
  for (AssertionQueue::const_iterator it = assertionsBegin(); it != assertionsEnd(); ++it) {
    facts.push_back(*it); 
  }
  
  SubstitutionEx subst;
  for (unsigned i = 0; i < facts.size(); ++i) {
    if(solve(facts[i], subst)) {
      for (unsigned j = 0; j < facts.size(); ++j) {
        facts[j] = subst.apply(facts[j]);
      }
    }
  }

  for (unsigned read = write = 0; read < facts.size(); ++read) {
    Node fact = Rewriter::rewrite(facts[read]);
    if (fact.isConst() &&
        fact.getConst<bool>() == true) {
      continue;
    }

    if (fact.isConst() &&
        fact.getConst<bool>() == false) {
      // we have a conflict
      Node conflict = subst.explain(fact);
      d_bv->setConflict(conflict);
      return false;
    }
    facts[write] = fact;
    ++write;
  }
  facts.resize(write);
  
  if (facts.empty())
    return true;

  d_quickSolver.clear();

  Node conflict = d_quickSolver(facts, true);
  if (conflict.isNull()) {
    return true;
  }

  if (conflict.getNumChildren() == 1) {
    Node theory_confl = subst.explain(conflict);
    d_bv->setConflict(theory_confl);
    return false;
  }

  Assert (conflict.getKind() == kind::AND);
  vector<TNode> theory_confl;
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode c = conflict[i];
    TNode c_expl = subst.explain(conflict);
    theory_confl.push_back(c_expl);
  }
  
  Node confl = Rewriter::rewrite(utils::mkAnd(theory_confl));
  d_bv->setConflict(confl);
  return false;
}


bool AlgebraicSolver::solve(TNode fact, SubstitutionEx& subst) {
  if (fact.getKind() != kind::EQUAL) return false; 
  if (fact[0].isVar() &&
      !fact[1].hasSubterm(fact[0])) {
    subt.addSubstitution(fact[0], fact[1], fact);
  } else if (fact[1].isVar() &&
             !fact[0].hasSubterm(fact[1])) {
    subt.addSubstitution(fact[1], fact[0], fact);
  }

  return true;
} 

bool AlgebraicSolver::isComplete() {

}
