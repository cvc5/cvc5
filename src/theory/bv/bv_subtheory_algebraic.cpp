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

#include "theory/bv/options.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/bv_subtheory_algebraic.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv_utils.h"

// #include "theory/bv/lazy_bitblaster.h"


using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::prop;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool hasExpensiveBVOperators(TNode fact);

SubstitutionEx::SubstitutionEx()
  : d_substitutions()
  , d_cache()
  , d_cacheInvalid(true)
{}

void SubstitutionEx::addSubstitution(TNode from, TNode to, TNode reason) {
  Debug("bv-substitution") << "SubstitutionEx::addSubstitution: "<< from <<" => "<< to <<"\n";
  Debug("bv-substitution") << " reason "<<reason << "\n";
  
  d_cacheInvalid = true;
  Assert (from != to);
  Assert (d_substitutions.find(from) == d_substitutions.end());
  d_substitutions[from] = SubstitutionElement(to, reason);
}

Node SubstitutionEx::apply(TNode node) {
  Debug("bv-substitution") << "SubstitutionEx::apply("<< node <<")\n";
  if (d_cacheInvalid) {
    d_cache.clear();
    d_cacheInvalid = false;
  }

  SubstitutionsCache::iterator it = d_cache.find(node);

  if (it != d_cache.end()) {
    Node res = it->second.to;
    Debug("bv-substitution") << "   =>"<< res <<"\n";
    return res;
  }

  Node result = internalApply(node);
  Debug("bv-substitution") << "   =>"<< result <<"\n";
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
      TNode to = it->second.to;
      reasons.push_back(it->second.reason);
      // check if the thing we subsituted to has substitutions
      TNode res = internalApply(to);
      // update reasons
      reasons.push_back(getReason(to));
      Node reason = utils::mkAnd(reasons);
      storeCache(current, res, reason);
      continue;
    }

    // if no children then just continue
    if(current.getNumChildren() == 0) {
      storeCache(current, current, utils::mkTrue());
      continue;
    }
    
    // children already processed 
    if (head.childrenAdded) {
      NodeBuilder<> nb(current.getKind());
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
        reasons.push_back(getReason(current[i]));
      }
      Node result = nb;
      // if the node is new apply substitutions to it
      Node subst_result = result;
      if (result != current) {
        subst_result = result!= current? internalApply(result) : result;
        reasons.push_back(getReason(result));
      }
      Node reason = utils::mkAnd(reasons);
      storeCache(current, subst_result, reason);
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
  if(!hasCache(node))
    return utils::mkTrue();
  
  Debug("bv-substitution") << "SubstitutionEx::explain("<< node <<")\n";
  Node res = getReason(node);
  Debug("bv-substitution") << "  with "<< res <<"\n";
  return res;
}

Node SubstitutionEx::getReason(TNode node) const {
  Assert(hasCache(node));
  SubstitutionsCache::const_iterator it = d_cache.find(node);
  return it->second.reason;
}

bool SubstitutionEx::hasCache(TNode node) const {
  return d_cache.find(node) != d_cache.end();
}

Node SubstitutionEx::getCache(TNode node) const {
  Assert (hasCache(node));
  return d_cache.find(node)->second.to;
}

void SubstitutionEx::storeCache(TNode from, TNode to, Node reason) {
  //  Debug("bv-substitution") << "SubstitutionEx::storeCache(" << from <<", " << to <<", "<< reason<<")\n"; 
  Assert (!hasCache(from));
  d_cache[from] = SubstitutionElement(to, reason);
}

AlgebraicSolver::AlgebraicSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv)
  , d_quickSolver(new BVQuickCheck())
  , d_isComplete(c, false)
  , d_isDifficult(c, false)
  , d_budget(options::bvAlgebraicBudget())
  , d_explanations()
  , d_statistics()
{}

bool AlgebraicSolver::check(Theory::Effort e) {
  Assert(!options::bitvectorEagerBitblast());

  d_explanations.clear();
  
  if (!Theory::fullEffort(e))
    return true;

  if (!useHeuristic())
    return true;
  
  ++(d_numCalls);
  
  TimerStat::CodeTimer algebraicTimer(d_statistics.d_solveTime);
  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check (" << e << ")\n";
  ++(d_statistics.d_numCallstoCheck);


  std::vector<TNode> assertions;
  std::vector<Node> worklist;

  uint64_t original_bb_cost = 0;

  NodeSet seen_assertions;
  // Processing assertions from scratch
  for (AssertionQueue::const_iterator it = assertionsBegin(); it != assertionsEnd(); ++it) {
    Debug("bv-subtheory-algebraic") << "   " << *it << "\n";
    TNode assertion = *it;
    assertions.push_back(assertion);
    worklist.push_back(assertion);
    Assert (d_explanations.find(assertion) == d_explanations.end());
    d_explanations[assertion] = assertion;
    uint64_t assertion_size = d_quickSolver->computeAtomWeight(assertion, seen_assertions);
    Assert (original_bb_cost < original_bb_cost + assertion_size);
    original_bb_cost+= assertion_size; 
  }

  Debug("bv-subtheory-algebraic") << "Assertions " << worklist.size() <<" : \n";

  bool changed = true;
  SubstitutionEx subst;
  
  while(changed) {
    changed = false;
    for (unsigned i = 0; i < worklist.size(); ++i) {
      // getting original assertion
      Node assertion = assertions[i];
      // apply current substitutions
      Node current = subst.apply(worklist[i]);
      Node subst_expl = subst.explain(worklist[i]);
      worklist[i] = Rewriter::rewrite(current);
      // explanation for this assertion
      Node assertion_expl = d_explanations[assertion];
      Node new_expl = subst_expl == utils::mkTrue() ? assertion_expl
        : utils::mkAnd(subst_expl, assertion_expl);
      d_explanations[assertion] = new_expl;
      
      // use the new substitution to solve
      if(solve(worklist[i], subst, new_expl)) {
        changed = true;
      }
    }
  }

  NodeSet subst_seen;
  uint64_t subst_bb_cost = 0;


  unsigned r = 0;
  unsigned w = 0;

  for (; r < worklist.size(); ++r) {

    TNode fact = worklist[r];
    
    if (Dump.isOn("bv-algebraic")) {
      Node expl = d_explanations[assertions[r]];
      Node query = utils::mkNot(utils::mkNode(kind::IMPLIES, expl, fact));
      Dump("bv-algebraic") << EchoCommand("ThoeryBV::AlgebraicSolver::substitution explanation"); 
      Dump("bv-algebraic") << PushCommand(); 
      Dump("bv-algebraic") << AssertCommand(query.toExpr());
      Dump("bv-algebraic") << CheckSatCommand();
      Dump("bv-algebraic") << PopCommand(); 
    }

    if (fact.isConst() &&
        fact.getConst<bool>() == true) {
      continue;
    }

    if (fact.isConst() &&
        fact.getConst<bool>() == false) {
      // we have a conflict
      Node conflict = Rewriter::rewrite(d_explanations[assertions[r]]);
      d_bv->setConflict(conflict);
      d_isComplete.set(true);
      Debug("bv-subtheory-algebraic") << " UNSAT: assertion simplfies to false with conflict: "<< conflict << "\n";
       
      if (Dump.isOn("bv-algebraic")) {
        Dump("bv-algebraic") << EchoCommand("TheoryBV::AlgebraicSolver::conflict"); 
        Dump("bv-algebraic") << PushCommand(); 
        Dump("bv-algebraic") << AssertCommand(conflict.toExpr());
        Dump("bv-algebraic") << CheckSatCommand();
        Dump("bv-algebraic") << PopCommand(); 
      }

      
      ++(d_statistics.d_numSimplifiesToFalse);
      ++(d_numSolved);
      return false;
    }

    subst_bb_cost+= d_quickSolver->computeAtomWeight(fact, subst_seen);
    worklist[w] = fact;
    Node expl = Rewriter::rewrite(d_explanations[assertions[r]]);
    d_explanations[fact] = expl;
    ++w;
  }

  worklist.resize(w);
  
  double ratio = ((double)subst_bb_cost)/original_bb_cost;
  if (ratio > 0.5) {
    // give up if problem not reduced enough
    d_isComplete = false;
    return true;
  }
  
  if(Debug.isOn("bv-subtheory-algebraic")) {
    Debug("bv-subtheory-algebraic") << "Assertions post-substitutions " << worklist.size() << ":\n";
    for (unsigned i = 0; i < worklist.size(); ++i) {
      Debug("bv-subtheory-algebraic") << "   " << worklist[i] << "\n";
      //Debug("bv-subtheory-algebraic") << "Reason:  " << d_explanations[worklist[i]] << "\n";
    }
  }

  // all facts solved to true
  if (worklist.empty()) {
    Debug("bv-subtheory-algebraic") << " SAT: everything simplifies to true.\n";
    ++(d_statistics.d_numSimplifiesToTrue);
    ++(d_numSolved);
    return true;
  }

  d_quickSolver->reset();
  d_quickSolver->push();
  bool ok = quickCheck(worklist, subst);
  d_quickSolver->pop();
  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check done " << ok << ".\n";
  return ok;
}

bool AlgebraicSolver::quickCheck(std::vector<Node>& facts, SubstitutionEx& subst) {
  SatValue res = d_quickSolver->checkSat(facts, d_budget);

  if (res == SAT_VALUE_UNKNOWN) {
    d_isComplete.set(false);
    Debug("bv-subtheory-algebraic") << " Unknown.\n";
    ++(d_statistics.d_numUnknown);
    return true;
  }
  
  if (res == SAT_VALUE_TRUE) {
    Debug("bv-subtheory-algebraic") << " Sat.\n";
    ++(d_statistics.d_numSat);
    ++(d_numSolved);
    d_isComplete.set(true);
    return true;
  }

  Assert (res == SAT_VALUE_FALSE);
  Assert (d_quickSolver->inConflict());  

  Debug("bv-subtheory-algebraic") << " Unsat.\n";
  ++(d_numSolved);
  ++(d_statistics.d_numUnsat);

  
  Node conflict = d_quickSolver->getConflict();
  Debug("bv-subtheory-algebraic") << " Conflict: " << conflict << "\n";

  // std::cout <<"QuickSolver conflict " << conflict <<"\n"; 
  
  // singleton conflict
  if (conflict.getKind() != kind::AND) {
    Assert (d_explanations.find(conflict) != d_explanations.end());
    Node theory_confl = d_explanations[conflict];
    d_bv->setConflict(theory_confl);
    return false;
  }

  Assert (conflict.getKind() == kind::AND);
  vector<TNode> theory_confl;
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode c = conflict[i];
    Assert (d_explanations.find(c) != d_explanations.end());
    TNode c_expl = d_explanations[c];
    theory_confl.push_back(c_expl);
  }
  
  Node confl = Rewriter::rewrite(utils::mkAnd(theory_confl));
  // std::cout <<"Subst conflict " << conflict <<"\n"; 
  Debug("bv-subtheory-algebraic") << " Out Conflict: " << confl << "\n";
  d_bv->setConflict(confl);
  return false;
}


bool AlgebraicSolver::solve(TNode fact, SubstitutionEx& subst, TNode reason) {
  if (fact.getKind() != kind::EQUAL) return false; 
  if (fact[0].isVar() &&
      !fact[1].hasSubterm(fact[0])) {
    subst.addSubstitution(fact[0], fact[1], reason);
    return true;
  } else if (fact[1].isVar() &&
             !fact[0].hasSubterm(fact[1])) {
    subst.addSubstitution(fact[1], fact[0], reason);
    return true;
  }

  return false;
} 

bool AlgebraicSolver::isComplete() {
  return d_isComplete.get(); 
}

bool AlgebraicSolver::useHeuristic() {
  if (!d_isDifficult.get())
    return false;

  if (d_numCalls == 0)
    return true;
  
  double success_rate = d_numSolved/d_numCalls;
  d_statistics.d_useHeuristic.setData(success_rate);
  return success_rate > 0.8;
}


void AlgebraicSolver::assertFact(TNode fact) {
  d_assertionQueue.push_back(fact);
  if (!d_isDifficult.get()) {
    d_isDifficult.set(hasExpensiveBVOperators(fact));
  }
}

AlgebraicSolver::~AlgebraicSolver() {
  delete d_quickSolver;
}

AlgebraicSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::AlgebraicSolver::NumCallsToCheck", 0)
  , d_numSimplifiesToTrue("theory::bv::AlgebraicSolver::NumSimplifiesToTrue", 0)
  , d_numSimplifiesToFalse("theory::bv::AlgebraicSolver::NumSimplifiesToFalse", 0)
  , d_numUnsat("theory::bv::AlgebraicSolver::NumUnsat", 0)
  , d_numSat("theory::bv::AlgebraicSolver::NumSat", 0)
  , d_numUnknown("theory::bv::AlgebraicSolver::NumUnknown", 0)
  , d_solveTime("theory::bv::AlgebraicSolver::SolveTime")
  , d_useHeuristic("theory::bv::AlgebraicSolver::UseHeuristic", 0.2)
{
  StatisticsRegistry::registerStat(&d_numCallstoCheck);
  StatisticsRegistry::registerStat(&d_numSimplifiesToTrue);
  StatisticsRegistry::registerStat(&d_numSimplifiesToFalse);
  StatisticsRegistry::registerStat(&d_numUnsat);
  StatisticsRegistry::registerStat(&d_numSat);
  StatisticsRegistry::registerStat(&d_numUnknown);
  StatisticsRegistry::registerStat(&d_solveTime);
  StatisticsRegistry::registerStat(&d_useHeuristic);
}

AlgebraicSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numCallstoCheck);
  StatisticsRegistry::unregisterStat(&d_numSimplifiesToTrue);
  StatisticsRegistry::unregisterStat(&d_numSimplifiesToFalse);
  StatisticsRegistry::unregisterStat(&d_numUnsat);
  StatisticsRegistry::unregisterStat(&d_numSat);
  StatisticsRegistry::unregisterStat(&d_numUnknown);
  StatisticsRegistry::unregisterStat(&d_solveTime);
  StatisticsRegistry::unregisterStat(&d_useHeuristic);
}

bool hasExpensiveBVOperatorsRec(TNode fact, TNodeSet& seen) {
  if (fact.getKind() == kind::BITVECTOR_MULT ||
      fact.getKind() == kind::BITVECTOR_UDIV_TOTAL ||
      fact.getKind() == kind::BITVECTOR_UREM_TOTAL) {
    return true;
  }

  if (seen.find(fact) != seen.end())
    return false;
  
  if (fact.getNumChildren() == 0)
    return false;
  
  for (unsigned i = 0; i < fact.getNumChildren(); ++i) {
    bool difficult = hasExpensiveBVOperatorsRec(fact[i], seen);
    if (difficult)
      return true;
  }
  seen.insert(fact);
  return false;
}

bool hasExpensiveBVOperators(TNode fact) {
  TNodeSet seen;
  return hasExpensiveBVOperatorsRec(fact, seen);
}
