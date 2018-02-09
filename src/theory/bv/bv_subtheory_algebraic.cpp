/*********************                                                        */
/*! \file bv_subtheory_algebraic.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/
#include "theory/bv/bv_subtheory_algebraic.h"

#include "options/bv_options.h"
#include "smt/smt_statistics_registry.h"
#include "smt_util/boolean_simplification.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory_model.h"


using namespace CVC4::context;
using namespace CVC4::prop;
using namespace CVC4::theory::bv::utils;
using namespace std;

namespace CVC4 {
namespace theory {
namespace bv {


bool hasExpensiveBVOperators(TNode fact);
Node mergeExplanations(const std::vector<Node>& expls);
Node mergeExplanations(TNode expl1, TNode expl2);


SubstitutionEx::SubstitutionEx(theory::SubstitutionMap* modelMap)
  : d_substitutions()
  , d_cache()
  , d_cacheInvalid(true)
  , d_modelMap(modelMap)
{}

bool SubstitutionEx::addSubstitution(TNode from, TNode to, TNode reason) {
  Debug("bv-substitution") << "SubstitutionEx::addSubstitution: "<< from
                           <<" => "<< to << "\n" << " reason "<<reason << "\n";
  Assert (from != to);
  if (d_substitutions.find(from) != d_substitutions.end()) {
    return false;
  }

  d_modelMap->addSubstitution(from, to);

  d_cacheInvalid = true;
  d_substitutions[from] = SubstitutionElement(to, reason);
  return true;
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
      Node reason = mergeExplanations(reasons);
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
      Node reason = mergeExplanations(reasons);
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
  if(!hasCache(node)) {
    return utils::mkTrue();
  }

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
  , d_modelMap(NULL)
  , d_quickSolver(new BVQuickCheck("alg", bv))
  , d_isComplete(c, false)
  , d_isDifficult(c, false)
  , d_budget(options::bitvectorAlgebraicBudget())
  , d_explanations()
  , d_inputAssertions()
  , d_ids()
  , d_numSolved(0)
  , d_numCalls(0)
  , d_ctx(new context::Context())
  , d_quickXplain(options::bitvectorQuickXplain() ? new QuickXPlain("alg", d_quickSolver) : NULL)
  , d_statistics()
{}

AlgebraicSolver::~AlgebraicSolver() {
  if(d_modelMap != NULL) { delete d_modelMap; }
  delete d_quickXplain;
  delete d_quickSolver;
  delete d_ctx;
}



bool AlgebraicSolver::check(Theory::Effort e) {
  Assert(options::bitblastMode() == theory::bv::BITBLAST_MODE_LAZY);

  if (!Theory::fullEffort(e)) {
    return true;
  }

  if (!useHeuristic()) {
    return true;
  }

  ++(d_numCalls);

  TimerStat::CodeTimer algebraicTimer(d_statistics.d_solveTime);
  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check (" << e << ")\n";
  ++(d_statistics.d_numCallstoCheck);

  d_explanations.clear();
  d_ids.clear();
  d_inputAssertions.clear();

  std::vector<WorklistElement> worklist;

  uint64_t original_bb_cost = 0;

  NodeManager* nm = NodeManager::currentNM();
  NodeSet seen_assertions;
  // Processing assertions from scratch
  for (AssertionQueue::const_iterator it = assertionsBegin(); it != assertionsEnd(); ++it) {
    Debug("bv-subtheory-algebraic") << "   " << *it << "\n";
    TNode assertion = *it;
    unsigned id = worklist.size();
    d_ids[assertion] = id;
    worklist.push_back(WorklistElement(assertion, id));
    d_inputAssertions.insert(assertion);
    storeExplanation(assertion);

    uint64_t assertion_size = d_quickSolver->computeAtomWeight(assertion, seen_assertions);
    Assert (original_bb_cost <= original_bb_cost + assertion_size);
    original_bb_cost+= assertion_size;
  }

  for (unsigned i = 0; i < worklist.size(); ++i) {
    d_ids[worklist[i].node] = worklist[i].id;
  }

  Debug("bv-subtheory-algebraic") << "Assertions " << worklist.size() <<" : \n";

  Assert (d_explanations.size() == worklist.size());

  delete d_modelMap;
  d_modelMap = new SubstitutionMap(d_context);
  SubstitutionEx subst(d_modelMap);

  // first round of substitutions
  processAssertions(worklist, subst);

  if (!d_isDifficult.get()) {
    // skolemize all possible extracts
    ExtractSkolemizer skolemizer(d_modelMap);
    skolemizer.skolemize(worklist);
    // second round of substitutions
    processAssertions(worklist, subst);
  }

  NodeSet subst_seen;
  uint64_t subst_bb_cost = 0;

  unsigned r = 0;
  unsigned w = 0;

  for (; r < worklist.size(); ++r) {

    TNode fact = worklist[r].node;
    unsigned id = worklist[r].id;

    if (Dump.isOn("bv-algebraic")) {
      Node expl = d_explanations[id];
      Node query = utils::mkNot(nm->mkNode(kind::IMPLIES, expl, fact));
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
      Node conflict = BooleanSimplification::simplify(d_explanations[id]);
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
    worklist[w] = WorklistElement(fact, id);
    Node expl =  BooleanSimplification::simplify(d_explanations[id]);
    storeExplanation(id, expl);
    d_ids[fact] = id;
    ++w;
  }

  worklist.resize(w);


  if(Debug.isOn("bv-subtheory-algebraic")) {
    Debug("bv-subtheory-algebraic") << "Assertions post-substitutions " << worklist.size() << ":\n";
    for (unsigned i = 0; i < worklist.size(); ++i) {
      Debug("bv-subtheory-algebraic") << "   " << worklist[i].node << "\n";
    }
  }


  // all facts solved to true
  if (worklist.empty()) {
    Debug("bv-subtheory-algebraic") << " SAT: everything simplifies to true.\n";
    ++(d_statistics.d_numSimplifiesToTrue);
    ++(d_numSolved);
    return true;
  }

  double ratio = ((double)subst_bb_cost)/original_bb_cost;
  if (ratio > 0.5 ||
      !d_isDifficult.get()) {
    // give up if problem not reduced enough
    d_isComplete.set(false);
    return true;
  }

  d_quickSolver->clearSolver();

  d_quickSolver->push();
  std::vector<Node> facts;
  for (unsigned i = 0; i < worklist.size(); ++i) {
    facts.push_back(worklist[i].node);
  }
  bool ok = quickCheck(facts);

  Debug("bv-subtheory-algebraic") << "AlgebraicSolver::check done " << ok << ".\n";
  return ok;
}

bool AlgebraicSolver::quickCheck(std::vector<Node>& facts) {
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
  d_isComplete.set(true);
  Debug("bv-subtheory-algebraic") << " Unsat.\n";
  ++(d_numSolved);
  ++(d_statistics.d_numUnsat);


  Node conflict = d_quickSolver->getConflict();
  Debug("bv-subtheory-algebraic") << " Conflict: " << conflict << "\n";

  // singleton conflict
  if (conflict.getKind() != kind::AND) {
    Assert (d_ids.find(conflict) != d_ids.end());
    unsigned id = d_ids[conflict];
    Assert (id < d_explanations.size());
    Node theory_confl = d_explanations[id];
    d_bv->setConflict(theory_confl);
    return false;
  }

  Assert (conflict.getKind() == kind::AND);
  if (options::bitvectorQuickXplain()) {
    d_quickSolver->popToZero();
    Debug("bv-quick-xplain") << "AlgebraicSolver::quickCheck original conflict size " << conflict.getNumChildren() << "\n";
    conflict = d_quickXplain->minimizeConflict(conflict);
    Debug("bv-quick-xplain") << "AlgebraicSolver::quickCheck minimized conflict size " << conflict.getNumChildren() << "\n";
  }

  vector<TNode> theory_confl;
  for (unsigned i = 0; i < conflict.getNumChildren(); ++i) {
    TNode c = conflict[i];

    Assert (d_ids.find(c) != d_ids.end());
    unsigned c_id = d_ids[c];
    Assert (c_id < d_explanations.size());
    TNode c_expl = d_explanations[c_id];
    theory_confl.push_back(c_expl);
  }

  Node confl = BooleanSimplification::simplify(utils::mkAnd(theory_confl));

  Debug("bv-subtheory-algebraic") << " Out Conflict: " << confl << "\n";
  setConflict(confl);
  return false;
}

void AlgebraicSolver::setConflict(TNode conflict) {
  Node final_conflict = conflict;
  if (options::bitvectorQuickXplain() &&
      conflict.getKind() == kind::AND &&
      conflict.getNumChildren() > 4) {
    final_conflict = d_quickXplain->minimizeConflict(conflict);
  }
  d_bv->setConflict(final_conflict);
}

bool AlgebraicSolver::solve(TNode fact, TNode reason, SubstitutionEx& subst) {
  if (fact.getKind() != kind::EQUAL) return false;

  NodeManager* nm = NodeManager::currentNM();
  TNode left = fact[0];
  TNode right = fact[1];

  if (left.isVar() && !right.hasSubterm(left)) {
    bool changed  = subst.addSubstitution(left, right, reason);
    return changed;
  }
  if (right.isVar() && !left.hasSubterm(right)) {
    bool changed = subst.addSubstitution(right, left, reason);
    return changed;
  }

  // xor simplification
  if (right.getKind() == kind::BITVECTOR_XOR &&
      left.getKind() == kind::BITVECTOR_XOR) {
    TNode var = left[0];
    if (var.getMetaKind() != kind::metakind::VARIABLE)
      return false;

    // simplify xor with same variable on both sides
    if (right.hasSubterm(var)) {
      std::vector<Node> right_children;
      for (unsigned i = 0; i < right.getNumChildren(); ++i) {
        if (right[i] != var)
          right_children.push_back(right[i]);
      }
      Assert (right_children.size());
      Node new_right = utils::mkNaryNode(kind::BITVECTOR_XOR, right_children);
      std::vector<Node> left_children;
      for (unsigned i = 1; i < left.getNumChildren(); ++i) {
        left_children.push_back(left[i]);
      }
      Node new_left = utils::mkNaryNode(kind::BITVECTOR_XOR, left_children);
      Node new_fact = nm->mkNode(kind::EQUAL, new_left, new_right);
      bool changed = subst.addSubstitution(fact, new_fact, reason);
      return changed;
    }

    NodeBuilder<> nb(kind::BITVECTOR_XOR);
    for (unsigned i = 1; i < left.getNumChildren(); ++i) {
      nb << left[i];
    }
    Node inverse = left.getNumChildren() == 2? (Node)left[1] : (Node)nb;
    Node new_right = nm->mkNode(kind::BITVECTOR_XOR, right, inverse);
    bool changed = subst.addSubstitution(var, new_right, reason);

    if (Dump.isOn("bv-algebraic")) {
      Node query = utils::mkNot(nm->mkNode(
          kind::EQUAL, fact, nm->mkNode(kind::EQUAL, var, new_right)));
      Dump("bv-algebraic") << EchoCommand("ThoeryBV::AlgebraicSolver::substitution explanation");
      Dump("bv-algebraic") << PushCommand();
      Dump("bv-algebraic") << AssertCommand(query.toExpr());
      Dump("bv-algebraic") << CheckSatCommand();
      Dump("bv-algebraic") << PopCommand();
    }


    return changed;
  }

  // (a xor t = a) <=> (t = 0)
  if (left.getKind() == kind::BITVECTOR_XOR &&
      right.getMetaKind() == kind::metakind::VARIABLE &&
      left.hasSubterm(right)) {
    TNode var = right;
    Node new_left = nm->mkNode(kind::BITVECTOR_XOR, var, left);
    Node zero = utils::mkConst(utils::getSize(var), 0u);
    Node new_fact = nm->mkNode(kind::EQUAL, zero, new_left);
    bool changed = subst.addSubstitution(fact, new_fact, reason);
    return changed;
  }

  if (right.getKind() == kind::BITVECTOR_XOR &&
      left.getMetaKind() == kind::metakind::VARIABLE &&
      right.hasSubterm(left)) {
    TNode var = left;
    Node new_right = nm->mkNode(kind::BITVECTOR_XOR, var, right);
    Node zero = utils::mkConst(utils::getSize(var), 0u);
    Node new_fact = nm->mkNode(kind::EQUAL, zero, new_right);
    bool changed = subst.addSubstitution(fact, new_fact, reason);
    return changed;
  }

  // (a xor b = 0) <=> (a = b)
  if (left.getKind() == kind::BITVECTOR_XOR &&
      left.getNumChildren() == 2 &&
      right.getKind() == kind::CONST_BITVECTOR &&
      right.getConst<BitVector>() == BitVector(utils::getSize(left), 0u)) {
    Node new_fact = nm->mkNode(kind::EQUAL, left[0], left[1]);
    bool changed = subst.addSubstitution(fact, new_fact, reason);
    return changed;
  }


  return false;
}

bool AlgebraicSolver::isSubstitutableIn(TNode node, TNode in) {
  if (node.getMetaKind() == kind::metakind::VARIABLE &&
      !in.hasSubterm(node))
    return true;
  return false;
}

void AlgebraicSolver::processAssertions(std::vector<WorklistElement>& worklist, SubstitutionEx& subst) {
  NodeManager* nm = NodeManager::currentNM();
  bool changed = true;
  while(changed) {
    // d_bv->spendResource();
    changed = false;
    for (unsigned i = 0; i < worklist.size(); ++i) {
      // apply current substitutions
      Node current = subst.apply(worklist[i].node);
      unsigned current_id = worklist[i].id;
      Node subst_expl = subst.explain(worklist[i].node);
      worklist[i] = WorklistElement(Rewriter::rewrite(current), current_id);
      // explanation for this assertion
      Node old_expl = d_explanations[current_id];
      Node new_expl = mergeExplanations(subst_expl, old_expl);
      storeExplanation(current_id, new_expl);

      // use the new substitution to solve
      if(solve(worklist[i].node, new_expl, subst)) {
        changed = true;
      }
    }

    // check for concat slicings
    for (unsigned i = 0; i < worklist.size(); ++i) {
      TNode fact = worklist[i].node;
      unsigned current_id = worklist[i].id;

      if (fact.getKind() != kind::EQUAL) {
        continue;
      }

      TNode left = fact[0];
      TNode right = fact[1];
      if (left.getKind() != kind::BITVECTOR_CONCAT ||
          right.getKind() != kind::BITVECTOR_CONCAT ||
          left.getNumChildren() != right.getNumChildren()) {
        continue;
      }

      bool can_slice = true;
      for (unsigned j = 0; j < left.getNumChildren(); ++j) {
        if (utils::getSize(left[j]) != utils::getSize(right[j]))
          can_slice = false;
      }

      if (!can_slice) {
        continue;
      }

      for (unsigned j = 0; j < left.getNumChildren(); ++j) {
        Node eq_j = nm->mkNode(kind::EQUAL, left[j], right[j]);
        unsigned id = d_explanations.size();
        TNode expl = d_explanations[current_id];
        storeExplanation(expl);
        worklist.push_back(WorklistElement(eq_j, id));
        d_ids[eq_j] = id;
      }
      worklist[i] = WorklistElement(utils::mkTrue(), worklist[i].id);
      changed = true;
    }
    Assert (d_explanations.size() == worklist.size());
  }
}

void AlgebraicSolver::storeExplanation(unsigned id, TNode explanation) {
  Assert (checkExplanation(explanation));
  d_explanations[id] = explanation;
}

void AlgebraicSolver::storeExplanation(TNode explanation) {
  Assert (checkExplanation(explanation));
  d_explanations.push_back(explanation);
}

bool AlgebraicSolver::checkExplanation(TNode explanation) {
  Node simplified_explanation = explanation; //BooleanSimplification::simplify(explanation);
  if (simplified_explanation.getKind() != kind::AND) {
    return d_inputAssertions.find(simplified_explanation) != d_inputAssertions.end();
  }
  for (unsigned i = 0; i < simplified_explanation.getNumChildren(); ++i) {
    if (d_inputAssertions.find(simplified_explanation[i]) == d_inputAssertions.end()) {
      return false;
    }
  }
  return true;
}


bool AlgebraicSolver::isComplete() {
  return d_isComplete.get();
}

bool AlgebraicSolver::useHeuristic() {
  if (d_numCalls == 0)
    return true;

  double success_rate = double(d_numSolved)/double(d_numCalls);
  d_statistics.d_useHeuristic.setData(success_rate);
  return success_rate > 0.8;
}


void AlgebraicSolver::assertFact(TNode fact) {
  d_assertionQueue.push_back(fact);
  d_isComplete.set(false);
  if (!d_isDifficult.get()) {
    d_isDifficult.set(hasExpensiveBVOperators(fact));
  }
}

EqualityStatus AlgebraicSolver::getEqualityStatus(TNode a, TNode b) {
  return EQUALITY_UNKNOWN;
}
bool AlgebraicSolver::collectModelInfo(TheoryModel* model, bool fullModel)
{
  Debug("bitvector-model") << "AlgebraicSolver::collectModelInfo\n";
  AlwaysAssert (!d_quickSolver->inConflict());
  set<Node> termSet;
  d_bv->computeRelevantTerms(termSet);

  // collect relevant terms that the bv theory abstracts to variables
  // (variables and parametric terms such as select apply_uf)
  std::vector<TNode> variables;
  std::vector<Node> values;
  for (set<Node>::const_iterator it = termSet.begin(); it != termSet.end(); ++it) {
    TNode term = *it;
    if (term.getType().isBitVector() &&
        (term.getMetaKind() == kind::metakind::VARIABLE ||
         Theory::theoryOf(term) != THEORY_BV)) {
      variables.push_back(term);
      values.push_back(term);
    }
  }

  NodeSet leaf_vars;
  Debug("bitvector-model") << "Substitutions:\n";
  for (unsigned i = 0; i < variables.size(); ++i) {
    TNode current = variables[i];
    TNode subst = Rewriter::rewrite(d_modelMap->apply(current));
    Debug("bitvector-model") << "   " << current << " => " << subst << "\n";
    values[i] = subst;
    utils::collectVariables(subst, leaf_vars);
  }

  Debug("bitvector-model") << "Model:\n";

  for (NodeSet::const_iterator it = leaf_vars.begin(); it != leaf_vars.end(); ++it) {
    TNode var = *it;
    Node value = d_quickSolver->getVarValue(var, true);
    Assert (!value.isNull() || !fullModel);

    // may be a shared term that did not appear in the current assertions
    // AJR: need to check whether already in map for cases where collectModelInfo is called multiple times in the same context
    if (!value.isNull() && !d_modelMap->hasSubstitution(var)) {
      Debug("bitvector-model") << "   " << var << " => " << value << "\n";
      Assert (value.getKind() == kind::CONST_BITVECTOR);
      d_modelMap->addSubstitution(var, value);
    }
  }

  Debug("bitvector-model") << "Final Model:\n";
  for (unsigned i = 0; i < variables.size(); ++i) {
    TNode current = values[i];
    TNode subst = Rewriter::rewrite(d_modelMap->apply(current));
    Debug("bitvector-model") << "AlgebraicSolver:   " << variables[i] << " => " << subst << "\n";
    // Doesn't have to be constant as it may be irrelevant
    Assert (subst.getKind() == kind::CONST_BITVECTOR);
    if (!model->assertEquality(variables[i], subst, true))
    {
      return false;
    }
  }
  return true;
 }

Node AlgebraicSolver::getModelValue(TNode node) {
  return Node::null();
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
  smtStatisticsRegistry()->registerStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->registerStat(&d_numSimplifiesToTrue);
  smtStatisticsRegistry()->registerStat(&d_numSimplifiesToFalse);
  smtStatisticsRegistry()->registerStat(&d_numUnsat);
  smtStatisticsRegistry()->registerStat(&d_numSat);
  smtStatisticsRegistry()->registerStat(&d_numUnknown);
  smtStatisticsRegistry()->registerStat(&d_solveTime);
  smtStatisticsRegistry()->registerStat(&d_useHeuristic);
}

AlgebraicSolver::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->unregisterStat(&d_numSimplifiesToTrue);
  smtStatisticsRegistry()->unregisterStat(&d_numSimplifiesToFalse);
  smtStatisticsRegistry()->unregisterStat(&d_numUnsat);
  smtStatisticsRegistry()->unregisterStat(&d_numSat);
  smtStatisticsRegistry()->unregisterStat(&d_numUnknown);
  smtStatisticsRegistry()->unregisterStat(&d_solveTime);
  smtStatisticsRegistry()->unregisterStat(&d_useHeuristic);
}

bool hasExpensiveBVOperatorsRec(TNode fact, TNodeSet& seen) {
  if (fact.getKind() == kind::BITVECTOR_MULT ||
      fact.getKind() == kind::BITVECTOR_UDIV_TOTAL ||
      fact.getKind() == kind::BITVECTOR_UREM_TOTAL) {
    return true;
  }

  if (seen.find(fact) != seen.end()) {
    return false;
  }

  if (fact.getNumChildren() == 0) {
    return false;
  }
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

void ExtractSkolemizer::skolemize(std::vector<WorklistElement>& facts) {
  TNodeSet seen;
  for (unsigned i = 0; i < facts.size(); ++i) {
    TNode current = facts[i].node;
    collectExtracts(current, seen);
  }

  for (VarExtractMap::iterator it = d_varToExtract.begin(); it != d_varToExtract.end(); ++it) {
    ExtractList& el = it->second;
    TNode var = it->first;
    Base& base = el.base;

    unsigned bw = utils::getSize(var);
    // compute decomposition
    std::vector<unsigned> cuts;
    for (unsigned i = 1; i <= bw; ++i) {
      if (base.isCutPoint(i)) {
        cuts.push_back(i);
      }
    }
    unsigned previous = 0;
    unsigned current = 0;
    std::vector<Node> skolems;
    for (unsigned i = 0; i < cuts.size(); ++i) {
      current = cuts[i];
      Assert (current > 0);
      int size = current - previous;
      Assert (size > 0);
      Node sk = utils::mkVar(size);
      skolems.push_back(sk);
      previous = current;
    }
    if (current < bw -1) {
      int size = bw - current;
      Assert (size > 0);
      Node sk = utils::mkVar(size);
      skolems.push_back(sk);
    }
    NodeBuilder<> skolem_nb(kind::BITVECTOR_CONCAT);

    for (int i = skolems.size() - 1; i >= 0; --i) {
      skolem_nb << skolems[i];
    }

    Node skolem_concat = skolems.size() == 1 ? (Node)skolems[0] : (Node) skolem_nb;
    Assert (utils::getSize(skolem_concat) == utils::getSize(var));
    storeSkolem(var, skolem_concat);

    for (unsigned i = 0; i < el.extracts.size(); ++i) {
      unsigned h = el.extracts[i].high;
      unsigned l = el.extracts[i].low;
      Node extract = utils::mkExtract(var, h, l);
      Node skolem_extract = Rewriter::rewrite(utils::mkExtract(skolem_concat, h, l));
      Assert (skolem_extract.getMetaKind() == kind::metakind::VARIABLE ||
              skolem_extract.getKind() == kind::BITVECTOR_CONCAT);
      storeSkolem(extract, skolem_extract);
    }
  }

  for (unsigned i = 0; i < facts.size(); ++i) {
    facts[i] = WorklistElement(skolemize(facts[i].node), facts[i].id);
  }
}

Node ExtractSkolemizer::mkSkolem(Node node) {
  Assert (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getMetaKind() == kind::metakind::VARIABLE);
  Assert (!d_skolemSubst.hasSubstitution(node));
  return utils::mkVar(utils::getSize(node));
}

void ExtractSkolemizer::unSkolemize(std::vector<WorklistElement>& facts) {
  for (unsigned i = 0; i < facts.size(); ++i) {
    facts[i] = WorklistElement(unSkolemize(facts[i].node), facts[i].id);
  }
}

void ExtractSkolemizer::storeSkolem(TNode node, TNode skolem) {
  d_skolemSubst.addSubstitution(node, skolem);
  d_modelMap->addSubstitution(node, skolem);
  d_skolemSubstRev.addSubstitution(skolem, node);
}

Node ExtractSkolemizer::unSkolemize(TNode node) {
  return d_skolemSubstRev.apply(node);
}

Node ExtractSkolemizer::skolemize(TNode node) {
  return d_skolemSubst.apply(node);
}

void ExtractSkolemizer::ExtractList::addExtract(Extract& e) {
  extracts.push_back(e);
  base.sliceAt(e.low);
  base.sliceAt(e.high+1);
}

void ExtractSkolemizer::storeExtract(TNode var, unsigned high, unsigned low) {
  Assert (var.getMetaKind() == kind::metakind::VARIABLE);
  if (d_varToExtract.find(var) == d_varToExtract.end()) {
    d_varToExtract[var] = ExtractList(utils::getSize(var));
  }
  VarExtractMap::iterator it = d_varToExtract.find(var);
  ExtractList& el = it->second;
  Extract e(high, low);
  el.addExtract(e);
}

void ExtractSkolemizer::collectExtracts(TNode node, TNodeSet& seen) {
  if (seen.find(node) != seen.end()) {
    return;
  }

  if (node.getKind() == kind::BITVECTOR_EXTRACT &&
      node[0].getMetaKind() == kind::metakind::VARIABLE) {
    unsigned high = utils::getExtractHigh(node);
    unsigned low = utils::getExtractLow(node);
    TNode var = node[0];
    storeExtract(var, high, low);
    seen.insert(node);
    return;
  }

  if (node.getNumChildren() == 0)
    return;

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectExtracts(node[i], seen);
  }
  seen.insert(node);
}

ExtractSkolemizer::ExtractSkolemizer(theory::SubstitutionMap* modelMap)
  : d_emptyContext()
  , d_varToExtract()
  , d_modelMap(modelMap)
  , d_skolemSubst(&d_emptyContext)
  , d_skolemSubstRev(&d_emptyContext)
{}

ExtractSkolemizer::~ExtractSkolemizer() {
}

Node mergeExplanations(const std::vector<Node>& expls) {
  TNodeSet literals;
  for (unsigned i = 0; i < expls.size(); ++i) {
    TNode expl = expls[i];
    Assert (expl.getType().isBoolean());
    if (expl.getKind() == kind::AND) {
      for (unsigned i = 0; i < expl.getNumChildren(); ++i) {
        TNode child = expl[i];
        if (child == utils::mkTrue())
          continue;
        literals.insert(child);
      }
    } else if (expl != utils::mkTrue()) {
      literals.insert(expl);
    }
  }

  if (literals.size() == 0) {
    return utils::mkTrue();
  }else if (literals.size() == 1) {
    return *literals.begin();
  }

  NodeBuilder<> nb(kind::AND);

  for (TNodeSet::const_iterator it = literals.begin(); it!= literals.end(); ++it) {
    nb << *it;
  }
  return nb;
}

Node mergeExplanations(TNode expl1, TNode expl2) {
  std::vector<Node> expls;
  expls.push_back(expl1);
  expls.push_back(expl2);
  return mergeExplanations(expls);
}

} /* namespace CVC4::theory::bv */
} /* namespace CVc4::theory */
} /* namespace CVC4 */
