#include "theory/arith/difference_manager.h"
#include "theory/uf/equality_engine_impl.h"

namespace CVC4 {
namespace theory {
namespace arith {

DifferenceManager::DifferenceManager(context::Context* c, PropManager& pm)
  : d_reasons(c),
    d_queue(pm),
    d_notify(*this),
    d_ee(d_notify, c, "theory::arith::DifferenceManager"),
    d_false(NodeManager::currentNM()->mkConst<bool>(false))
{}

void DifferenceManager::propagate(TNode x){
  Debug("arith::differenceManager")<< "DifferenceManager::propagate("<<x<<")"<<std::endl;

  d_queue.propagate(x, Node::null(), true);
}

void DifferenceManager::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::NOT:
      lhs = literal[0];
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_ee.getExplanation(lhs, rhs, assumptions);
}

#warning "Stolen from theory_uf.h verbatim. Generalize me!"
Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}


Node DifferenceManager::explain(TNode lit){
  std::vector<TNode> assumptions;
  explain(lit, assumptions);
  return mkAnd(assumptions);
}

void DifferenceManager::addDifference(ArithVar s, Node x, Node y){
  Assert(s >= d_differences.size() || !isDifferenceSlack(s));

  Debug("arith::differenceManager") << s << x << y << std::endl;

  d_differences.resize(s+1);
  d_differences[s] = Difference(x,y);
}

void DifferenceManager::differenceIsZero(ArithVar s, TNode reason){
  Assert(isDifferenceSlack(s));
  TNode x = d_differences[s].x;
  TNode y = d_differences[s].y;

  d_reasons.push_back(reason);
  d_ee.addEquality(x, y, reason);
}

void DifferenceManager::differenceCannotBeZero(ArithVar s, TNode reason){
  Assert(isDifferenceSlack(s));
  TNode x = d_differences[s].x;
  TNode y = d_differences[s].y;

  d_reasons.push_back(reason);
  d_ee.addDisequality(x, y, reason);
}

void DifferenceManager::addSharedTerm(Node x){
  d_ee.addTriggerTerm(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
