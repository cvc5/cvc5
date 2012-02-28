#include "theory/arith/difference_manager.h"
#include "theory/uf/equality_engine_impl.h"

namespace CVC4 {
namespace theory {
namespace arith {

DifferenceManager::DifferenceManager(context::Context* c, PropManager& pm)
  : d_literalsQueue(c),
    d_queue(pm),
    d_notify(*this),
    d_ee(d_notify, c, "theory::arith::DifferenceManager"),
    d_false(NodeManager::currentNM()->mkConst<bool>(false)),
    d_hasSharedTerms(c, false)
{}

void DifferenceManager::propagate(TNode x){
  Debug("arith::differenceManager")<< "DifferenceManager::propagate("<<x<<")"<<std::endl;

  d_queue.propagate(x, explain(x), true);
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
  d_ee.explainEquality(lhs, rhs, assumptions);
}

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

void DifferenceManager::addAssertionToEqualityEngine(bool eq, ArithVar s, TNode reason){
  Assert(isDifferenceSlack(s));

  TNode x = d_differences[s].x;
  TNode y = d_differences[s].y;

  if(eq){
    d_ee.addEquality(x, y, reason);
  }else{
    d_ee.addDisequality(x, y, reason);
  }
}

void DifferenceManager::dequeueLiterals(){
  Assert(d_hasSharedTerms);
  while(!d_literalsQueue.empty()){
    const LiteralsQueueElem& front = d_literalsQueue.dequeue();

    addAssertionToEqualityEngine(front.d_eq, front.d_var, front.d_reason);
  }
}

void DifferenceManager::enableSharedTerms(){
  Assert(!d_hasSharedTerms);
  d_hasSharedTerms = true;
  dequeueLiterals();
}

void DifferenceManager::assertLiteral(bool eq, ArithVar s, TNode reason){
  d_literalsQueue.enqueue(LiteralsQueueElem(eq, s, reason));
  if(d_hasSharedTerms){
    dequeueLiterals();
  }
}

void DifferenceManager::addSharedTerm(Node x){
  if(!d_hasSharedTerms){
    enableSharedTerms();
  }
  d_ee.addTriggerTerm(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
