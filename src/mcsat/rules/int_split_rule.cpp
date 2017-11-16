#include "theory/rewriter.h"
#include "mcsat/rules/int_split_rule.h"

using namespace CVC4;
using namespace mcsat;
using namespace rules;

IntSplitRule::IntSplitRule(ClauseDatabase& clauseDB, const SolverTrail& trail, StatisticsRegistry* registry) 
: ProofRule("mcsat::int_split_rule", clauseDB, trail, registry)
{
}

static Literal getLiteral(Node node) {
  node = theory::Rewriter::rewrite(node);
  bool negated = node.getKind() == kind::NOT;
  Node atom = negated ? node[0] : node;
  Variable variable = VariableDatabase::getCurrentDB()->getVariable(atom);
  return Literal(variable, negated);
}

CRef IntSplitRule::split(Variable x, SolverTrail::PropagationToken& propToken) {
  unsigned level = d_trail.decisionLevel(x);
  
  Rational r = d_trail.value(x).getConst<Rational>();  
  Integer a = r.floor();
  Integer b = a + 1;

  NodeManager* nm = NodeManager::currentNM(); 
  
  Node x_node = x.getNode();
  Node a_node = nm->mkConst<Rational>(a);
  Node b_node = nm->mkConst<Rational>(b);
  Node x_lte_a = nm->mkNode(kind::LEQ, x_node, a_node);
  Node x_gte_b = nm->mkNode(kind::GEQ, x_node, b_node);

  std::vector<Literal> lits;
  Literal l1 = getLiteral(x_lte_a);
  lits.push_back(l1);
  Literal l2 = getLiteral(x_gte_b);
  lits.push_back(l2);

  propToken(~l1, level);
  propToken(~l2, level);
  
  return commit(lits);
}
