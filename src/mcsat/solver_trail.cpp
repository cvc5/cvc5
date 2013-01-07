#include "mcsat/solver_trail.h"
#include "mcsat/clause/clause_db.h"
#include "mcsat/variable/variable_db.h"
#include "mcsat/options.h"

#include "theory/rewriter.h"
#include "util/node_visitor.h"

using namespace CVC4;
using namespace CVC4::mcsat;

SolverTrail::SolverTrail(context::Context* context)
: d_decisionLevel(0)
, d_cacheTimestamp(1)
, d_context(context)
{
  c_TRUE = NodeManager::currentNM()->mkConst<bool>(true);
  c_FALSE = NodeManager::currentNM()->mkConst<bool>(false);

  Variable varTrue = VariableDatabase::getCurrentDB()->getVariable(c_TRUE);
  Variable varFalse = VariableDatabase::getCurrentDB()->getVariable(c_FALSE);

  // Propagate out TRUE and !FALSE
  PropagationToken out(*this, PropagationToken::PROPAGATION_INIT);
  Literal l1(varTrue, false);
  Literal l2(varFalse, true);
  out(l1, 0u);
  out(l2, 0u);
}

SolverTrail::~SolverTrail() {
}

struct SubstituteVisitor {
  const SolverTrail& trail;
  unsigned level;
  std::hash_map<TNode, Node, TNodeHashFunction> d_evaluation;
public:
  SubstituteVisitor(const SolverTrail& trail, unsigned level) 
  : trail(trail), level(level) {}
  
  typedef Node return_type;

  bool alreadyVisited(TNode current, TNode parent) const {
    return d_evaluation.find(current) != d_evaluation.end();
  }

  void visit(TNode current, TNode parent) {
    if (current.isConst()) {
      d_evaluation[current] = current;
      return;
    }
    if (VariableDatabase::getCurrentDB()->hasVariable(current)) {
      Variable var = VariableDatabase::getCurrentDB()->getVariable(current);
      if (trail.hasValue(var) && trail.decisionLevel(var) <= level) {
	d_evaluation[current] = trail.value(var);
      } else {
	d_evaluation[current] = current;
      }
      return;
    }
    NodeBuilder<> nb(current.getKind());
    for (unsigned i = 0; i < current.getNumChildren(); ++ i) {
      nb << d_evaluation[current[i]];
    }
    Node result = nb;
    d_evaluation[current] = theory::Rewriter::rewrite(result);
  }

  void start(TNode node) {}
  
  Node done(TNode node) {
    return d_evaluation[node];
  }
};
  
Node SolverTrail::evaluate(Literal l, unsigned level) const {
  Node atom = l.getVariable().getNode();
  Node node = l.isNegated() ? atom.notNode() : atom;
  SubstituteVisitor visitor(*this, level);
  Node eval = NodeVisitor<SubstituteVisitor>::run(visitor, node);
  return eval;
}

void SolverTrail::newDecision() {
  Assert(consistent());

  d_context->push();
  d_decisionLevel ++;
  d_decisionTrail.push_back(d_trail.size());
}

void SolverTrail::popDecision(std::vector<Variable>& variablesUnset) {

  Assert(d_decisionTrail.size() > 0);

  if (Debug.isOn("mcsat::trail")) {
    if (!checkConsistency()) {
      Debug("mcsat::trail") << *this << std::endl;
      Assert(false);
    }
  }

  // Pop the trail elements
  while (d_trail.size() > d_decisionTrail.back()) {
    const Element& e = d_trail.back();
    if (e.type == SolverTrail::SEMANTIC_PROPAGATION) {
      d_semanticRepropagate.push_back(RepropagateInfo(e.var, isTrue(e.var), decisionLevel(e.var)));
    }
    unsetValue(e);
    variablesUnset.push_back(e.var);
    d_trail.pop_back();
  }

  // Update the info
  d_decisionTrail.pop_back();
  d_decisionLevel --;
  d_context->pop();

  // If we were inconsistent, not anymore
  d_inconsistentPropagations.clear();

  if (Debug.isOn("mcsat::trail")) {
    if (!checkConsistency()) {
      Debug("mcsat::trail") << *this << std::endl;
      Assert(false);
    }
  }
}

void SolverTrail::popToLevel(unsigned level, std::vector<Variable>& variablesUnset) {
  Debug("mcsat::trail") << "SolverTrail::popToLevel(" << level << "): at level " << d_decisionLevel << std::endl;

  // Pop to the given level
  while (d_decisionLevel > level) {
    popDecision(variablesUnset);
  }

  // Repropagate all the semantic propagations valid at this level
  PropagationToken out(*this, PropagationToken::PROPAGATION_INIT);
  for (unsigned i = 0; i < d_semanticRepropagate.size(); ++ i) {
    const RepropagateInfo& info = d_semanticRepropagate[i];
    if (info.level <= level) {
      out(Literal(info.var, !info.value), info.level);
    }
  }
  d_semanticRepropagate.clear();

  Debug("mcsat::trail") << "SolverTrail::popToLevel(" << level << "): new trail: " << *this << std::endl;
}

void SolverTrail::addNewClauseListener(ClauseDatabase::INewClauseNotify* listener) const {
  for (unsigned i = 0; i < d_clauses.size(); ++ i) {
    d_clauses[i]->addNewClauseListener(listener);
  }
}

unsigned SolverTrail::decisionLevel(Variable var) const {
  Assert(!value(var).isNull());
  return d_modelInfo[var].decisionLevel;
}

unsigned SolverTrail::trailIndex(Variable var) const {
  Assert(!value(var).isNull());
  return d_modelInfo[var].trailIndex;
}

CVC4_UNUSED static bool ensureTrue(const SolverTrail& trail, Literal l) {
  if (!trail.hasValue(l.getVariable())) {
    Debug("mcsat::trail::error") << trail << std::endl;
    Debug("mcsat::trail::error") << l << " does not have a value" << std::endl;
    return false;
  }

  if (!trail.isTrue(l)) {
    Debug("mcsat::trail::error") << trail << std::endl;
    Debug("mcsat::trail::error") << l << " is not true" << std::endl;
    return false;
  }
  return true;
}

void SolverTrail::PropagationToken::operator () (Literal l, unsigned level) {

  Debug("mcsat::trail") << "PropagationToken::operator () (" << l << ", " << level << ")" << std::endl;

  // Assert(d_trail.evaluatesToTrue(l, level));
  
  d_used = true;

  if (!d_trail.hasValue(l.getVariable())) {
    Assert(level <= d_trail.decisionLevel());
    Assert(true); // TODO: Check that l evaluates to true in the model

    if (l.isNegated()) {
      d_trail.setValue(l.getVariable(), d_trail.c_FALSE, false);
    } else {
      d_trail.setValue(l.getVariable(), d_trail.c_TRUE, false);
    }
    Variable var = l.getVariable();

    d_trail.d_modelInfo[var].decisionLevel = level;
    d_trail.d_modelInfo[var].trailIndex = d_trail.d_trail.size();
    d_trail.d_trail.push_back(Element(SEMANTIC_PROPAGATION, var));
  } else {
    Assert(ensureTrue(d_trail, l));
  }
}

CVC4_UNUSED static bool clausePropagates(Literal l, CRef reason, SolverTrail& trail) {
  Clause& clause = reason.getClause();
  if (clause[0] != l) {
    return false;
  }
  for (unsigned i = 1; i < clause.size(); ++ i) {
    if (!trail.isFalse(clause[i])) {
      return false;
    }
  }
  return true;
}

void SolverTrail::PropagationToken::operator () (Literal l, CRef reason) {

  Debug("mcsat::trail") << "PropagationToken::operator () (" << l << ", " << reason << ")" << std::endl;
  // Assert(!d_trail.evaluatesToFalse(l, d_trail.decisionLevel()) || d_trail.isFalse(l));

  d_used = true;

  Assert(clausePropagates(l, reason, d_trail));
  
  // If new propagation, record in model and in trail
  if (!d_trail.isTrue(l)) {
    // Check that we're not in conflict with this propagation
    if (d_trail.isFalse(l)) {
      // Conflict
      Debug("mcsat::trail") << "PropagationToken::operator () (" << l << ", " << reason << "): conflict" << std::endl;
      d_trail.d_inconsistentPropagations.push_back(InconsistentPropagation(l, reason));
    } else {
      // No conflict, remember the l value in the model
      if (l.isNegated()) {
	d_trail.setValue(l.getVariable(), d_trail.c_FALSE, false);
      } else {
	d_trail.setValue(l.getVariable(), d_trail.c_TRUE, false);
      }
      // Set the model information
      Variable var = l.getVariable();
      d_trail.d_modelInfo[var].decisionLevel = d_trail.decisionLevel();
      d_trail.d_modelInfo[var].trailIndex = d_trail.d_trail.size();
      // Remember the reason
      d_trail.d_clauseReasons[l] = reason;
      d_trail.d_reasonProviders[l] = &d_trail.d_clauseReasons;
      // Push to the trail
      d_trail.d_trail.push_back(Element(CLAUSAL_PROPAGATION, var));
    }
  } 
}

void SolverTrail::PropagationToken::operator () (Literal l, ReasonProvider* reason_provider) {

  Debug("mcsat::trail") << "PropagationToken::operator () (" << l << ", with lazy reason)" << std::endl;
  // Assert(!d_trail.evaluatesToFalse(l, d_trail.decisionLevel()) || d_trail.isFalse(l));

  d_used = true;

    // If new propagation, record in model and in trail
  if (!d_trail.isTrue(l)) {
    // Check that we're not in conflict with this propagation
    if (d_trail.isFalse(l)) {
      // Conflict
      Debug("mcsat::trail") << "PropagationToken::operator () (" << l << ", with lazy reason): conflict" << std::endl;
      CRef reason = reason_provider->explain(l, *this);
      d_trail.d_inconsistentPropagations.push_back(InconsistentPropagation(l, reason));
    } else {
      // No conflict, remember the l value in the model
      if (l.isNegated()) {
        d_trail.setValue(l.getVariable(), d_trail.c_FALSE, false);
      } else {
        d_trail.setValue(l.getVariable(), d_trail.c_TRUE, false);
      }
      // Set the model information
      Variable var = l.getVariable();
      d_trail.d_modelInfo[var].decisionLevel = d_trail.decisionLevel();
      d_trail.d_modelInfo[var].trailIndex = d_trail.d_trail.size();
      // Remember the reason
      d_trail.d_reasonProviders[l] = reason_provider;
      // Push to the trail
      d_trail.d_trail.push_back(Element(CLAUSAL_PROPAGATION, var));
    }
  }
}


void SolverTrail::DecisionToken::operator () (Literal l) {
  Assert(!d_used);
  Assert(d_trail.consistent());
  Assert(d_trail.d_model[l.getVariable()].isNull());
  Assert(!d_trail.evaluatesToFalse(l, d_trail.decisionLevel()));

  Debug("mcsat::trail") << "DecisionToken::operator () (" << l << ")" << std::endl;

  d_trail.newDecision();
  d_used = true;

  if (l.isNegated()) {
    d_trail.setValue(l.getVariable(), d_trail.c_FALSE, false);
  } else {
    d_trail.setValue(l.getVariable(), d_trail.c_TRUE, false);
  }
  // Set the model information
  Variable var = l.getVariable();
  d_trail.d_modelInfo[var].decisionLevel = d_trail.decisionLevel();
  d_trail.d_modelInfo[var].trailIndex = d_trail.d_trail.size();
  // Push to the trail
  d_trail.d_trail.push_back(Element(BOOLEAN_DECISION, l.getVariable()));
}

void SolverTrail::DecisionToken::operator () (Variable var, TNode val, bool track, bool fixed) {
  Assert(!d_used);
  Assert(d_trail.consistent());
  Assert(d_trail.d_model[var].isNull());

  Debug("mcsat::trail") << "DecisionToken::operator () (" << var << ", " << val << ")" << std::endl;

  if (!fixed || d_trail.decisionLevel() > 0) {
    d_trail.newDecision();
  }
  d_used = true;

  d_trail.setValue(var, val, track);

  // Set the model information
  d_trail.d_modelInfo[var].decisionLevel = d_trail.decisionLevel();
  d_trail.d_modelInfo[var].trailIndex = d_trail.d_trail.size();
  // Push to the trail
  d_trail.d_trail.push_back(Element(SEMANTIC_DECISION, var));
}

bool SolverTrail::hasReason(Literal literal) const {
  // You can resolve with l if ~l has been propagated true with a clausal reason
  return d_reasonProviders[literal] != 0;
}

bool SolverTrail::hasClausalReason(Literal literal) const {
  // You can resolve with l if ~l has been propagated true with a clausal reason
  return d_reasonProviders[literal] == &d_clauseReasons;
}


CRef SolverTrail::reason(Literal literal) {
  Assert(hasReason(literal));
  ReasonProvider* reasonProvider = d_reasonProviders[literal];
  PropagationToken out(*this, PropagationToken::PROPAGATION_INIT);
  CRef reason = reasonProvider->explain(literal, out);
  // If not a clausal reason provider, remember just in case
  if (reasonProvider != &d_clauseReasons) {
    d_clauseReasons[literal] = reason;
    d_reasonProviders[literal] = &d_clauseReasons;
  }
  // Return the explanation
  return reason;
}

void SolverTrail::getInconsistentPropagations(std::vector<InconsistentPropagation>& out) const {
  out.clear();
  for (unsigned i = 0; i < d_inconsistentPropagations.size(); ++ i) {
    out.push_back(d_inconsistentPropagations[i]);
  }
}

void SolverTrail::toStream(std::ostream& out) const {
  out << "Trail[";
  unsigned level = 0;
  for (unsigned i = 0; i < d_trail.size(); ++ i) {
    if (d_trail[i].isDecision() || i == 0) {
      out << std::endl << level++ << "\t";
    } else {
      out << ", ";
    }
    out << i << ":";
    TNode v = value(d_trail[i].var);
    if (v.getType().isBoolean()) {
      Literal l(d_trail[i].var, v == c_FALSE);
      out << "[" << l << "]";
    } else {
      out << "[" << d_trail[i].var << " -> " << v << "]";
    }
  }
  out << std::endl << "]";
}

bool SolverTrail::checkConsistency() const {
  for (unsigned i = 0; i < d_trail.size(); ++ i) {
    const Element& e = d_trail[i];
    switch (e.type) {
    case BOOLEAN_DECISION:
      // Decisions don't have reasons
      if (hasReason(Literal(e.var, isFalse(e.var)))) {
        Debug("mcsat::trail") << "SolverTrail::checkConsistency(): decision at " << i << " has a reason!!!" << std::endl;
        return false;
      }
      break;
    case SEMANTIC_DECISION:
      // No Booleans here
      if (e.var.getNode().getType().isBoolean()) {
        Debug("mcsat::trail") << "SolverTrail::checkConsistency(): semantic decision at " << i << " is Boolean!!!" << std::endl;
        return false;
      }
      // Same type as the assignment
      if (!e.var.getNode().getType().isComparableTo(value(e.var).getType())) {
        Debug("mcsat::trail") << "SolverTrail::checkConsistency(): semantic decision at " << i << " of different type!!!" << std::endl;
        return false;
      }
      break;
    case CLAUSAL_PROPAGATION:
      // Clausal propagations must have reasons
      if (!hasReason(Literal(e.var, isFalse(e.var)))) {
        Debug("mcsat::trail") << "SolverTrail::checkConsistency(): clausal propagation with no reason at " << i << "!!!" << std::endl;
        return false;
      }
      break;
    case SEMANTIC_PROPAGATION:
      // Semantic propagations don't have reasons
      if (hasReason(Literal(e.var, isFalse(e.var)))) {
        Debug("mcsat::trail") << "SolverTrail::checkConsistency(): semantic propagation with reason" << i << "!!!" << std::endl;
        return false;
      }
      break;
    }
  }

  return true;
}

void SolverTrail::gcMark(std::set<Variable>& varsToKeep, std::set<CRef>& clausesToKeep) {
  // The trail cares about variables in the trail and any clauses that are in the clausal reasons
  for(unsigned i = 0; i < d_trail.size(); ++i) {
    Variable var = d_trail[i].var;
    if(d_trail[i].hasReason()) {
      Literal l(var, !isTrue(var));
      if(d_reasonProviders[l] == &d_clauseReasons) {
        // For clausal reasons, it's enough to keep the clause, the variable is part of the clause
        // so it gets kept
        clausesToKeep.insert(d_clauseReasons[l]);
      } else {
        // We don't have a reason yet, keep the variable
        varsToKeep.insert(var);
      }
    } else {
      varsToKeep.insert(var);
    }
  }
}

void SolverTrail::gcRelocate(const VariableGCInfo& vReloc, const ClauseRelocationInfo& cReloc) {
  // The trail cares about variables in the trail and any clauses that are in the clausal reasons
  for(unsigned i = 0; i < d_trail.size(); ++i) {
    Variable var = d_trail[i].var;
    if(d_trail[i].hasReason()) {
      Literal l(var, !isTrue(var));
      if(d_reasonProviders[l] == &d_clauseReasons) {
        d_clauseReasons[l] = cReloc.relocate(d_clauseReasons[l]);
      }
    }
  }
}

bool SolverTrail::satisfies(CRef cRef) const {
  Clause& clause = cRef.getClause();
  for (unsigned i = 0; i < clause.size(); ++ i) {
    if (isTrue(clause[i])) {
      return true;
    }
  }
  return false;
}

void SolverTrail::removeSatisfied(std::vector<CRef>& clauses) const {
  unsigned toKeep = 0;
  for (unsigned i = 0; i < clauses.size(); ++ i) {
    if (!satisfies(clauses[i])) {
      clauses[toKeep ++] = clauses[i];
    }
  }
  clauses.resize(toKeep);
}
