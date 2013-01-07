#pragma once

#include "mcsat/variable/variable.h"
#include "mcsat/variable/variable_db.h"

#include <boost/integer_traits.hpp>

namespace CVC4 {
namespace mcsat {
namespace util {

/**
 * A priority queue for the variables of certain types.
 */
class VariablePriorityQueue {

  /** The heap elements */
  std::vector<Variable> d_heapElements;
  
  /** Scores of variables */
  std::vector< std::vector<double> > d_variableScores;

  double& var_score(Variable var) {
    return d_variableScores[var.typeIndex()][var.index()];
  }

  double var_score(Variable var) const {
    return d_variableScores[var.typeIndex()][var.index()];
  }

  /** Null index in the heap */
  static const unsigned null_index = boost::integer_traits<unsigned>::const_max;
  
  /** Positions of the variables in the heap */
  std::vector< std::vector<unsigned> > d_variableIndices;

  unsigned& var_index(Variable var) {
    return d_variableIndices[var.typeIndex()][var.index()];
  }

  unsigned var_index(Variable var) const {
    return d_variableIndices[var.typeIndex()][var.index()];
  }

  /**
   * Max over the score of all the variables (even the ones not currently in
   * the queue).
   */
  double d_variableScoresMax;

  /** Percolate the given variable up */
  void percolateUp(Variable var);

  /** Percolate the given variable down */
  void percolateDown(Variable var);
  
  /** Remove the variable */
  void remove(Variable var);
  
  /** 
   * Compare variables according to their current score 
   * @return true if v1 > v2
   */
  bool cmp(const Variable& v1, const Variable& v2) const {
    double v1_score = var_score(v1);
    double v2_score = var_score(v2);
    if (v1_score == v2_score) {
      return v1 < v2;
    } else {
      return v1_score > v2_score;
    }
  } 
  
  /** How much to increase the score per bump */
  double d_variableScoreIncreasePerBump;

  /** The decay factor */
  double d_variableScoreDecayFactor;

  /** Max score before we scale everyone back */
  double d_maxScoreBeforeScaling;

public:

  /** Construct a variable queue for variables of given type */
  VariablePriorityQueue();

  /** Add new variable to track */
  void newVariable(Variable var) {
    newVariable(var, 0);
  }

  /** Add new variable to track with the given score */
  void newVariable(Variable var, double score);

  /** Get the top variable */
  Variable pop();

  /** Get a random variable off the queue */
  Variable getRandom() const;
  
  /** Is the queue empty */
  bool empty() const;

  /** Enqueues the variable for decision making */
  void enqueue(Variable var);

  /** Is the variable in queue */
  bool inQueue(Variable var) const;

  /** Bump the score of the variable */
  void bumpVariable(Variable var, unsigned amount = 1);

  /** Decay the scores of variables */
  void decayScores();

  /** Get the score of a variable */
  double getScore(Variable var) const;

  /** Relocates any the variable queue */
  void gcRelocate(const VariableGCInfo& vReloc);
};

}
}
}




