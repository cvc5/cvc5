#include "mcsat/util/var_priority_queue.h"
#include "mcsat/variable/variable_db.h"
#include "mcsat/options.h"

#include <limits>

using namespace CVC4;
using namespace mcsat;
using namespace util;

/*
  see http://en.wikipedia.org/wiki/Binary_heap\
*/
static unsigned leftChild(unsigned i)  { return 2*i+1; }
static unsigned rightChild(unsigned i) { return 2*i+2; }
static unsigned parent(unsigned i)     { Assert(i > 0); return (i-1)/2; }

VariablePriorityQueue::VariablePriorityQueue()
: d_variableScoresMax(1)
, d_variableScoreIncreasePerBump(1)
, d_variableScoreDecayFactor(0.95)
, d_maxScoreBeforeScaling(options::mcsat_var_max_score())
{}

void VariablePriorityQueue::decayScores() {
  d_variableScoreIncreasePerBump /= d_variableScoreDecayFactor;
}

void VariablePriorityQueue::newVariable(Variable var, double score) {

  // Make sure there is space for the type 
  size_t typeIndex = var.typeIndex();
  if (typeIndex >= d_variableScores.size()) {
    d_variableScores.resize(typeIndex + 1);
    d_variableIndices.resize(typeIndex + 1);
  }

  // Insert a new score
  if (var.index() >= d_variableScores[typeIndex].size()) {
    d_variableScores[typeIndex].resize(var.index() + 1, 0);
    d_variableIndices[typeIndex].resize(var.index() + 1, null_index);
  }

  // Set the data
  var_score(var) = score;
  var_index(var) = null_index;

  // See if it's the max score
  if (score > d_variableScoresMax) {
    d_variableScoresMax = score;
  }

  // Enqueue the variable
  enqueue(var);
}

bool VariablePriorityQueue::inQueue(Variable var) const {
  Assert(var.typeIndex() < d_variableScores.size());
  Assert(var.index() < d_variableScores[var.typeIndex()].size());
  return var_index(var) != null_index;
}

void VariablePriorityQueue::enqueue(Variable var) {
  Assert(var.typeIndex() < d_variableScores.size());
  Assert(var.index() < d_variableScores[var.typeIndex()].size());
  Assert(!inQueue(var));

  // Add to the queue
  unsigned index = d_heapElements.size();
  var_index(var) = index;
  d_heapElements.push_back(var);
  
  // Push the new variable up
  percolateUp(var);
}

void VariablePriorityQueue::percolateUp(Variable var) {
  
  // The variable we're moving
  unsigned i = var_index(var);
  
  // While we're bigger than the parent swap them
  do {
    // We're at the top
    if (i == 0) break;
    // The parent
    Variable parent_var = d_heapElements[parent(i)];
    // If we're bigger than the parent, swp
    if (cmp(var, parent_var)) {
      // parent -> current
      d_heapElements[i]	= parent_var;  
      var_index(parent_var) = i;
      // current -> parent
      i = parent(i);
    } else {
      // Done
      break;
    }
  } while (true);
        
  // Remember the variable and index
  d_heapElements[i] = var;
  var_index(var) = i;
}

void VariablePriorityQueue::bumpVariable(Variable var, unsigned amount) {
  Assert(var.typeIndex() < d_variableScores.size());
  Assert(var.index() < d_variableScores[var.typeIndex()].size());
  
  // New heuristic value
  double newValue = var_score(var) + d_variableScoreIncreasePerBump*amount;
  if (newValue > d_variableScoresMax) {
    d_variableScoresMax = newValue;
  }

  // Update the value
  var_score(var) = newValue;
  
  // If the variable is in queue, push it up
  if (inQueue(var)) {
    percolateUp(var);
  } 
  
  // If the new value is too big, update all the values
  if (newValue > d_maxScoreBeforeScaling) {
    // This should preserve the order, we're fine
    for (unsigned type = 0; type < d_variableScores.size(); ++ type) {
      for (unsigned i = 0; i < d_variableScores[type].size(); ++ i) {
        d_variableScores[type][i] /= d_maxScoreBeforeScaling;
      }
    }
    d_variableScoresMax /= d_maxScoreBeforeScaling;
    d_variableScoreIncreasePerBump /= d_maxScoreBeforeScaling;
  }
}

double VariablePriorityQueue::getScore(Variable var) const {
  Assert(var.typeIndex() < d_variableScores.size());
  Assert(var.index() < d_variableScores[var.typeIndex()].size());
  return var_score(var);
}

Variable VariablePriorityQueue::pop() {
  Assert(d_heapElements.size() > 0);
  
  // The element we're popping
  Variable var = d_heapElements[0];
  var_index(var) = null_index;
  
  // Put the last element in the first place
  if (d_heapElements.size() > 1) {
    Variable toMove = d_heapElements.back();
    d_heapElements[0] = toMove;
    var_index(toMove) = 0;
    d_heapElements.pop_back();
    percolateDown(toMove);
  } else {
    d_heapElements.pop_back();
  }
  
  return var;
}

void VariablePriorityQueue::percolateDown(Variable var) {
  
  // The variable we're moving
  unsigned i = var_index(var);
  
  // While we're smaller than one of the children push down
  do {
    // If no more children, we're done
    if (leftChild(i) >= d_heapElements.size()) break;
    
    // Get the larger child 
    unsigned largerChild = leftChild(i);
    Variable largerVar = d_heapElements[largerChild];    
    if (rightChild(i) < d_heapElements.size()) {
      Variable rightVar = d_heapElements[rightChild(i)];
      if (cmp(rightVar, largerVar)) {
	largerChild = rightChild(i);
	largerVar = rightVar;
      } 
    } 
    
    // If we're not smaller than the larger child, we're in the right spot
    if (!cmp(largerVar, var)) break;
    
    // Swap with the larger child
    d_heapElements[i] = largerVar;
    var_index(largerVar) = i;
    
    // Continue
    i = largerChild;
  } while (true);
        
  // Remember the variable and index
  d_heapElements[i] = var;
  var_index(var) = i;
}

Variable VariablePriorityQueue::getRandom() const {
  // Get a random variable from the queue
  unsigned i = (rand() % d_heapElements.size());
  return d_heapElements[i];
}

bool VariablePriorityQueue::empty() const {
  return d_heapElements.empty();
}

void VariablePriorityQueue::remove(Variable var) {
  
  Assert(inQueue(var));
  
  double maxScore = d_variableScoresMax;

  // Make the variable largest
  double oldScore = d_variableScores[var.typeIndex()][var.index()];
  var_score(var) = std::numeric_limits<double>::max();
  percolateUp(var);
  Variable largest = pop();
  Assert(largest == var);
  var_score(var) = oldScore;
  
  d_variableScoresMax = maxScore;
}

void VariablePriorityQueue::gcRelocate(const VariableGCInfo& vReloc) {
  std::vector<Variable> toDelete;
  // Get the variables to delete
  for (unsigned i = 0; i < d_heapElements.size(); ++ i) {
    Variable var = d_heapElements[i];
    if (vReloc.isCollected(var)) {
      toDelete.push_back(var);
    }    
  }
  // Remove the variables
  for (unsigned i = 0; i < toDelete.size(); ++ i) {
    remove(toDelete[i]);
  }
}
