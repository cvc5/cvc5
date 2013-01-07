#include "mcsat/solver.h"

using namespace CVC4;
using namespace CVC4::mcsat;

void SolverPluginRequest::backtrack(unsigned level, CRef cRef) {
  d_solver->requestBacktrack(level, cRef);
}

void SolverPluginRequest::restart() {
  d_solver->requestRestart();
}

void SolverPluginRequest::propagate() {
  d_solver->requestPropagate();
}

void SolverPluginRequest::gc() {
  d_solver->requestGC();
}

void SolverPluginRequest::bump(Variable var, unsigned amount) {
  d_solver->bump(var, amount);
}

bool SolverPluginRequest::pending() const {
  return d_solver->d_request;
}


