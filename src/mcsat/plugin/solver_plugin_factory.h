#pragma once

#include "cvc4_public.h"

#include <string>
#include <vector>

#include "context/context.h"
#include "base/exception.h"

#include "mcsat/plugin/solver_plugin.h"

namespace CVC4 {
namespace mcsat {

class SolverPluginFactoryException : public Exception {
public:
  SolverPluginFactoryException(std::string message)
  : Exception(message) {
  }
};

class SolverPluginFactory {
public:
  static SolverPlugin* create(std::string name, ClauseDatabase& clauseDb, const SolverTrail& d_trail, SolverPluginRequest& request, StatisticsRegistry* registry)
    throw(SolverPluginFactoryException);
};

}
}


