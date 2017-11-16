#include "mcsat/plugin/solver_plugin_factory.h"

// All plugins to ensure static linking
#include "mcsat/bcp/bcp_engine.h"
#include "mcsat/cnf/cnf_plugin.h"
#include "mcsat/fm/fm_plugin.h"
#include "mcsat/uf/uf_plugin.h"

#include <sstream>

using namespace CVC4;
using namespace CVC4::mcsat;

SolverPlugin* SolverPluginFactory::create(std::string name, ClauseDatabase& clauseDb, const SolverTrail& trail, SolverPluginRequest& request, StatisticsRegistry* registry)
  throw(SolverPluginFactoryException)
{
  ISolverPluginConstructor* constructor = SolverPluginRegistry::getConstructor(name);
  if (constructor) {
    return constructor->construct(clauseDb, trail, request, registry);
  } else {

    std::stringstream ss;
    ss << "Solver " << name << " not available. Available plugins are:";

    std::vector<std::string> plugins;
    SolverPluginRegistry::getAvailablePlugins(plugins);
    std::ostream_iterator<std::string> out_it (ss, ", ");
    std::copy(plugins.begin(), plugins.end(), out_it);

    throw SolverPluginFactoryException(ss.str());
  }
}

