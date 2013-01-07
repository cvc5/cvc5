#include "mcsat/plugin/solver_plugin_registry.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::mcsat;

ISolverPluginConstructor* SolverPluginRegistry::getConstructor(string id) {
  SolverPluginRegistry* registry = getInstance();
  registry_type::const_iterator find = registry->d_solverConstructors.find(id);
  if (find == registry->d_solverConstructors.end()) {
    return NULL;
  } else {
    return find->second;
  }
}

SolverPluginRegistry* SolverPluginRegistry::getInstance() {
  static SolverPluginRegistry registry;
  return &registry;
}

SolverPluginRegistry::~SolverPluginRegistry() {
  registry_type::const_iterator it = d_solverConstructors.begin();
  registry_type::const_iterator it_end = d_solverConstructors.begin();
  for (; it != it_end; ++ it) {
    delete it->second;
  }
}

void SolverPluginRegistry::getAvailablePlugins(std::vector<std::string>& plugins) {
  SolverPluginRegistry* registry = getInstance();
  registry_type::const_iterator it = registry->d_solverConstructors.begin();
  registry_type::const_iterator it_end = registry->d_solverConstructors.end();
  for (; it != it_end; ++ it) {
    plugins.push_back(it->first);
  }
}
