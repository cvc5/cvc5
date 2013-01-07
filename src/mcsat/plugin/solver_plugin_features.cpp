#include "mcsat/plugin/solver_plugin_features.h"
#include "mcsat/plugin/solver_plugin.h"

using namespace CVC4;
using namespace mcsat;

template<typename T>
class ScopedReset {

  T& d_toReset;
  T d_resetValue;

public:

  ScopedReset(T& toWatch, T resetValue)
  : d_toReset(toWatch)
  , d_resetValue(resetValue)
  {
    d_toReset = d_resetValue;
  }

  ~ScopedReset() {
    d_toReset = d_resetValue;
  }
};

void FeatureDispatch::addPlugin(SolverPlugin* plugin) {
  Debug("mcsat::plugin") << "FeatureDispatch::addPlugin(): " << *plugin << std::endl;
  const features_set& s = plugin->getFeaturesSet();
  features_set::const_iterator it = s.begin();
  for(; it != s.end(); ++ it) {
    PluginFeature type = *it;
    Debug("mcsat::plugin") << "FeatureDispatch::addPlugin(): " << type << std::endl;
    if (type >= d_plugins.size()) {
      d_plugins.resize(type + 1);
    }
    d_plugins[type].push_back(plugin);
  }
}

void FeatureDispatch::propagate(SolverTrail::PropagationToken& out) {
  ScopedReset<bool> interrupt(d_interrupt, false);
  for(unsigned i = 0; d_trail.consistent() && !d_interrupt && i < d_plugins[CAN_PROPAGATE].size(); ++ i) {
    SolverPlugin* plugin = d_plugins[CAN_PROPAGATE][i];
    Debug("mcsat::plugin") << "FeatureDispatch::propagate(): " << *plugin << std::endl;
    plugin->propagate(out);
  }
}

void FeatureDispatch::decide(SolverTrail::DecisionToken& out, Variable var) {
  ScopedReset<bool> interrupt(d_interrupt, false);
  for(unsigned i = 0; !out.used() && !d_interrupt && i < d_plugins[CAN_DECIDE_VALUES].size(); ++ i) {
    SolverPlugin* plugin = d_plugins[CAN_DECIDE_VALUES][i];
    Debug("mcsat::plugin") << "FeatureDispatch::decide(): " << *plugin << std::endl;
    plugin->decide(out, var);
  }
}

void FeatureDispatch::interrupt() {
  d_interrupt = true;
}

void FeatureDispatch::outputStatusHeader(std::ostream& out) const {
  for(unsigned i = 0; i < d_plugins[CAN_PROPAGATE].size(); ++ i) {
    SolverPlugin* plugin = d_plugins[CAN_PROPAGATE][i];
    plugin->outputStatusHeader(out);
  }
}

void FeatureDispatch::outputStatusLine(std::ostream& out) const {
  for(unsigned i = 0; i < d_plugins[CAN_PROPAGATE].size(); ++ i) {
    SolverPlugin* plugin = d_plugins[CAN_PROPAGATE][i];
    plugin->outputStatusLine(out);
  }
}
