#pragma once

#include <set>
#include <vector>
#include <iostream>

#include "mcsat/variable/variable.h"
#include "mcsat/clause/clause_ref.h"
#include "mcsat/solver_trail.h"

namespace CVC4 {
namespace mcsat {

class SolverPlugin;

/**
 * The features that this plugin provides.
 */
enum PluginFeature {
  // The plugin does propagation
  CAN_PROPAGATE,
  // The plugin does decisions
  CAN_DECIDE_VALUES,
};

inline std::ostream& operator << (std::ostream& out, PluginFeature feature) {
  switch (feature) {
    case CAN_PROPAGATE:
      out << "CAN_PROPAGATE"; break;
    case CAN_DECIDE_VALUES:
      out << "CAN_DECIDE"; break;    
  }
  return out;
}

/** Interface for plugin notificaiton */
class SolverPluginFeatures {

public:

  typedef std::set<PluginFeature> features_set;

private:

  /** Which notifications the plugin asks for */
  features_set d_features;

protected:

  /** To be called by plugins to announce features */
  void addFeature(PluginFeature type) {
    d_features.insert(type);
  }

public:

  virtual ~SolverPluginFeatures() {}

  /** Get all notification types */
  const features_set& getFeaturesSet() {
    return d_features;
  }

  /** Perform propagation */
  virtual void propagate(SolverTrail::PropagationToken& out) {
    Unreachable("If you claim to implement, then reimplement");
  }

  /** Perform a decision */
  virtual void decide(SolverTrail::DecisionToken& out, Variable var) {
    Unreachable("If you claim to implement, then reimplement");
  }

  /** Perform a decision from given decision options */
  virtual void decide(SolverTrail::DecisionToken& out, const LiteralVector& options) {
    Unreachable("If you claim to implement, then reimplement");
  }

  virtual void outputStatusHeader(std::ostream& out) const {}
  virtual void outputStatusLine(std::ostream& out) const {}
};


/**
 * Class to collect plugins and dispatch actions.
 */
class FeatureDispatch : public SolverPluginFeatures  {

  /** All plugins arranged by features */
  std::vector< std::vector<SolverPlugin*> > d_plugins;

  /** The solver trail */
  const SolverTrail& d_trail;

  /** True if interrupted */
  bool d_interrupt;

public:

  FeatureDispatch(const SolverTrail& trail)
  : d_trail(trail), d_interrupt(false)
  {}

  /** Add a plugin to notify */
  void addPlugin(SolverPlugin* plugin);

  /** Perform propagation */
  void propagate(SolverTrail::PropagationToken& out);

  /** Perform a decision */
  void decide(SolverTrail::DecisionToken& out, Variable var);

  /** Interrupt it. No-op if nothing running, and as soon as any the method is done, interrupt is off */
  void interrupt();

  void outputStatusHeader(std::ostream& out) const;
  void outputStatusLine(std::ostream& out) const;
};

}
}
