#pragma once

#include "cvc4_private.h"

#include "util/tls.h"
#include "context/context.h"
#include "context/cdo.h"

#include "variable.h"

namespace CVC4 {
namespace mcsat {

/** Class containing all the information needed to relocate the variables. */
class VariableGCInfo {

private:

  /** Removed variables */
  VariableHashSet d_removedVariables;

  friend class VariableDatabase;

  /** Mark the variable as collected */
  void add(Variable var);

  /** Old variables per type */
  std::vector< std::vector<Variable> > d_removedByType;
  
public:

  /** Clear any information. */
  void clear() {
    d_removedVariables.clear();
    d_removedByType.clear();
  }

  /** Returns true if the variable was collected */
  bool isCollected(Variable var) const {
    return d_removedVariables.find(var) != d_removedVariables.end();
  }

  /** Remove collected variables from the vector */
  void collect(std::vector<Variable>& vars) const;

  /** Iterator through the removed variables of some types */
  typedef std::vector<Variable>::const_iterator const_iterator;

  /** Iterator begin */
  const_iterator begin(size_t typeIndex) const;

  /** Iterator end */
  const_iterator end(size_t typeIndex) const;

  /** Size */
  size_t size(size_t typeIndex) const;
};


/**
 * Database of variables, both Boolean and non-Boolean. The variables are preferred
 * to nodes as they provide contiguous ids for important nodes (variables and 
 * shared terms).
 */
class VariableDatabase {

public:

  /** Interface for notification of new variables */
  class INewVariableNotify {
    /** Is this listener context dependent */
    bool d_isContextDependent;

  public:

    INewVariableNotify(bool cd)
    : d_isContextDependent(cd) {}
    virtual ~INewVariableNotify() {}

    /** Is this listener context dependent */
    bool isContextDependent() const {
      return d_isContextDependent;
    }

    virtual void newVariable(Variable var) = 0;
  };

private:

  /** Vector of types */
  std::vector<TypeNode> d_variableTypes;

  /** Map from Types to type-id */
  typedef std::hash_map<TypeNode, size_t, TypeNodeHashFunction> typenode_to_id_map;
  typenode_to_id_map d_typenodeToIdMap;

  /** Nodes of the variables */
  std::vector< std::vector<Node> > d_variableNodes;

  /** Recylcling of variables */
  std::vector< std::vector<Variable> > d_variablesToRecycle;

  typedef std::hash_map<TNode, Variable, TNodeHashFunction> node_to_variable_map;

  /** Map from nodes to variable id's */
  node_to_variable_map d_nodeToVariableMap;

  /** The context we're using */
  context::Context* d_context;

  /** Context dependent number of variables */
  context::CDO<size_t> d_variablesCountAtCurrentLevel;

  /** All variables in the database */
  std::vector<Variable> d_variables;

  /** Non-context-dependent notify subscribers */
  std::vector<INewVariableNotify*> d_notifySubscribers;

  /** Context dependent notify subscribers */
  std::vector<INewVariableNotify*> d_cd_notifySubscribers;

  /** Clause database we're using */
  static CVC4_THREADLOCAL(VariableDatabase*) s_current;
  
  /** Pop notifications go through this class */
  class Backtracker : public context::ContextNotifyObj {
    VariableDatabase& d_db;
  public:
    Backtracker(context::Context* context, VariableDatabase& db);
    void contextNotifyPop();
  };

  /** Backtracker for notifications context pops */
  Backtracker d_backtracker;

  /** Backtracker is a friend in order to notify listeners on backtrack */
  friend class Backtracker;

public:

  /** Constructor with the context to obey */
  VariableDatabase(context::Context* context);

  /** Check if the node has a variable */
  bool hasVariable(TNode node) const;

  /** Create a new variable or reuse an existing one */
  Variable getVariable(TNode node);

  /**
   * Add a listener for the creation of new variables. A context independent listener will only be notified
   * once when the variable is created. If the listener is context dependent, it will be notified when the
   * variable created, but it will be re-notified on every pop so that it can update it's internal state.
   *
   * @param listener the listener
   */
  void addNewVariableListener(INewVariableNotify* listener);

  /** Return the node associated with the variable */
  TNode getNode(Variable var) const {
    if (var.isNull()) return TNode::null();
    Assert(var.typeIndex() < d_variableNodes.size());
    return d_variableNodes[var.typeIndex()][var.index()];
  }

  /** Get the type of the variable */
  TypeNode getTypeNode(Variable var) const {
    if (var.isNull()) return TypeNode::null();
    return d_variableTypes[var.typeIndex()];
  }

  /** Get the index of the given type */
  size_t getTypeIndex(TypeNode type);

  /** Returns the number of variables of a given type */
  size_t size(size_t typeIndex) const;

  /** Returns the total number of variables */
  size_t size() const { return d_variables.size(); }

  /**
   * Get the current clause database
   */
  static VariableDatabase* getCurrentDB() {
    return s_current;
  }

  /**
   * Set the current database.
   */
  static void setCurrentDB(VariableDatabase* current) {
    s_current = current;
  }

  /**
   * Helper class to ensure scoped variable database.
   */
  class SetCurrent {
    VariableDatabase* old;
  public:
    /** Set the given DB in the current scope. */
    SetCurrent(VariableDatabase* db) {
      old = getCurrentDB();
      setCurrentDB(db);
    }
    ~SetCurrent() {
      setCurrentDB(old);
    }
  };

  /**
   * Performs GC keeping the varsToKeep variables and filling in the relocationInfo for the user.
   */
  void performGC(const std::set<Variable>& varsToKeep, VariableGCInfo& relocationInfo);

  /** Debug info to stream */
  void toStream(std::ostream& out) const;
  
};

inline std::ostream& operator << (std::ostream& out, const VariableDatabase& db) {
  db.toStream(out);
  return out;
}

}
}
