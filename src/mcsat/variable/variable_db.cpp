#include "variable_db.h"

using namespace CVC4;
using namespace mcsat;

CVC4_THREADLOCAL(VariableDatabase*) VariableDatabase::s_current = 0;

VariableDatabase::Backtracker::Backtracker(context::Context* context, VariableDatabase& db)
: ContextNotifyObj(context)
, d_db(db)
{}

void VariableDatabase::Backtracker::contextNotifyPop() {
  for (unsigned toNotify = 0; toNotify < d_db.d_cd_notifySubscribers.size(); ++ toNotify) {
    INewVariableNotify* notify = d_db.d_cd_notifySubscribers[toNotify];
    for (unsigned i = d_db.d_variablesCountAtCurrentLevel; i < d_db.d_variableNodes.size(); ++ i) {
      notify->newVariable(d_db.d_variables[i]);
    }
  }
  d_db.d_variablesCountAtCurrentLevel = d_db.d_variables.size();
}

VariableDatabase::VariableDatabase(context::Context* context)
: d_context(context)
, d_variablesCountAtCurrentLevel(context, 0)
, d_backtracker(context, *this)
{
  Assert(s_current == 0, "Make sure active DB is 0 before creating a new VariableDatabase");
  s_current = this;
  Debug("mcsat::var_db") << "VariableDatabase(): var_null = " << +Variable::s_null_varId << std::endl;
}

size_t VariableDatabase::getTypeIndex(TypeNode type) {
  typenode_to_id_map::const_iterator find_type = d_typenodeToIdMap.find(type);
  size_t typeIndex;
  if (find_type == d_typenodeToIdMap.end()) {
    typeIndex = d_variableTypes.size();
    d_typenodeToIdMap[type] = typeIndex;
    d_variableTypes.push_back(type);
    d_variableNodes.resize(typeIndex + 1);
    d_variablesToRecycle.resize(typeIndex + 1);
  } else {
    typeIndex = find_type->second;
  }
  Debug("mcsat::var_db") << "VariableDatabase::getTypeIndex(" << type << ") => " << typeIndex << std::endl;
  return typeIndex;
}

size_t VariableDatabase::size(size_t typeIndex) const {
  return d_variableNodes[typeIndex].size();
}

bool VariableDatabase::hasVariable(TNode node) const {
  return d_nodeToVariableMap.find(node) != d_nodeToVariableMap.end();
}

Variable VariableDatabase::getVariable(TNode node) {

  // Find the variable (it might exist already)
  node_to_variable_map::const_iterator find = d_nodeToVariableMap.find(node);

  // If the variable is there, we just return it
  if (find != d_nodeToVariableMap.end()) {
    // No need to notify, people were notified already
    return find->second;
  }

  // The type of the variable
  TypeNode type = node.getType();
  size_t typeIndex = getTypeIndex(type);

  // The id of the new variable
  size_t newVarId;
  if (d_variablesToRecycle[typeIndex].size() > 0) {
    // Recycle the variable
    newVarId = d_variablesToRecycle[typeIndex].back().index();
    d_variablesToRecycle[typeIndex].pop_back();
    d_variableNodes[typeIndex][newVarId] = node;
  } else {
    // Completely new variable
    newVarId = d_variableNodes[typeIndex].size();
    // Add the information
    d_variableNodes[typeIndex].push_back(node);
  }

  Variable var(newVarId, typeIndex);

  // Add to the node map
  d_nodeToVariableMap[node] = var;
  d_variables.push_back(var);

  Debug("mcsat::var_db") << "VariableDatabase::newVariable(" << node << ") => " << var.index() << std::endl;

  for (unsigned toNotify = 0; toNotify < d_notifySubscribers.size(); ++ toNotify) {
    d_notifySubscribers[toNotify]->newVariable(var);
  }
  d_variablesCountAtCurrentLevel = d_variables.size();

  return var;
}

void VariableDatabase::addNewVariableListener(INewVariableNotify* listener) {

  for (unsigned typeIndex = 0; typeIndex < d_variableTypes.size(); ++ typeIndex) {
    for (unsigned variableIndex = 0; variableIndex < d_variableNodes[typeIndex].size(); ++ variableIndex) {
      listener->newVariable(Variable(variableIndex, typeIndex));
    }
  }
  
  if (listener->isContextDependent()) {
    d_cd_notifySubscribers.push_back(listener);
  }
  d_notifySubscribers.push_back(listener);
}

void VariableDatabase::performGC(const std::set<Variable>& varsToKeep, VariableGCInfo& relocationInfo) {

  // Clear any relocation info
  relocationInfo.clear();

  unsigned current = 0;
  unsigned lastToKeep = 0;
  for (; current < d_variables.size(); ++ current) {
    Variable var = d_variables[current];
    if (varsToKeep.count(var) > 0) {
      // We're keeping this one
      d_variables[lastToKeep ++] = var;
    } else {
      Debug("mcsat::gc") << "GC: collecting " << var << std::endl;
      // Erase the node information
      d_nodeToVariableMap.erase(var.getNode());
      d_variableNodes[var.typeIndex()][var.index()] = Node::null();
      // Add to rectycle list
      d_variablesToRecycle[var.typeIndex()].push_back(var);
      // Add to relocation info
      relocationInfo.add(var);
    }
  }
  Assert(d_variables.size() >= lastToKeep);
  d_variables.resize(lastToKeep);

  d_variablesCountAtCurrentLevel = d_variables.size();

}

/** Iterator to */
VariableGCInfo::const_iterator VariableGCInfo::begin(size_t typeIndex) const {
  return d_removedByType[typeIndex].begin();
}

/** Iterator to */
VariableGCInfo::const_iterator VariableGCInfo::end(size_t typeIndex) const {
  return d_removedByType[typeIndex].end();
}

void VariableGCInfo::add(Variable var) {
  Assert(d_removedVariables.find(var) == d_removedVariables.end());
  d_removedVariables.insert(var);
  size_t typeIndex = var.typeIndex();
  if (typeIndex >= d_removedByType.size()) {
    d_removedByType.resize(typeIndex + 1);
  }
  d_removedByType[typeIndex].push_back(var);
}

size_t VariableGCInfo::size(size_t typeIndex) const {
  if (typeIndex >= d_removedByType.size()) {
    return 0;
  } else {
    return d_removedByType[typeIndex].size();
  }
}

void VariableGCInfo::collect(std::vector<Variable>& vars) const {
  unsigned current = 0;
  unsigned lastToKeep = 0;
  for (; current < vars.size(); ++ current) {
    Variable var = vars[current];
    if (!isCollected(var)) {
      vars[lastToKeep++] = var;
    }
  }
  Assert(vars.size() >= lastToKeep);
  vars.resize(lastToKeep);
}

void VariableDatabase::toStream(std::ostream& out) const {
  out << "vars = " << d_variables.size();
}
