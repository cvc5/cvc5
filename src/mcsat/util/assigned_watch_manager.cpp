#include "mcsat/util/assigned_watch_manager.h"

using namespace CVC4;
using namespace mcsat;
using namespace util;

void AssignedWatchManager::gcRelocate(const VariableGCInfo& vReloc) {

  // Map from lists to lists
  typedef __gnu_cxx::hash_map<VariableListReference, VariableListReference, VariableListReferenceHashFunction> list_to_list_map;

  // Map of relocation for variable lists
  list_to_list_map relocation_map;

  // Relocate the lists
  unsigned oldSize = d_memory.size();
  unsigned memIndex = 0;
  unsigned list_to_keep = 0;
  for (unsigned list_i = 0; list_i < d_varlistList.size(); ++ list_i) {
    VariableListReference list = d_varlistList[list_i];
    // Do we keep this list
    if (vReloc.isCollected(getConstraint(list))) {
      // If collected, we just go on
    } else {
      // If we need to move, move the list
      if (list.index() != memIndex) {
        for (unsigned i = 0; i < list.size(); ++ i) {
          d_memory[memIndex + i] = d_memory[list.index() + i];
        }
      }
      VariableListReference newList(memIndex, list.size());
      relocation_map[list] = newList;
      memIndex += list.size();

      // Keep the list
      d_varlistList[list_to_keep ++] = newList;
    }
  }
  Assert(d_memory.size() >= memIndex);
  d_memory.resize(memIndex);
  Assert(d_varlistList.size() >= list_to_keep);
  d_varlistList.resize(list_to_keep);

  // If no lists were relocated, we need not do anything
  if (oldSize == d_memory.size()) {
    return;
  }

  // Relocate the list to constraint map
  varlist_to_var_map varlistToConstraintNew;
  varlist_to_var_map::const_iterator l_it = d_varlistToConstraint.begin();
  varlist_to_var_map::const_iterator l_it_end = d_varlistToConstraint.end();
  for (; l_it != l_it_end; ++ l_it) {
    list_to_list_map::const_iterator find = relocation_map.find(l_it->first);
    if (find != relocation_map.end()) {
      varlistToConstraintNew[find->second] = l_it->second;
    }
  }
  Assert(d_varlistToConstraint.size() >= varlistToConstraintNew.size());
  d_varlistToConstraint.swap(varlistToConstraintNew);

  // Watchlists
  std::set<Variable>::const_iterator v_it = d_watchedVariables.begin();
  std::set<Variable>::const_iterator v_it_end = d_watchedVariables.end();
  std::vector<Variable> unwatchedVariables;
  for (; v_it != v_it_end; ++ v_it) {
    watch_list& list = d_watchLists[*v_it];
    unsigned i = 0;
    unsigned keep = 0;
    for (; i < list.size(); ++ i) {
      VariableListReference current = list[i];
      list_to_list_map::const_iterator find = relocation_map.find(current);
      if (find != relocation_map.end()) {
        list[keep ++] = find->second;
      }
    }
    Assert(list.size() >= keep);
    list.resize(keep);
    if (keep == 0) {
      unwatchedVariables.push_back(*v_it);
    }
  }
  for (unsigned i = 0; i < unwatchedVariables.size(); ++ i) {
    d_watchedVariables.erase(unwatchedVariables[i]);
  }

}
