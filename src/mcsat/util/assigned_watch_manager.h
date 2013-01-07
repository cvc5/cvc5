#pragma once

#include "mcsat/variable/variable_db.h"
#include "mcsat/variable/variable_table.h"

#include <vector>
#include <ext/hash_map>
#include <boost/integer/integer_mask.hpp>

namespace CVC4 {
namespace mcsat {
namespace util {

/**
 * A reference to a list of variables. The reference is just an index into a
 * memory and the length of the list (> 0).
 */
class VariableListReference {

protected:

  /** Number of bits kept for the reference */
  static const size_t BITS_FOR_REFERENCE = 32;

  /** NUmber of bits kept for the size */
  static const size_t BITS_FOR_SIZE = 32;

  /** Index of the reference */
  size_t d_index : BITS_FOR_REFERENCE;

  /** Size of the list */
  size_t d_size  : BITS_FOR_SIZE;

  /** Null reference */
  static const size_t nullRef = boost::low_bits_mask_t<BITS_FOR_REFERENCE>::sig_bits;

  VariableListReference(size_t ref, size_t size)
  : d_index(ref)
  , d_size(size)
  {}

  friend class AssignedWatchManager;

public:

  /** Create a null list reference */
  VariableListReference()
  : d_index(nullRef)
  , d_size(0)
  {}

  /** Create a reference from antoher reference */
  VariableListReference(const VariableListReference& other)
  : d_index(other.d_index)
  , d_size(other.d_size)
  {}

  /** Assign this reference another reference */
  VariableListReference& operator = (const VariableListReference& other) {
    d_index = other.d_index;
    d_size = other.d_size;
    return *this;
  }

  /** What is the index of this list in the memory */
  size_t index() const {
    return d_index;
  }

  /** Is this a null reference */
  bool isNull() const {
    return d_index == +nullRef;
  }
  
  /** What is the size of this list (>0) */
  size_t size() const {
    return d_size;
  }

  /** Equality checking for two references */
  bool operator == (const VariableListReference& other) const {
    return d_index == other.d_index;
  }

};

/**
 * This hash function is only apropriate for lists coming from the same memory.
 */
class VariableListReferenceHashFunction {
public:
  size_t operator () (const VariableListReference& varList) const {
    return varList.index();
  }
};

/**
 * A variable list is a subsequence of a memory dedicated for lists of 
 * variables. It is obtained from the memory using the list reference.
 */
class VariableList : public VariableListReference {

  std::vector<Variable>& d_memory;

public:

  VariableList(std::vector<Variable>& memory, VariableListReference ref)
  : VariableListReference(ref)
  , d_memory(memory)
  {}

  VariableList(const VariableList& other)
  : VariableListReference(other)
  , d_memory(other.d_memory)
  {}

  /** Get the variable at the given index of the list */
  const Variable& operator [] (size_t i) const {
    Assert(i < size());
    return d_memory[d_index + i];
  }

  /** Swap two variables in this list */
  void swap(size_t i, size_t j) {
    Assert(i < size() && j < size());
    std::swap(d_memory[d_index + i], d_memory[d_index + j]);
  }

  /** Output the list */
  void toStream(std::ostream& out) const {
    out << "VariableList[";
    for (unsigned i = 0; i < d_size; ++ i) {
      if (i > 0) out << ",";
      out << d_memory[d_index + i];
    }
    out << "]";
  }

};

inline std::ostream& operator << (std::ostream& out, const VariableList& list) {
  list.toStream(out);
  return out;
}

/** 
 * A manager of the lists of constraint variables. It contains the memory into 
 * which the lists can index. Each list can be at attached to a variable.
 */
class AssignedWatchManager {

  typedef __gnu_cxx::hash_map<VariableListReference, Variable, VariableListReferenceHashFunction> varlist_to_var_map;

  /** The list memory */
  std::vector<Variable> d_memory;

  /** A list of references to variable lists */
  typedef std::vector<VariableListReference> watch_list;

  /** A table from variables to lists */
  typedef variable_table<watch_list> watch_lists;

  /** Watchlist indexed by variables */
  watch_lists d_watchLists;

  /** Map from lists to constraint variables */
  varlist_to_var_map d_varlistToConstraint;

  /** List of all lists in creation order */
  std::vector<VariableListReference> d_varlistList;

  /** Set of watched variables */
  std::set<Variable> d_watchedVariables;

public:

  /**
   * Adds a new list of variables to watch and associate it with a constraint.
   */
  VariableListReference newListToWatch(const std::vector<Variable>& vars, Variable constraint) {
    // Create the list
    VariableListReference ref(d_memory.size(), vars.size());
    for(unsigned i = 0; i < vars.size(); ++ i) {
      d_memory.push_back(vars[i]);
    }
    // Record
    d_varlistToConstraint[ref] = constraint;
    d_varlistList.push_back(ref);
    // The new list reference
    return ref;
  }

  /**
   * Get the constraint associated with the variable list.
   */
  Variable getConstraint(util::VariableListReference list) const {
    Assert(d_varlistToConstraint.find(list) != d_varlistToConstraint.end());
    return d_varlistToConstraint.find(list)->second;
  }


  /** Add list to the watchlist of var */
  void watch(Variable var, VariableListReference ref) {
    d_watchLists[var].push_back(ref);
    d_watchedVariables.insert(var);
  }

  /** Size of the watchlist */
  size_t size() const { return d_memory.size(); }
  
  /** An iterator that can remove as it traverses a watchlist */
  class remove_iterator {
    
    friend class AssignedWatchManager;
    
    /** The watch-lists from the manager */
    watch_lists& d_watchLists;     
    
    /** Index of the watch list */
    Variable d_variable;

    /** Element beyond the last to keep */
    size_t d_end_of_keep;
    /** Current element */
    size_t d_current;
 
    remove_iterator(watch_lists& lists, Variable var)
    : d_watchLists(lists)
    , d_variable(var)
    , d_end_of_keep(0)
    , d_current(0)
    {}

  public:
    
    /** Is there a next element */
    bool done() const {
      return d_current == d_watchLists[d_variable].size();
    }
    /** Continue to the next element and keep this one */
    void next_and_keep() {
      d_watchLists[d_variable][d_end_of_keep ++] = d_watchLists[d_variable][d_current ++];
    }
    /** Continue to the next element and remove this one */
    void next_and_remove() { 
      ++ d_current;
    }
    /** Get the current element */
    VariableListReference operator * () const {
      return d_watchLists[d_variable][d_current];
    }

    /** Removes removed elements from the list */
    ~remove_iterator() {
      while (!done()) {
	next_and_keep();
      }
      d_watchLists[d_variable].resize(d_end_of_keep);
    }
  };

  /** Returns the iterator that can remove elements */
  remove_iterator begin(Variable var) {
    return remove_iterator(d_watchLists, var);
  }

  /** Get the actual variable list */
  VariableList get(VariableListReference ref) {
    return VariableList(d_memory, ref);
  }

  /** Do garbage collection */
  void gcRelocate(const VariableGCInfo& vReloc);
};

}
}
}
