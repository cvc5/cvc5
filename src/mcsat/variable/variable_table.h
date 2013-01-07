#pragma once

#include "mcsat/variable/variable.h"
#include "mcsat/variable/variable_db.h"

#include <vector>

namespace CVC4 {
namespace mcsat {

/** Filters all variables */
struct variable_filter_none {
  bool operator () (const Variable& var) const { return true; }
};

/** Filters variables by given type */
class variable_filter_by_type {
  size_t d_type_index;
public:
  variable_filter_by_type(TypeNode type)
  : d_type_index(VariableDatabase::getCurrentDB()->getTypeIndex(type)) {
  }
  bool operator () (const Variable& var) const {
    return d_type_index == var.typeIndex();
  }
};

template <typename T, typename variable_filter = variable_filter_none>
class variable_table {

  typedef std::vector<T> per_type_table;

  typedef typename std::vector<T>::reference element_ref;
  typedef typename std::vector<T>::const_reference element_const_ref;

  /** The table per type */
  std::vector<per_type_table> d_table;

  /** Default value for the vectors */
  T d_defaultValue;

  /** On every new variable the table is resized */
  class new_variable_listener : public VariableDatabase::INewVariableNotify {
    variable_table& d_table;
    variable_filter d_filter;
  public:
    new_variable_listener(variable_table& table)
    : INewVariableNotify(false)
    , d_table(table)
    {}
    void newVariable(Variable var);
  } d_new_literal_listener;

public:

  /** Construct the table. Attaches to the current variable database */
  variable_table(const T& defaultValue = T());

  /** Dereference */
  element_const_ref operator [] (Variable var) const {
    return d_table[var.typeIndex()][var.index()];
  }

  /** Dereference */
  element_ref operator [] (Variable var) {
    return d_table[var.typeIndex()][var.index()];
  }

  /** Size of the table for a particular type */
  size_t size(size_t typeId) const {
    return d_table[typeId].size();
  }

  /** Output to stream */
  void toStream(std::ostream& out) const {
    for (unsigned i = 0; i < d_table.size(); ++ i) {
      for (unsigned j = 0; j < d_table[i].size(); ++ j) {
        if (j > 0) { out << ", "; }
        out << d_table[i][j];
      }
      out << std::endl;
    }
  }

};

template<typename T, typename variable_filter>
void variable_table<T, variable_filter>::new_variable_listener::newVariable(Variable var) {
  if (d_filter(var)) {
    size_t typeIndex = var.typeIndex();
    if (d_table.d_table.size() <= typeIndex) {
      d_table.d_table.resize(typeIndex + 1);
    }
    size_t index = var.index();
    if (d_table.d_table[typeIndex].size() <= index) {
      d_table.d_table[typeIndex].resize(index + 1, d_table.d_defaultValue);
    }
  }
}

template<typename T, typename variable_filter>
variable_table<T, variable_filter>::variable_table(const T& defaultValue)
: d_defaultValue(defaultValue)
, d_new_literal_listener(*this)
{
  VariableDatabase* db = VariableDatabase::getCurrentDB();
  db->addNewVariableListener(&d_new_literal_listener);
}

template<typename T, typename variable_filter>
std::ostream& operator << (std::ostream& out, const variable_table<T, variable_filter>& table) {
  table.toStream(out);
  return out;
}

class variable_set : protected variable_table<bool> {

  /** Inserted ones */
  std::vector<Variable> d_inserted;

  /** Size of the set */
  size_t d_size;

public:

  variable_set()
  : d_size(0)
  {}

  size_t size() const {
    return d_size;
  }

  bool contains(Variable v) const {
    return operator [] (v);
  }

  void insert(Variable v) {
    if (!contains(v)) {
      operator [] (v) = true;
      d_inserted.push_back(v);
      d_size ++;
    }
  }

  void remove(Variable v) {
    Assert(contains(v));
    operator [] (v) = false;
    d_size --;
  }

  void clear() {
    for (unsigned i = 0; i < d_inserted.size(); ++ i) {
      if (contains(d_inserted[i])) {
        remove(d_inserted[i]);
      }
    }
    d_inserted.clear();
    d_size = 0;
  }

  void get(std::vector<Variable>& out) const {
    for (unsigned i = 0; i < d_inserted.size(); ++ i) {
      if (contains(d_inserted[i])) {
        out.push_back(d_inserted[i]);
      }
    }
  }

  void toStream(std::ostream& out) const {
    std::vector<Variable> vars;
    get(vars);
    out << vars;
  }
};

inline std::ostream& operator << (std::ostream& out, const variable_set& set) {
  set.toStream(out);
  return out;
}


}
}




