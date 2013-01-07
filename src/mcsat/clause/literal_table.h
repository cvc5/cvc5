#pragma once

#include "mcsat/clause/literal.h"
#include "mcsat/variable/variable_db.h"

#include <vector>

namespace CVC4 {
namespace mcsat {

template <typename T>
class literal_table {

  std::vector<T> d_table;

  typedef typename std::vector<T>::reference element_ref;
  typedef typename std::vector<T>::const_reference element_const_ref;

  /** Default value for the vectors */
  T d_defaultValue;

  /** On every new variable the table is resized */
  class new_literal_listener : public VariableDatabase::INewVariableNotify {
    literal_table& d_table;
    size_t d_bool_type_index;
  public:
    new_literal_listener(literal_table& table)
    : INewVariableNotify(false)
    , d_table(table)
    , d_bool_type_index(VariableDatabase::getCurrentDB()->getTypeIndex(NodeManager::currentNM()->booleanType()))
    {}
    void newVariable(Variable var);
  } d_new_literal_listener;

public:

  /** Construct the table. Attaches to the current variable database */
  literal_table(const T& defaultValue = T());

  /** Dereference */
  element_const_ref operator [] (Literal l) const {
    return d_table[l.index()];
  }

  /** Dereference */
  element_ref operator [] (Literal l) {
    return d_table[l.index()];
  }

  /** Size of the table */
  size_t size() const {
    return d_table.size();
  }

  /** Element by index */
  element_ref operator [] (size_t index) {
    return d_table[index];
  }

  /** Element by index */
  element_const_ref operator [] (size_t index) const {
    return d_table[index];
  }

};

template<typename T>
void literal_table<T>::new_literal_listener::newVariable(Variable var) {
  if (var.typeIndex() == d_bool_type_index) {
    Literal l1(var, true);
    Literal l2(var, false);

    size_t index = std::max(l1.index(), l2.index());
    if (d_table.d_table.size() <= index) {
      d_table.d_table.resize(index + 1, d_table.d_defaultValue);
    }
  }
}

template<typename T>
literal_table<T>::literal_table(const T& defaultValue)
: d_defaultValue(defaultValue)
, d_new_literal_listener(*this)
{
  VariableDatabase* db = VariableDatabase::getCurrentDB();
  db->addNewVariableListener(&d_new_literal_listener);
}

class literal_set : protected literal_table<bool> {

  /** Inserted ones */
  std::vector<Literal> d_inserted;

  /** Size of the set */
  size_t d_size;

public:

  literal_set()
  : d_size(0)
  {}

  size_t size() const {
    return d_size;
  }

  bool contains(Literal l) const {
    return operator [] (l);
  }

  void insert(Literal l) {
    if (!contains(l)) {
      operator [] (l) = true;
      d_inserted.push_back(l);
      d_size ++;
    }
  }

  void remove(Literal l) {
    Assert(contains(l));
    operator [] (l) = false;
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

  void get(std::vector<Literal>& out) const {
    for (unsigned i = 0; i < d_inserted.size(); ++ i) {
      if (contains(d_inserted[i])) {
        out.push_back(d_inserted[i]);
      }
    }
  }

  void toStream(std::ostream& out) const {
    std::vector<Literal> lits;
    get(lits);
    out << lits;
  }
};

inline std::ostream& operator << (std::ostream& out, const literal_set& set) {
  set.toStream(out);
  return out;
}

}
}




