/*********************                                                        */
/*! \file record.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A class representing a Record definition
 **
 ** A class representing a Record definition.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__RECORD_H
#define __CVC4__RECORD_H

#include <iostream>
#include <string>
#include <vector>
#include <utility>
#include "util/hash.h"

namespace CVC4 {

class CVC4_PUBLIC Record;

// operators for record select and update

class CVC4_PUBLIC RecordSelect {
  std::string d_field;
public:
  RecordSelect(const std::string& field) throw() : d_field(field) { }
  std::string getField() const throw() { return d_field; }
  bool operator==(const RecordSelect& t) const throw() { return d_field == t.d_field; }
  bool operator!=(const RecordSelect& t) const throw() { return d_field != t.d_field; }
};/* class RecordSelect */

class CVC4_PUBLIC RecordUpdate {
  std::string d_field;
public:
  RecordUpdate(const std::string& field) throw() : d_field(field) { }
  std::string getField() const throw() { return d_field; }
  bool operator==(const RecordUpdate& t) const throw() { return d_field == t.d_field; }
  bool operator!=(const RecordUpdate& t) const throw() { return d_field != t.d_field; }
};/* class RecordUpdate */

struct CVC4_PUBLIC RecordSelectHashFunction {
  inline size_t operator()(const RecordSelect& t) const {
    return StringHashFunction()(t.getField());
  }
};/* struct RecordSelectHashFunction */

struct CVC4_PUBLIC RecordUpdateHashFunction {
  inline size_t operator()(const RecordUpdate& t) const {
    return StringHashFunction()(t.getField());
  }
};/* struct RecordUpdateHashFunction */

std::ostream& operator<<(std::ostream& out, const RecordSelect& t) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) CVC4_PUBLIC;

inline std::ostream& operator<<(std::ostream& out, const RecordSelect& t) {
  return out << "[" << t.getField() << "]";
}

inline std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) {
  return out << "[" << t.getField() << "]";
}

}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

// now an actual record definition

class CVC4_PUBLIC Record {
  std::vector< std::pair<std::string, Type> > d_fields;

public:

  typedef std::vector< std::pair<std::string, Type> >::const_iterator const_iterator;
  typedef const_iterator iterator;

  Record(const std::vector< std::pair<std::string, Type> >& fields) :
    d_fields(fields) {
  }

  const_iterator find(std::string name) const {
    const_iterator i;
    for(i = begin(); i != end(); ++i) {
      if((*i).first == name) {
        break;
      }
    }
    return i;
  }

  size_t getIndex(std::string name) const {
    const_iterator i = find(name);
    CheckArgument(i != end(), name, "requested field `%s' does not exist in record", name.c_str());
    return i - begin();
  }

  size_t getNumFields() const {
    return d_fields.size();
  }

  const_iterator begin() const {
    return d_fields.begin();
  }

  const_iterator end() const {
    return d_fields.end();
  }

  std::pair<std::string, Type> operator[](size_t index) const {
    CheckArgument(index < d_fields.size(), index, "index out of bounds for record type");
    return d_fields[index];
  }

  bool operator==(const Record& r) const {
    return d_fields == r.d_fields;
  }

  bool operator!=(const Record& r) const {
    return !(*this == r);
  }

};/* class Record */

struct CVC4_PUBLIC RecordHashFunction {
  inline size_t operator()(const Record& r) const {
    size_t n = 0;
    for(Record::iterator i = r.begin(); i != r.end(); ++i) {
      n = (n << 3) ^ TypeHashFunction()((*i).second);
    }
    return n;
  }
};/* struct RecordHashFunction */

std::ostream& operator<<(std::ostream& os, const Record& r) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__RECORD_H */
