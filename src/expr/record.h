/*********************                                                        */
/*! \file record.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

// Forward Declarations
namespace CVC4 {
// This forward delcartion is required to resolve a cicular dependency with
// Record which is a referenced in a Kind file.
class Type;
} /* namespace CVC4 */

namespace CVC4 {

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

// now an actual record definition
class CVC4_PUBLIC Record {
public:
  // Type must stay as incomplete types throughout this header!
  // Everything containing a Type must be a pointer or a reference.
  typedef std::vector< std::pair<std::string, Type> > FieldVector;

  Record(const FieldVector& fields);
  Record(const Record& other);
  ~Record();
  Record& operator=(const Record& r);

  bool contains(const std::string &name) const;

  size_t getIndex(std::string name) const;
  size_t getNumFields() const;

  const FieldVector& getFields() const;
  const std::pair<std::string, Type>& operator[](size_t index) const;

  bool operator==(const Record& r) const;
  bool operator!=(const Record& r) const {
    return !(*this == r);
  }

private:
  FieldVector* d_fields;
};/* class Record */

struct CVC4_PUBLIC RecordHashFunction {
  size_t operator()(const Record& r) const;
};/* struct RecordHashFunction */

std::ostream& operator<<(std::ostream& os, const Record& r) CVC4_PUBLIC;

}/* CVC4 namespace */

#endif /* __CVC4__RECORD_H */
