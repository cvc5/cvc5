/*********************                                                        */
/*! \file record.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a record definition
 **
 ** A class representing a record definition.
 **/

#include "expr/record.h"

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "expr/expr.h"
#include "expr/type.h"


namespace CVC4 {

static Record::FieldVector::const_iterator find(
    const Record::FieldVector& fields, const std::string& name)
{
  for(Record::FieldVector::const_iterator i = fields.begin(), i_end = fields.end(); i != i_end; ++i){
    if((*i).first == name) {
      return i;
    }
  }
  return fields.end();
}

Record::Record(const FieldVector& fields)
    : d_fields(new FieldVector(fields))
{
  Debug("record") << "making " << this << " " << d_fields << std::endl;
}

Record::Record(const Record& other)
    : d_fields(new FieldVector(other.getFields()))
{
  Debug("record") << "copy constructor " << this << " " << d_fields << std::endl;
}

Record::~Record() {
  Debug("record") << "deleting " << this << " " << d_fields << std::endl;
  delete d_fields;
}

Record& Record::operator=(const Record& r) {
  Debug("record") << "setting " << this << " " << d_fields << std::endl;
  Record::FieldVector& local = *d_fields;
  local = r.getFields();
  return *this;
}

const Record::FieldVector& Record::getFields() const {
  return *d_fields;
}

bool Record::contains(const std::string& name) const {
  return find(*d_fields, name) != d_fields->end();
}


size_t Record::getIndex(std::string name) const {
  FieldVector::const_iterator i = find(*d_fields, name);
  PrettyCheckArgument(i != d_fields->end(), name,
                      "requested field `%s' does not exist in record",
                      name.c_str());
  return i - d_fields->begin();
}

size_t Record::getNumFields() const {
  return d_fields->size();
}


std::ostream& operator<<(std::ostream& os, const Record& r) {
  os << "[# ";
  bool first = true;
  const Record::FieldVector& fields = r.getFields();
  for(Record::FieldVector::const_iterator i = fields.begin(),
      i_end = fields.end(); i != i_end; ++i) {
    if(!first) {
      os << ", ";
    }
    os << (*i).first << ":" << (*i).second;
    first = false;
  }
  os << " #]";

  return os;
}

size_t RecordHashFunction::operator()(const Record& r) const {
  size_t n = 0;
  const Record::FieldVector& fields = r.getFields();
  for(Record::FieldVector::const_iterator i = fields.begin(),
      i_end = fields.end(); i != i_end; ++i) {
    n = (n << 3) ^ TypeHashFunction()((*i).second);
  }
  return n;
}

std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) {
  return out << "[" << t.getField() << "]";
}


const std::pair<std::string, Type>& Record::operator[](size_t index) const {
  PrettyCheckArgument(index < d_fields->size(), index,
                      "index out of bounds for record type");
  return (*d_fields)[index];
}

bool Record::operator==(const Record& r) const {
  return (*d_fields) == *(r.d_fields);
}

}/* CVC4 namespace */
