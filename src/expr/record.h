/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a Record definition.
 */

#include "cvc5_public.h"

#ifndef CVC5__RECORD_H
#define CVC5__RECORD_H

#include <iostream>
#include <string>
#include <vector>
#include <utility>

// Forward Declarations
namespace cvc5 {
// This forward delcartion is required to resolve a cicular dependency with
// Record which is a referenced in a Kind file.
class TypeNode;
}  // namespace cvc5

namespace cvc5 {

// operators for record update
class RecordUpdate
{
  std::string d_field;

 public:
  RecordUpdate(const std::string& field) : d_field(field) {}
  std::string getField() const { return d_field; }
  bool operator==(const RecordUpdate& t) const { return d_field == t.d_field; }
  bool operator!=(const RecordUpdate& t) const { return d_field != t.d_field; }
}; /* class RecordUpdate */

struct RecordUpdateHashFunction
{
  inline size_t operator()(const RecordUpdate& t) const {
    return std::hash<std::string>()(t.getField());
  }
}; /* struct RecordUpdateHashFunction */

std::ostream& operator<<(std::ostream& out, const RecordUpdate& t);

using Record = std::vector<std::pair<std::string, TypeNode>>;

}  // namespace cvc5

#endif /* CVC5__RECORD_H */
