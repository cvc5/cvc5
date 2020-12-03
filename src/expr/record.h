/*********************                                                        */
/*! \file record.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a Record definition
 **
 ** A class representing a Record definition.
 **/

#include "cvc4_public.h"

#ifndef CVC4__RECORD_H
#define CVC4__RECORD_H

#include <functional>
#include <iostream>
#include <string>
#include <vector>
#include <utility>

// Forward Declarations
namespace CVC4 {
// This forward delcartion is required to resolve a cicular dependency with
// Record which is a referenced in a Kind file.
class TypeNode;
} /* namespace CVC4 */

namespace CVC4 {

// operators for record update
class CVC4_PUBLIC RecordUpdate {
  std::string d_field;

 public:
  RecordUpdate(const std::string& field) : d_field(field) {}
  std::string getField() const { return d_field; }
  bool operator==(const RecordUpdate& t) const { return d_field == t.d_field; }
  bool operator!=(const RecordUpdate& t) const { return d_field != t.d_field; }
};/* class RecordUpdate */

struct CVC4_PUBLIC RecordUpdateHashFunction {
  inline size_t operator()(const RecordUpdate& t) const {
    return std::hash<std::string>()(t.getField());
  }
};/* struct RecordUpdateHashFunction */

std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) CVC4_PUBLIC;

using Record = std::vector<std::pair<std::string, TypeNode>>;

}/* CVC4 namespace */

#endif /* CVC4__RECORD_H */
