/*********************                                                        */
/*! \file attribute.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief AttributeManager implementation.
 **
 ** AttributeManager implementation.
 **/

#include "expr/attribute.h"
#include "expr/node_value.h"
#include "util/output.h"

#include <utility>

using namespace std;

namespace CVC4 {
namespace expr {
namespace attr {

void AttributeManager::deleteAllAttributes(NodeValue* nv) {
  d_bools.erase(nv);
  deleteFromTable(d_ints, nv);
  deleteFromTable(d_tnodes, nv);
  deleteFromTable(d_nodes, nv);
  deleteFromTable(d_types, nv);
  deleteFromTable(d_strings, nv);
  deleteFromTable(d_ptrs, nv);

  d_cdbools.erase(nv);
  deleteFromTable(d_cdints, nv);
  deleteFromTable(d_cdtnodes, nv);
  deleteFromTable(d_cdnodes, nv);
  deleteFromTable(d_cdstrings, nv);
  deleteFromTable(d_cdptrs, nv);
}

void AttributeManager::deleteAllAttributes() {
  d_bools.clear();
  deleteAllFromTable(d_ints);
  deleteAllFromTable(d_tnodes);
  deleteAllFromTable(d_nodes);
  deleteAllFromTable(d_types);
  deleteAllFromTable(d_strings);
  deleteAllFromTable(d_ptrs);

  d_cdbools.clear();
  d_cdints.clear();
  d_cdtnodes.clear();
  d_cdnodes.clear();
  d_cdstrings.clear();
  d_cdptrs.clear();
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
