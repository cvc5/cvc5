/*********************                                                        */
/*! \file attribute.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Dejan Jovanovic, Tim King
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

AttributeManager::AttributeManager(context::Context* ctxt) :
  d_cdbools(ctxt),
  d_cdints(ctxt),
  d_cdtnodes(ctxt),
  d_cdnodes(ctxt),
  d_cdstrings(ctxt),
  d_cdptrs(ctxt),
  d_inGarbageCollection(false)
{}

bool AttributeManager::inGarbageCollection() const {
  return d_inGarbageCollection;
}

void AttributeManager::debugHook(int debugFlag) {
  /* DO NOT CHECK IN ANY CODE INTO THE DEBUG HOOKS!
   * debugHook() is an empty function for the purpose of debugging
   * the AttributeManager without recompiling all of CVC4.
   * Formally this is a nop.
   */
}

void AttributeManager::deleteAllAttributes(NodeValue* nv) {
  Assert(!inGarbageCollection());
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

void AttributeManager::deleteAttributes(const AttrIdVec& atids){
  typedef std::map<uint64_t, std::vector< uint64_t> > AttrToVecMap;
  AttrToVecMap perTableIds;

  for(AttrIdVec::const_iterator it = atids.begin(), it_end = atids.end(); it != it_end; ++it){
    const AttributeUniqueId& pair = *(*it);
    std::vector< uint64_t>& inTable = perTableIds[pair.getTableId()];
    inTable.push_back(pair.getWithinTypeId());
  }
  AttrToVecMap::iterator it = perTableIds.begin(), it_end = perTableIds.end();
  for(; it != it_end; ++it){
    Assert(((*it).first) <= LastAttrTable);
    AttrTableId tableId = (AttrTableId) ((*it).first);
    std::vector< uint64_t>& ids = (*it).second;
    std::sort(ids.begin(), ids.end());

    switch(tableId){
    case AttrTableBool:
      Unimplemented("delete attributes is unimplemented for bools");
      break;
    case AttrTableUInt64:
      deleteAttributesFromTable(d_ints, ids);
      break;
    case AttrTableTNode:
      deleteAttributesFromTable(d_tnodes, ids);
      break;
    case AttrTableNode:
      deleteAttributesFromTable(d_nodes, ids);
      break;
    case AttrTableTypeNode:
      deleteAttributesFromTable(d_types, ids);
      break;
    case AttrTableString:
      deleteAttributesFromTable(d_strings, ids);
      break;
    case AttrTablePointer:
      deleteAttributesFromTable(d_ptrs, ids);
      break;

    case AttrTableCDBool:
    case AttrTableCDUInt64:
    case AttrTableCDTNode:
    case AttrTableCDNode:
    case AttrTableCDString:
    case AttrTableCDPointer:
      Unimplemented("CDAttributes cannot be deleted. Contact Tim/Morgan if this behavior is desired.");
      break;
    case LastAttrTable:
    default:
      Unreachable();
    }
  }
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
