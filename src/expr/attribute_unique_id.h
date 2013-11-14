
#pragma once

#include "cvc4_private.h"
#include <stdint.h>

// ATTRIBUTE IDs ============================================================

namespace CVC4 {
namespace expr {
namespace attr {

/** A unique id for each attribute table. */
enum AttrTableId {
  AttrTableBool,
  AttrTableUInt64,
  AttrTableTNode,
  AttrTableNode,
  AttrTableTypeNode,
  AttrTableString,
  AttrTablePointer,
  AttrTableCDBool,
  AttrTableCDUInt64,
  AttrTableCDTNode,
  AttrTableCDNode,
  AttrTableCDString,
  AttrTableCDPointer,
  LastAttrTable
};

/**
 * This uniquely indentifies attributes across tables.
 */
class AttributeUniqueId {
  AttrTableId d_tableId;
  uint64_t d_withinTypeId;

public:
  AttributeUniqueId() : d_tableId(LastAttrTable), d_withinTypeId(0){}

  AttributeUniqueId(AttrTableId tableId, uint64_t within)
    : d_tableId(tableId), d_withinTypeId(within)
  {}

  AttrTableId getTableId() const{ return d_tableId; }
  uint64_t getWithinTypeId() const{ return d_withinTypeId; }

};/* CVC4::expr::attr::AttributeUniqueId */

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
