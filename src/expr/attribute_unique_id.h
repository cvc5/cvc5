/*********************                                                        */
/*! \file attribute_unique_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

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
  AttrTableCDBool,
  AttrTableCDUInt64,
  AttrTableCDTNode,
  AttrTableCDNode,
  AttrTableCDString,
  AttrTableCDPointer,
  LastAttrTable
};

/**
 * This uniquely identifies attributes across tables.
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
