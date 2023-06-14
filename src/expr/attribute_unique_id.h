/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#pragma once

// ATTRIBUTE IDs ============================================================

namespace cvc5::internal {
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

}; /* cvc5::internal::expr::attr::AttributeUniqueId */

}  // namespace attr
}  // namespace expr
}  // namespace cvc5::internal
