/*********************                                                        */
/*! \file pickle_data.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief This is a "pickle" for expressions, CVC4-internal view
 **
 ** This is the CVC4-internal view (private data structure) for a
 ** "pickle" for expressions.  The public-facing view is a "Pickle",
 ** which just points to a PickleData.  A pickle is a binary
 ** serialization of an expression that can be converted back into an
 ** expression in the same or another ExprManager.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__PICKLE_DATA_H
#define __CVC4__PICKLE_DATA_H

#include <sstream>
#include <deque>
#include <stack>
#include <exception>

#include "expr/expr.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "expr/variable_type_map.h"
#include "expr/kind.h"
#include "expr/metakind.h"

namespace CVC4 {

class NodeManager;

namespace expr {
namespace pickle {

const unsigned NBITS_BLOCK = 64;
const unsigned NBITS_KIND = __CVC4__EXPR__NODE_VALUE__NBITS__KIND;
const unsigned NBITS_NCHILDREN = __CVC4__EXPR__NODE_VALUE__NBITS__NCHILDREN;
const unsigned NBITS_CONSTBLOCKS = 32;

struct BlockHeader {
  unsigned d_kind          : NBITS_KIND;
};/* struct BlockHeader */

struct BlockHeaderOperator {
  unsigned d_kind          : NBITS_KIND;
  unsigned d_nchildren     : NBITS_NCHILDREN;
  unsigned long            : NBITS_BLOCK - (NBITS_KIND + NBITS_NCHILDREN);
};/* struct BlockHeaderOperator */

struct BlockHeaderConstant {
  unsigned d_kind          : NBITS_KIND;
  unsigned long d_constblocks   : NBITS_BLOCK - NBITS_KIND;
};/* struct BlockHeaderConstant */

struct BlockHeaderVariable {
  unsigned d_kind          : NBITS_KIND;
  unsigned long            : NBITS_BLOCK - NBITS_KIND;
};/* struct BlockHeaderVariable */

struct BlockBody  {
  unsigned long d_data          : NBITS_BLOCK;
};/* struct BlockBody */

union Block {
  BlockHeader d_header;
  BlockHeaderConstant d_headerConstant;
  BlockHeaderOperator d_headerOperator;
  BlockHeaderVariable d_headerVariable;

  BlockBody d_body;
};/* union Block */

class PickleData {
  typedef std::deque<Block> BlockDeque;
  BlockDeque d_blocks;

public:
  PickleData& operator<<(Block b) {
    enqueue(b);
    return (*this);
  }

  std::string toString() const;

  void enqueue(Block b) {
    d_blocks.push_back(b);
  }

  Block dequeue() {
    Block b = d_blocks.front();
    d_blocks.pop_front();
    return b;
  }

  bool empty() const { return d_blocks.empty(); }
  uint32_t size() const { return d_blocks.size(); }

  void swap(PickleData& other){
    d_blocks.swap(other.d_blocks);
  }

  void writeToStringStream(std::ostringstream& oss) const;
};/* class PickleData */

}/* CVC4::expr::pickle namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PICKLE_DATA_H */
