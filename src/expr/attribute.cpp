/*********************                                                        */
/** attribute.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** AttributeManager implementation.
 **/

#include "expr/attribute.h"
#include "expr/node_value.h"
#include "util/output.h"

namespace CVC4 {
namespace expr {
namespace attr {

void AttributeManager::deleteAllAttributes(NodeValue* nv) {
  d_bools.erase(nv);
  for(unsigned id = 0; id < attr::LastAttributeId<uint64_t, false>::s_id; ++id) {
    d_ints.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<TNode, false>::s_id; ++id) {
    d_exprs.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<std::string, false>::s_id; ++id) {
    d_strings.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<void*, false>::s_id; ++id) {
    d_ptrs.erase(std::make_pair(id, nv));
  }

  // FIXME CD-bools in optimized table
        /*
  for(unsigned id = 0; id < attr::LastAttributeId<bool, true>::s_id; ++id) {
    d_cdbools.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<uint64_t, true>::s_id; ++id) {
    d_cdints.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<TNode, true>::s_id; ++id) {
    d_cdexprs.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<std::string, true>::s_id; ++id) {
    d_cdstrings.erase(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<void*, true>::s_id; ++id) {
    d_cdptrs.erase(std::make_pair(id, nv));
  }
        */
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
