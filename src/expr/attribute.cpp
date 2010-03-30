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

#include <utility>

using namespace std;

namespace CVC4 {
namespace expr {
namespace attr {

/**
 * Search for the NodeValue in all attribute tables and remove it,
 * calling the cleanup function if one is defined.
 */
template <class T>
inline void AttributeManager::deleteFromTable(AttrHash<T>& table,
                                              NodeValue* nv) {
  for(uint64_t id = 0; id < attr::LastAttributeId<T, false>::s_id; ++id) {
    typedef AttributeTraits<T, false> traits_t;
    typedef AttrHash<T> hash_t;
    pair<uint64_t, NodeValue*> pr = std::make_pair(id, nv);
    if(traits_t::cleanup[id] != NULL) {
      typename hash_t::iterator i = table.find(pr);
      if(i != table.end()) {
        traits_t::cleanup[id]((*i).second);
        table.erase(pr);
      }
    } else {
      table.erase(pr);
    }
  }
}

void AttributeManager::deleteAllAttributes(NodeValue* nv) {
  d_bools.erase(nv);
  deleteFromTable(d_ints, nv);
  deleteFromTable(d_exprs, nv);
  deleteFromTable(d_strings, nv);
  deleteFromTable(d_ptrs, nv);

  // FIXME CD-bools in optimized table
  for(unsigned id = 0; id < attr::LastAttributeId<bool, true>::s_id; ++id) {
    Debug("gc") << "looking for " << id << " x " << nv << ":" << *nv << std::endl;
    d_cdbools.obliterate(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<uint64_t, true>::s_id; ++id) {
    d_cdints.obliterate(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<TNode, true>::s_id; ++id) {
    d_cdexprs.obliterate(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<std::string, true>::s_id; ++id) {
    d_cdstrings.obliterate(std::make_pair(id, nv));
  }
  for(unsigned id = 0; id < attr::LastAttributeId<void*, true>::s_id; ++id) {
    d_cdptrs.obliterate(std::make_pair(id, nv));
  }
}

}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */
