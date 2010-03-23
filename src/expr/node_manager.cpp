/*********************                                                        */
/** node_manager.cpp
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Expression manager implementation.
 **/

#include "node_manager.h"

#include <ext/hash_set>

using namespace std;
using namespace CVC4::expr;
using __gnu_cxx::hash_set;

namespace CVC4 {

__thread NodeManager* NodeManager::s_current = 0;

NodeManager::~NodeManager() {
  NodeManagerScope nms(this);
  while(!d_zombies.empty()) {
    reclaimZombies();
  }

  poolRemove( &expr::NodeValue::s_null );
}

NodeValue* NodeManager::poolLookup(NodeValue* nv) const {
  NodeValuePool::const_iterator find = d_nodeValuePool.find(nv);
  if(find == d_nodeValuePool.end()) {
    return NULL;
  } else {
    return *find;
  }
}

/**
 * This class ensure that NodeManager::d_reclaiming gets set to false
 * even on exceptional exit from NodeManager::reclaimZombies().
 */
struct Reclaim {
  bool& d_reclaimField;
  Reclaim(bool& reclaim) :
    d_reclaimField(reclaim) {

    Debug("gc") << ">> setting RECLAIM field\n";
    d_reclaimField = true;
  }
  ~Reclaim() {
    Debug("gc") << "<< clearing RECLAIM field\n";
    d_reclaimField = false;
  }
};

struct NVReclaim {
  NodeValue*& d_reclaimField;
  NVReclaim(NodeValue*& reclaim) :
    d_reclaimField(reclaim) {

    Debug("gc") << ">> setting NVRECLAIM field\n";
  }
  ~NVReclaim() {
    Debug("gc") << "<< clearing NVRECLAIM field\n";
    d_reclaimField = NULL;
  }
};

void NodeManager::reclaimZombies() {
  // FIXME multithreading

  Debug("gc") << "reclaiming " << d_zombies.size() << " zombie(s)!\n";

  // during reclamation, reclaimZombies() is never supposed to be called
  Assert(! d_reclaiming, "NodeManager::reclaimZombies() not re-entrant!");
  Reclaim r(d_reclaiming);

  // We copy the set away and clear the NodeManager's set of zombies.
  // This is because reclaimZombie() decrements the RC of the
  // NodeValue's children, which may (recursively) reclaim them.
  //
  // Let's say we're reclaiming zombie NodeValue "A" and its child "B"
  // then becomes a zombie (NodeManager::gc(B) is called).
  //
  // One way to handle B's zombification is simply to put it into
  // d_zombies.  This is what we do.  However, if we're currently
  // processing d_zombies in the loop below, such addition may be
  // invisible to us (B is leaked) or even invalidate our iterator,
  // causing a crash.

  vector<NodeValue*> zombies;
  zombies.reserve(d_zombies.size());
  std::copy(d_zombies.begin(),
            d_zombies.end(),
            std::back_inserter(zombies));
  d_zombies.clear();

  for(vector<NodeValue*>::iterator i = zombies.begin();
      i != zombies.end();
      ++i) {
    NodeValue* nv = *i;

    // collect ONLY IF still zero
    if(nv->d_rc == 0) {
      Debug("gc") << "deleting node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";

      // remove from the pool
      if(nv->getKind() != kind::VARIABLE) {
        poolRemove(nv);
      }
      NVReclaim rc(d_underTheShotgun);
      d_underTheShotgun = nv;

      // remove attributes
      d_attrManager.deleteAllAttributes(nv);

      // decr ref counts of children
      nv->decrRefCounts();
      free(nv);
    }
  }
}

}/* CVC4 namespace */
