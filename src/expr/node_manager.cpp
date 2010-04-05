/*********************                                                        */
/** node_manager.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, taking
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

NodeManager::NodeManager(context::Context* ctxt) :
  d_attrManager(ctxt),
  d_nodeUnderDeletion(NULL),
  d_reclaiming(false) {
  poolInsert( &expr::NodeValue::s_null );

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    Kind k = Kind(i);

    if(hasOperator(k)) {
      d_operators[i] = mkConst(Kind(k));
    }
  }
}

NodeManager::~NodeManager() {
  // have to ensure "this" is the current NodeManager during
  // destruction of operators, because they get GCed.

  NodeManagerScope nms(this);

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    d_operators[i] = Node::null();
  }

  while(!d_zombies.empty()) {
    reclaimZombies();
  }

  poolRemove( &expr::NodeValue::s_null );
}

/**
 * This class ensures that NodeManager::d_reclaiming gets set to false
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

/**
 * Similarly, ensure d_nodeUnderDeletion gets set to NULL even on
 * exceptional exit from NodeManager::reclaimZombies().
 */
struct NVReclaim {
  NodeValue*& d_deletionField;

  NVReclaim(NodeValue*& deletionField) :
    d_deletionField(deletionField) {

    Debug("gc") << ">> setting NVRECLAIM field\n";
  }

  ~NVReclaim() {
    Debug("gc") << "<< clearing NVRECLAIM field\n";
    d_deletionField = NULL;
  }
};

void NodeManager::reclaimZombies() {
  // FIXME multithreading

  Debug("gc") << "reclaiming " << d_zombies.size() << " zombie(s)!\n";

  // during reclamation, reclaimZombies() is never supposed to be called
  Assert(! d_reclaiming, "NodeManager::reclaimZombies() not re-entrant!");

  // whether exit is normal or exceptional, the Reclaim dtor is called
  // and ensures that d_reclaiming is set back to false.
  Reclaim r(d_reclaiming);

  // We copy the set away and clear the NodeManager's set of zombies.
  // This is because reclaimZombie() decrements the RC of the
  // NodeValue's children, which may (recursively) reclaim them.
  //
  // Let's say we're reclaiming zombie NodeValue "A" and its child "B"
  // then becomes a zombie (NodeManager::markForDeletion(B) is called).
  //
  // One way to handle B's zombification would be simply to put it
  // into d_zombies.  This is what we do.  However, if we were to
  // concurrently process d_zombies in the loop below, such addition
  // may be invisible to us (B is leaked) or even invalidate our
  // iterator, causing a crash.  So we need to copy the set away.

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
                  << " [" << nv->d_id << "]: " << *nv << "\n";

      // remove from the pool
      if(nv->getKind() != kind::VARIABLE) {
        poolRemove(nv);
      }

      // whether exit is normal or exceptional, the NVReclaim dtor is
      // called and ensures that d_nodeUnderDeletion is set back to
      // NULL.
      NVReclaim rc(d_nodeUnderDeletion);
      d_nodeUnderDeletion = nv;

      // remove attributes
      d_attrManager.deleteAllAttributes(nv);

      // decr ref counts of children
      nv->decrRefCounts();
      free(nv);
    }
  }
}/* NodeManager::reclaimZombies() */

}/* CVC4 namespace */
