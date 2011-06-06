/*********************                                                        */
/*! \file node_manager.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): acsys, taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Expression manager implementation.
 **
 ** Expression manager implementation.
 **
 ** Reviewed by Chris Conway, Apr 5 2010 (bug #65).
 **/

#include "node_manager.h"

#include "theory/builtin/theory_builtin_type_rules.h"
#include "theory/booleans/theory_bool_type_rules.h"
#include "theory/uf/theory_uf_type_rules.h"
#include "theory/arith/theory_arith_type_rules.h"
#include "theory/arrays/theory_arrays_type_rules.h"
#include "theory/bv/theory_bv_type_rules.h"
#include "theory/datatypes/theory_datatypes_type_rules.h"

#include "util/Assert.h"
#include "util/options.h"
#include "util/stats.h"
#include "util/tls.h"

#include <algorithm>
#include <stack>
#include <ext/hash_set>

using namespace std;
using namespace CVC4::expr;
using __gnu_cxx::hash_set;

namespace CVC4 {

CVC4_THREADLOCAL(NodeManager*) NodeManager::s_current = NULL;

/**
 * This class sets it reference argument to true and ensures that it gets set
 * to false on destruction. This can be used to make sure a flag gets toggled
 * in a function even on exceptional exit (e.g., see reclaimZombies()).
 */
struct ScopedBool {
  bool& d_value;

  ScopedBool(bool& value) :
    d_value(value) {

    Debug("gc") << ">> setting ScopedBool\n";
    d_value = true;
  }

  ~ScopedBool() {
    Debug("gc") << "<< clearing ScopedBool\n";
    d_value = false;
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

NodeManager::NodeManager(context::Context* ctxt,
                         ExprManager* exprManager) :
  d_optionsAllocated(new Options()),
  d_options(d_optionsAllocated),
  d_statisticsRegistry(new StatisticsRegistry()),
  d_attrManager(ctxt),
  d_exprManager(exprManager),
  d_nodeUnderDeletion(NULL),
  d_inReclaimZombies(false) {
  init();
}


NodeManager::NodeManager(context::Context* ctxt,
                         ExprManager* exprManager,
                         const Options& options) :
  d_optionsAllocated(NULL),
  d_options(&options),
  d_statisticsRegistry(new StatisticsRegistry()),
  d_attrManager(ctxt),
  d_exprManager(exprManager),
  d_nodeUnderDeletion(NULL),
  d_inReclaimZombies(false) {
  init();
}

inline void NodeManager::init() {
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

  {
    ScopedBool dontGC(d_inReclaimZombies);
    d_attrManager.deleteAllAttributes();
  }

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    d_operators[i] = Node::null();
  }

  while(!d_zombies.empty()) {
    reclaimZombies();
  }

  poolRemove( &expr::NodeValue::s_null );

  if(Debug.isOn("gc:leaks")) {
    Debug("gc:leaks") << "still in pool:" << std::endl;
    for(NodeValuePool::const_iterator i = d_nodeValuePool.begin(),
          iend = d_nodeValuePool.end();
        i != iend;
        ++i) {
      Debug("gc:leaks") << "  " << *i
                        << " id=" << (*i)->d_id
                        << " rc=" << (*i)->d_rc
                        << " " << **i << std::endl;
    }
    Debug("gc:leaks") << ":end:" << std::endl;
  }

  delete d_statisticsRegistry;
  delete d_optionsAllocated;
}

void NodeManager::reclaimZombies() {
  // FIXME multithreading

  Debug("gc") << "reclaiming " << d_zombies.size() << " zombie(s)!\n";

  // during reclamation, reclaimZombies() is never supposed to be called
  Assert(! d_inReclaimZombies, "NodeManager::reclaimZombies() not re-entrant!");

  // whether exit is normal or exceptional, the Reclaim dtor is called
  // and ensures that d_inReclaimZombies is set back to false.
  ScopedBool r(d_inReclaimZombies);

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
  std::remove_copy_if(d_zombies.begin(),
                      d_zombies.end(),
                      std::back_inserter(zombies),
                      NodeValueReferenceCountNonZero());
  d_zombies.clear();

  for(vector<NodeValue*>::iterator i = zombies.begin();
      i != zombies.end();
      ++i) {
    NodeValue* nv = *i;

    // collect ONLY IF still zero
    if(nv->d_rc == 0) {
      if(Debug.isOn("gc")) {
        Debug("gc") << "deleting node value " << nv
                    << " [" << nv->d_id << "]: ";
        nv->printAst(Debug("gc"));
        Debug("gc") << std::endl;
      }

      // remove from the pool
      kind::MetaKind mk = nv->getMetaKind();
      if(mk != kind::metakind::VARIABLE) {
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
      if(mk == kind::metakind::CONSTANT) {
        // Destroy (call the destructor for) the C++ type representing
        // the constant in this NodeValue.  This is needed for
        // e.g. CVC4::Rational, since it has a gmp internal
        // representation that mallocs memory and should be cleaned
        // up.  (This won't delete a pointer value if used as a
        // constant, but then, you should probably use a smart-pointer
        // type for a constant payload.)
        kind::metakind::deleteNodeValueConstant(nv);
      }
      free(nv);
    }
  }
}/* NodeManager::reclaimZombies() */

TypeNode NodeManager::computeType(TNode n, bool check)
  throw (TypeCheckingExceptionPrivate, AssertionException) {
  TypeNode typeNode;

  // Infer the type
  switch(n.getKind()) {
  case kind::BUILTIN:
    typeNode = builtinOperatorType();
    break;
  case kind::SORT_TYPE:
    typeNode = kindType();
    break;
  case kind::APPLY:
    typeNode = CVC4::theory::builtin::ApplyTypeRule::computeType(this, n, check);
    break;
  case kind::EQUAL:
    typeNode = CVC4::theory::builtin::EqualityTypeRule::computeType(this, n, check);
    break;
  case kind::DISTINCT:
    typeNode = CVC4::theory::builtin::DistinctTypeRule::computeType(this, n, check);
    break;
  case kind::TUPLE:
    typeNode = CVC4::theory::builtin::TupleTypeRule::computeType(this, n, check);
    break;
  case kind::CONST_BOOLEAN:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::NOT:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::AND:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::IFF:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::IMPLIES:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::OR:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::XOR:
    typeNode = CVC4::theory::boolean::BooleanTypeRule::computeType(this, n, check);
    break;
  case kind::ITE:
    typeNode = CVC4::theory::boolean::IteTypeRule::computeType(this, n, check);
    break;
  case kind::APPLY_UF:
    typeNode = CVC4::theory::uf::UfTypeRule::computeType(this, n, check);
    break;
  case kind::PLUS:
    typeNode = CVC4::theory::arith::ArithOperatorTypeRule::computeType(this, n, check);
    break;
  case kind::MULT:
    typeNode = CVC4::theory::arith::ArithOperatorTypeRule::computeType(this, n, check);
    break;
  case kind::MINUS:
    typeNode = CVC4::theory::arith::ArithOperatorTypeRule::computeType(this, n, check);
    break;
  case kind::UMINUS:
    typeNode = CVC4::theory::arith::ArithOperatorTypeRule::computeType(this, n, check);
    break;
  case kind::DIVISION:
    typeNode = CVC4::theory::arith::ArithOperatorTypeRule::computeType(this, n, check);
    break;
  case kind::CONST_RATIONAL:
    typeNode = CVC4::theory::arith::ArithConstantTypeRule::computeType(this, n, check);
    break;
  case kind::CONST_INTEGER:
    typeNode = CVC4::theory::arith::ArithConstantTypeRule::computeType(this, n, check);
    break;
  case kind::LT:
    typeNode = CVC4::theory::arith::ArithPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::LEQ:
    typeNode = CVC4::theory::arith::ArithPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::GT:
    typeNode = CVC4::theory::arith::ArithPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::GEQ:
    typeNode = CVC4::theory::arith::ArithPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::SELECT:
    typeNode = CVC4::theory::arrays::ArraySelectTypeRule::computeType(this, n, check);
    break;
  case kind::STORE:
    typeNode = CVC4::theory::arrays::ArrayStoreTypeRule::computeType(this, n, check);
    break;
  case kind::CONST_BITVECTOR:
    typeNode = CVC4::theory::bv::BitVectorConstantTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_AND:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_OR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_XOR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_NOT:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_NAND:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_NOR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_XNOR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_COMP:
    typeNode = CVC4::theory::bv::BitVectorCompRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_MULT:
    typeNode = CVC4::theory::bv::BitVectorArithRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_PLUS:
    typeNode = CVC4::theory::bv::BitVectorArithRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SUB:
    typeNode = CVC4::theory::bv::BitVectorArithRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_NEG:
    typeNode = CVC4::theory::bv::BitVectorArithRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_UDIV:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_UREM:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SDIV:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SREM:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SMOD:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SHL:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_LSHR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ASHR:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ROTATE_LEFT:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ROTATE_RIGHT:
    typeNode = CVC4::theory::bv::BitVectorFixedWidthTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ULT:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ULE:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_UGT:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_UGE:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SLT:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SLE:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SGT:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SGE:
    typeNode = CVC4::theory::bv::BitVectorPredicateTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_EXTRACT:
    typeNode = CVC4::theory::bv::BitVectorExtractTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_CONCAT:
    typeNode = CVC4::theory::bv::BitVectorConcatRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_REPEAT:
    typeNode = CVC4::theory::bv::BitVectorRepeatTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_ZERO_EXTEND:
    typeNode = CVC4::theory::bv::BitVectorExtendTypeRule::computeType(this, n, check);
    break;
  case kind::BITVECTOR_SIGN_EXTEND:
    typeNode = CVC4::theory::bv::BitVectorExtendTypeRule::computeType(this, n, check);
    break;
  case kind::APPLY_CONSTRUCTOR:
    typeNode = CVC4::theory::datatypes::DatatypeConstructorTypeRule::computeType(this, n, check);
    break;
  case kind::APPLY_SELECTOR:
    typeNode = CVC4::theory::datatypes::DatatypeSelectorTypeRule::computeType(this, n, check);
    break;
  case kind::APPLY_TESTER:
    typeNode = CVC4::theory::datatypes::DatatypeTesterTypeRule::computeType(this, n, check);
    break;
  case kind::APPLY_TYPE_ASCRIPTION:
    typeNode = CVC4::theory::datatypes::DatatypeAscriptionTypeRule::computeType(this, n, check);
    break;
  default:
    Debug("getType") << "FAILURE" << std::endl;
    Unhandled(n.getKind());
  }

  setAttribute(n, TypeAttr(), typeNode);
  setAttribute(n, TypeCheckedAttr(),
               check || getAttribute(n, TypeCheckedAttr()));

  return typeNode;
}

TypeNode NodeManager::getType(TNode n, bool check)
  throw (TypeCheckingExceptionPrivate, AssertionException) {
  // Many theories' type checkers call Node::getType() directly.
  // This is incorrect, since "this" might not be the caller's
  // curent node manager.  Rather than force the individual typecheckers
  // not to do this (by policy, which would be imperfect and lead
  // to hard-to-find bugs, which it has in the past), we just
  // set this node manager to be current for the duration of this
  // check.
  NodeManagerScope nms(this);

  TypeNode typeNode;
  bool hasType = getAttribute(n, TypeAttr(), typeNode);
  bool needsCheck = check && !getAttribute(n, TypeCheckedAttr());

  Debug("getType") << "getting type for " << n << std::endl;

  if(needsCheck && !d_options->earlyTypeChecking) {
    /* Iterate and compute the children bottom up. This avoids stack
       overflows in computeType() when the Node graph is really deep,
       which should only affect us when we're type checking lazily. */
    stack<TNode> worklist;
    worklist.push(n);

    while( !worklist.empty() ) {
      TNode m = worklist.top();

      bool readyToCompute = true;

      for( TNode::iterator it = m.begin(), end = m.end();
           it != end;
           ++it ) {
        if( !hasAttribute(*it, TypeAttr())
            || (check && !getAttribute(*it, TypeCheckedAttr())) ) {
          readyToCompute = false;
          worklist.push(*it);
        }
      }

      if( readyToCompute ) {
        /* All the children have types, time to compute */
        typeNode = computeType(m, check);
        worklist.pop();
      }
    } // end while

    /* Last type computed in loop should be the type of n */
    Assert( typeNode == getAttribute(n, TypeAttr()) );
  } else if( !hasType || needsCheck ) {
    /* We can compute the type top-down, without worrying about
       deep recursion. */
    typeNode = computeType(n, check);
  }

  /* The type should be have been computed and stored. */
  Assert( hasAttribute(n, TypeAttr()) );
  /* The check should have happened, if we asked for it. */
  Assert( !check || getAttribute(n, TypeCheckedAttr()) );

  Debug("getType") << "type of " << n << " is " << typeNode << std::endl;
  return typeNode;
}

TypeNode NodeManager::mkConstructorType(const Datatype::Constructor& constructor,
                                        TypeNode range) {
  std::vector<TypeNode> sorts;
  Debug("datatypes") << "ctor name: " << constructor.getName() << std::endl;
  for(Datatype::Constructor::const_iterator i = constructor.begin();
      i != constructor.end();
      ++i) {
    TypeNode selectorType = *(*i).getSelector().getType().d_typeNode;
    Debug("datatypes") << selectorType << std::endl;
    TypeNode sort = selectorType[1];

    // should be guaranteed here already, but just in case
    Assert(!sort.isFunctionLike());

    Debug("datatypes") << "ctor sort: " << sort << std::endl;
    sorts.push_back(sort);
  }
  Debug("datatypes") << "ctor range: " << range << std::endl;
  CheckArgument(!range.isFunctionLike(), range,
                "cannot create higher-order function types");
  sorts.push_back(range);
  return mkTypeNode(kind::CONSTRUCTOR_TYPE, sorts);
}

}/* CVC4 namespace */
