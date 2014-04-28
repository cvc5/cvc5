/*********************                                                        */
/*! \file node_manager.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): ACSYS, Tim King, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Expression manager implementation.
 **
 ** Expression manager implementation.
 **
 ** Reviewed by Chris Conway, Apr 5 2010 (bug #65).
 **/

#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"

#include "expr/attribute.h"
#include "util/cvc4_assert.h"
#include "options/options.h"
#include "util/statistics_registry.h"
#include "util/tls.h"

#include "expr/type_checker.h"

#include <algorithm>
#include <stack>
#include <utility>
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
  d_options(new Options()),
  d_statisticsRegistry(new StatisticsRegistry()),
  next_id(0),
  d_attrManager(new expr::attr::AttributeManager(ctxt)),
  d_exprManager(exprManager),
  d_nodeUnderDeletion(NULL),
  d_inReclaimZombies(false),
  d_abstractValueCount(0),
  d_skolemCounter(0) {
  init();
}

NodeManager::NodeManager(context::Context* ctxt,
                         ExprManager* exprManager,
                         const Options& options) :
  d_options(new Options(options)),
  d_statisticsRegistry(new StatisticsRegistry()),
  next_id(0),
  d_attrManager(new expr::attr::AttributeManager(ctxt)),
  d_exprManager(exprManager),
  d_nodeUnderDeletion(NULL),
  d_inReclaimZombies(false),
  d_abstractValueCount(0),
  d_skolemCounter(0) {
  init();
}

void NodeManager::init() {
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
    d_attrManager->deleteAllAttributes();
  }

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    d_operators[i] = Node::null();
  }

  Assert(!d_attrManager->inGarbageCollection() );
  while(!d_zombies.empty()) {
    reclaimZombies();
  }

  poolRemove( &expr::NodeValue::s_null );

  if(Debug.isOn("gc:leaks")) {
    Debug("gc:leaks") << "still in pool:" << endl;
    for(NodeValuePool::const_iterator i = d_nodeValuePool.begin(),
          iend = d_nodeValuePool.end();
        i != iend;
        ++i) {
      Debug("gc:leaks") << "  " << *i
                        << " id=" << (*i)->d_id
                        << " rc=" << (*i)->d_rc
                        << " " << **i << endl;
    }
    Debug("gc:leaks") << ":end:" << endl;
  }

  delete d_statisticsRegistry;
  delete d_attrManager;
  delete d_options;
}

void NodeManager::reclaimZombies() {
  // FIXME multithreading
  Assert(!d_attrManager->inGarbageCollection());

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
  remove_copy_if(d_zombies.begin(),
                 d_zombies.end(),
                 back_inserter(zombies),
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
        Debug("gc") << endl;
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
      d_attrManager->deleteAllAttributes(nv);

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

TypeNode NodeManager::getType(TNode n, bool check)
  throw(TypeCheckingExceptionPrivate, AssertionException) {

  // Many theories' type checkers call Node::getType() directly.  This
  // is incorrect, since "this" might not be the caller's curent node
  // manager.  Rather than force the individual typecheckers not to do
  // this (by policy, which would be imperfect and lead to
  // hard-to-find bugs, which it has in the past), we just set this
  // node manager to be current for the duration of this check.
  //
  NodeManagerScope nms(this);

  TypeNode typeNode;
  bool hasType = getAttribute(n, TypeAttr(), typeNode);
  bool needsCheck = check && !getAttribute(n, TypeCheckedAttr());

  Debug("getType") << "getting type for " << n << endl;

  if(needsCheck && !(*d_options)[options::earlyTypeChecking]) {
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
        typeNode = TypeChecker::computeType(this, m, check);
        worklist.pop();
      }
    } // end while

    /* Last type computed in loop should be the type of n */
    Assert( typeNode == getAttribute(n, TypeAttr()) );
  } else if( !hasType || needsCheck ) {
    /* We can compute the type top-down, without worrying about
       deep recursion. */
    typeNode = TypeChecker::computeType(this, n, check);
  }

  /* The type should be have been computed and stored. */
  Assert( hasAttribute(n, TypeAttr()) );
  /* The check should have happened, if we asked for it. */
  Assert( !check || getAttribute(n, TypeCheckedAttr()) );

  Debug("getType") << "type of " << n << " is " << typeNode << endl;
  return typeNode;
}

Node NodeManager::mkSkolem(const std::string& prefix, const TypeNode& type, const std::string& comment, int flags) {
  Node n = NodeBuilder<0>(this, kind::SKOLEM);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  if((flags & SKOLEM_EXACT_NAME) == 0) {
    stringstream name;
    name << prefix << '_' << ++d_skolemCounter;
    setAttribute(n, expr::VarNameAttr(), name.str());
  } else {
    setAttribute(n, expr::VarNameAttr(), prefix);
  }
  if((flags & SKOLEM_NO_NOTIFY) == 0) {
    for(vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
      (*i)->nmNotifyNewSkolem(n, comment, (flags & SKOLEM_IS_GLOBAL) == SKOLEM_IS_GLOBAL);
    }
  }
  return n;
}

TypeNode NodeManager::mkConstructorType(const DatatypeConstructor& constructor,
                                        TypeNode range) {
  vector<TypeNode> sorts;
  Debug("datatypes") << "ctor name: " << constructor.getName() << endl;
  for(DatatypeConstructor::const_iterator i = constructor.begin();
      i != constructor.end();
      ++i) {
    TypeNode selectorType = *(*i).getSelector().getType().d_typeNode;
    Debug("datatypes") << selectorType << endl;
    TypeNode sort = selectorType[1];

    // should be guaranteed here already, but just in case
    Assert(!sort.isFunctionLike());

    Debug("datatypes") << "ctor sort: " << sort << endl;
    sorts.push_back(sort);
  }
  Debug("datatypes") << "ctor range: " << range << endl;
  CheckArgument(!range.isFunctionLike(), range,
                "cannot create higher-order function types");
  sorts.push_back(range);
  return mkTypeNode(kind::CONSTRUCTOR_TYPE, sorts);
}

TypeNode NodeManager::mkPredicateSubtype(Expr lambda)
  throw(TypeCheckingExceptionPrivate) {

  Node lambdan = Node::fromExpr(lambda);

  if(lambda.isNull()) {
    throw TypeCheckingExceptionPrivate(lambdan, "cannot make a predicate subtype based on null expression");
  }

  TypeNode tn = lambdan.getType();
  if(! tn.isPredicateLike() ||
     tn.getArgTypes().size() != 1) {
    stringstream ss;
    ss << "expected a predicate of one argument to define predicate subtype, but got type `" << tn << "'";
    throw TypeCheckingExceptionPrivate(lambdan, ss.str());
  }

  return TypeNode(mkTypeConst(Predicate(lambda)));
}

TypeNode NodeManager::mkPredicateSubtype(Expr lambda, Expr witness)
  throw(TypeCheckingExceptionPrivate) {

  Node lambdan = Node::fromExpr(lambda);

  if(lambda.isNull()) {
    throw TypeCheckingExceptionPrivate(lambdan, "cannot make a predicate subtype based on null expression");
  }

  TypeNode tn = lambdan.getType();
  if(! tn.isPredicateLike() ||
     tn.getArgTypes().size() != 1) {
    stringstream ss;
    ss << "expected a predicate of one argument to define predicate subtype, but got type `" << tn << "'";
    throw TypeCheckingExceptionPrivate(lambdan, ss.str());
  }

  return TypeNode(mkTypeConst(Predicate(lambda, witness)));
}

TypeNode NodeManager::mkSubrangeType(const SubrangeBounds& bounds)
  throw(TypeCheckingExceptionPrivate) {
  return TypeNode(mkTypeConst(bounds));
}

TypeNode NodeManager::getDatatypeForTupleRecord(TypeNode t) {
  Assert(t.isTuple() || t.isRecord());

  // if the type doesn't have an associated datatype, then make one for it
  TypeNode& dtt = d_tupleAndRecordTypes[t];
  if(dtt.isNull()) {
    if(t.isTuple()) {
      Datatype dt("__cvc4_tuple");
      DatatypeConstructor c("__cvc4_tuple_ctor");
      for(TypeNode::const_iterator i = t.begin(); i != t.end(); ++i) {
        c.addArg("__cvc4_tuple_stor", (*i).toType());
      }
      dt.addConstructor(c);
      dtt = TypeNode::fromType(toExprManager()->mkDatatypeType(dt));
      Debug("tuprec") << "REWROTE " << t << " to " << dtt << std::endl;
      dtt.setAttribute(DatatypeTupleAttr(), t);
    } else {
      const Record& rec = t.getRecord();
      Datatype dt("__cvc4_record");
      DatatypeConstructor c("__cvc4_record_ctor");
      for(Record::const_iterator i = rec.begin(); i != rec.end(); ++i) {
        c.addArg((*i).first, (*i).second);
      }
      dt.addConstructor(c);
      dtt = TypeNode::fromType(toExprManager()->mkDatatypeType(dt));
      Debug("tuprec") << "REWROTE " << t << " to " << dtt << std::endl;
      dtt.setAttribute(DatatypeRecordAttr(), t);
    }
  } else {
    Debug("tuprec") << "REUSING cached " << t << ": " << dtt << std::endl;
  }
  Assert(!dtt.isNull());
  return dtt;
}

void NodeManager::reclaimAllZombies(){
  reclaimZombiesUntil(0u);
}

/** Reclaim zombies while there are more than k nodes in the pool (if possible).*/
void NodeManager::reclaimZombiesUntil(uint32_t k){
  if(safeToReclaimZombies()){
    while(poolSize() >= k && !d_zombies.empty()){
      reclaimZombies();
    }
  }
}

size_t NodeManager::poolSize() const{
  return d_nodeValuePool.size();
}

TypeNode NodeManager::mkSort(uint32_t flags) {
  NodeBuilder<1> nb(this, kind::SORT_TYPE);
  Node sortTag = NodeBuilder<0>(this, kind::SORT_TAG);
  nb << sortTag;
  TypeNode tn = nb.constructTypeNode();
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewSort(tn, flags);
  }
  return tn;
}

TypeNode NodeManager::mkSort(const std::string& name, uint32_t flags) {
  NodeBuilder<1> nb(this, kind::SORT_TYPE);
  Node sortTag = NodeBuilder<0>(this, kind::SORT_TAG);
  nb << sortTag;
  TypeNode tn = nb.constructTypeNode();
  setAttribute(tn, expr::VarNameAttr(), name);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewSort(tn, flags);
  }
  return tn;
}

TypeNode NodeManager::mkSort(TypeNode constructor,
                                    const std::vector<TypeNode>& children,
                                    uint32_t flags) {
  Assert(constructor.getKind() == kind::SORT_TYPE &&
         constructor.getNumChildren() == 0,
         "expected a sort constructor");
  Assert(children.size() > 0, "expected non-zero # of children");
  Assert( hasAttribute(constructor.d_nv, expr::SortArityAttr()) &&
          hasAttribute(constructor.d_nv, expr::VarNameAttr()),
          "expected a sort constructor" );
  std::string name = getAttribute(constructor.d_nv, expr::VarNameAttr());
  Assert(getAttribute(constructor.d_nv, expr::SortArityAttr()) == children.size(),
         "arity mismatch in application of sort constructor");
  NodeBuilder<> nb(this, kind::SORT_TYPE);
  Node sortTag = Node(constructor.d_nv->d_children[0]);
  nb << sortTag;
  nb.append(children);
  TypeNode type = nb.constructTypeNode();
  setAttribute(type, expr::VarNameAttr(), name);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyInstantiateSortConstructor(constructor, type, flags);
  }
  return type;
}

TypeNode NodeManager::mkSortConstructor(const std::string& name,
                                        size_t arity) {
  Assert(arity > 0);
  NodeBuilder<> nb(this, kind::SORT_TYPE);
  Node sortTag = NodeBuilder<0>(this, kind::SORT_TAG);
  nb << sortTag;
  TypeNode type = nb.constructTypeNode();
  setAttribute(type, expr::VarNameAttr(), name);
  setAttribute(type, expr::SortArityAttr(), arity);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewSortConstructor(type);
  }
  return type;
}

Node NodeManager::mkVar(const std::string& name, const TypeNode& type, uint32_t flags) {
  Node n = NodeBuilder<0>(this, kind::VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  setAttribute(n, expr::VarNameAttr(), name);
  setAttribute(n, expr::GlobalVarAttr(), flags & ExprManager::VAR_FLAG_GLOBAL);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewVar(n, flags);
  }
  return n;
}

Node* NodeManager::mkVarPtr(const std::string& name,
                            const TypeNode& type, uint32_t flags) {
  Node* n = NodeBuilder<0>(this, kind::VARIABLE).constructNodePtr();
  setAttribute(*n, TypeAttr(), type);
  setAttribute(*n, TypeCheckedAttr(), true);
  setAttribute(*n, expr::VarNameAttr(), name);
  setAttribute(*n, expr::GlobalVarAttr(), flags & ExprManager::VAR_FLAG_GLOBAL);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewVar(*n, flags);
  }
  return n;
}

Node NodeManager::mkBoundVar(const std::string& name, const TypeNode& type) {
  Node n = mkBoundVar(type);
  setAttribute(n, expr::VarNameAttr(), name);
  return n;
}

Node* NodeManager::mkBoundVarPtr(const std::string& name,
                                 const TypeNode& type) {
  Node* n = mkBoundVarPtr(type);
  setAttribute(*n, expr::VarNameAttr(), name);
  return n;
}

Node NodeManager::mkVar(const TypeNode& type, uint32_t flags) {
  Node n = NodeBuilder<0>(this, kind::VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  setAttribute(n, expr::GlobalVarAttr(), flags & ExprManager::VAR_FLAG_GLOBAL);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewVar(n, flags);
  }
  return n;
}

Node* NodeManager::mkVarPtr(const TypeNode& type, uint32_t flags) {
  Node* n = NodeBuilder<0>(this, kind::VARIABLE).constructNodePtr();
  setAttribute(*n, TypeAttr(), type);
  setAttribute(*n, TypeCheckedAttr(), true);
  setAttribute(*n, expr::GlobalVarAttr(), flags & ExprManager::VAR_FLAG_GLOBAL);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewVar(*n, flags);
  }
  return n;
}

Node NodeManager::mkBoundVar(const TypeNode& type) {
  Node n = NodeBuilder<0>(this, kind::BOUND_VARIABLE);
  setAttribute(n, TypeAttr(), type);
  setAttribute(n, TypeCheckedAttr(), true);
  return n;
}

Node* NodeManager::mkBoundVarPtr(const TypeNode& type) {
  Node* n = NodeBuilder<0>(this, kind::BOUND_VARIABLE).constructNodePtr();
  setAttribute(*n, TypeAttr(), type);
  setAttribute(*n, TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkInstConstant(const TypeNode& type) {
  Node n = NodeBuilder<0>(this, kind::INST_CONSTANT);
  n.setAttribute(TypeAttr(), type);
  n.setAttribute(TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkAbstractValue(const TypeNode& type) {
  Node n = mkConst(AbstractValue(++d_abstractValueCount));
  n.setAttribute(TypeAttr(), type);
  n.setAttribute(TypeCheckedAttr(), true);
  return n;
}

bool NodeManager::safeToReclaimZombies() const{
  // FIXME multithreading
  return !d_inReclaimZombies && !d_attrManager->inGarbageCollection();
}

void NodeManager::deleteAttributes(const std::vector<const expr::attr::AttributeUniqueId*>& ids){
  d_attrManager->deleteAttributes(ids);
}

void NodeManager::debugHook(int debugFlag){
  // For debugging purposes only, DO NOT CHECK IN ANY CODE!
}

}/* CVC4 namespace */
