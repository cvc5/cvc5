/*********************                                                        */
/*! \file node_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Expression manager implementation.
 **
 ** Expression manager implementation.
 **
 ** Reviewed by Chris Conway, Apr 5 2010 (bug #65).
 **/
#include "expr/node_manager.h"

#include <algorithm>
#include <stack>
#include <utility>

#include "base/check.h"
#include "base/listener.h"
#include "expr/attribute.h"
#include "expr/dtype.h"
#include "expr/node_manager_attributes.h"
#include "expr/node_manager_listeners.h"
#include "expr/skolem_manager.h"
#include "expr/type_checker.h"
#include "options/options.h"
#include "options/smt_options.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

using namespace std;
using namespace CVC4::expr;

namespace CVC4 {

thread_local NodeManager* NodeManager::s_current = NULL;

namespace {

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

} // namespace

namespace attr {
  struct LambdaBoundVarListTag { };
}/* CVC4::attr namespace */

// attribute that stores the canonical bound variable list for function types
typedef expr::Attribute<attr::LambdaBoundVarListTag, Node> LambdaBoundVarListAttr;

NodeManager::NodeManager(ExprManager* exprManager)
    : d_options(new Options()),
      d_statisticsRegistry(new StatisticsRegistry()),
      d_resourceManager(new ResourceManager(*d_statisticsRegistry, *d_options)),
      d_skManager(new SkolemManager),
      d_registrations(new ListenerRegistrationList()),
      next_id(0),
      d_attrManager(new expr::attr::AttributeManager()),
      d_exprManager(exprManager),
      d_nodeUnderDeletion(NULL),
      d_inReclaimZombies(false),
      d_abstractValueCount(0),
      d_skolemCounter(0)
{
  init();
}

NodeManager::NodeManager(ExprManager* exprManager, const Options& options)
    : d_options(new Options()),
      d_statisticsRegistry(new StatisticsRegistry()),
      d_resourceManager(new ResourceManager(*d_statisticsRegistry, *d_options)),
      d_skManager(new SkolemManager),
      d_registrations(new ListenerRegistrationList()),
      next_id(0),
      d_attrManager(new expr::attr::AttributeManager()),
      d_exprManager(exprManager),
      d_nodeUnderDeletion(NULL),
      d_inReclaimZombies(false),
      d_abstractValueCount(0),
      d_skolemCounter(0)
{
  d_options->copyValues(options);
  init();
}

void NodeManager::init() {
  poolInsert( &expr::NodeValue::null() );

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    Kind k = Kind(i);

    if(hasOperator(k)) {
      d_operators[i] = mkConst(Kind(k));
    }
  }
  d_resourceManager->setHardLimit((*d_options)[options::hardLimit]);
  if((*d_options)[options::perCallResourceLimit] != 0) {
    d_resourceManager->setResourceLimit((*d_options)[options::perCallResourceLimit], false);
  }
  if((*d_options)[options::cumulativeResourceLimit] != 0) {
    d_resourceManager->setResourceLimit((*d_options)[options::cumulativeResourceLimit], true);
  }
  if((*d_options)[options::perCallMillisecondLimit] != 0) {
    d_resourceManager->setTimeLimit((*d_options)[options::perCallMillisecondLimit], false);
  }
  if((*d_options)[options::cumulativeMillisecondLimit] != 0) {
    d_resourceManager->setTimeLimit((*d_options)[options::cumulativeMillisecondLimit], true);
  }
  if((*d_options)[options::cpuTime]) {
    d_resourceManager->useCPUTime(true);
  }

  // Do not notify() upon registration as these were handled manually above.
  d_registrations->add(d_options->registerTlimitListener(
      new TlimitListener(d_resourceManager), false));
  d_registrations->add(d_options->registerTlimitPerListener(
      new TlimitPerListener(d_resourceManager), false));
  d_registrations->add(d_options->registerRlimitListener(
      new RlimitListener(d_resourceManager), false));
  d_registrations->add(d_options->registerRlimitPerListener(
      new RlimitPerListener(d_resourceManager), false));
}

NodeManager::~NodeManager() {
  // have to ensure "this" is the current NodeManager during
  // destruction of operators, because they get GCed.

  NodeManagerScope nms(this);

  // Destroy skolem manager before cleaning up attributes and zombies
  d_skManager = nullptr;

  {
    ScopedBool dontGC(d_inReclaimZombies);
    // hopefully by this point all SmtEngines have been deleted
    // already, along with all their attributes
    d_attrManager->deleteAllAttributes();
  }

  for(unsigned i = 0; i < unsigned(kind::LAST_KIND); ++i) {
    d_operators[i] = Node::null();
  }

  d_unique_vars.clear();

  TypeNode dummy;
  d_tt_cache.d_children.clear();
  d_tt_cache.d_data = dummy;
  d_rt_cache.d_children.clear();
  d_rt_cache.d_data = dummy;

  d_ownedDTypes.clear();

  Assert(!d_attrManager->inGarbageCollection());

  std::vector<NodeValue*> order = TopologicalSort(d_maxedOut);
  d_maxedOut.clear();

  while (!d_zombies.empty() || !order.empty()) {
    if (d_zombies.empty()) {
      // Delete the maxed out nodes in toplogical order once we know
      // there are no additional zombies, or other nodes to worry about.
      Assert(!order.empty());
      // We process these in reverse to reverse the topological order.
      NodeValue* greatest_maxed_out = order.back();
      order.pop_back();
      Assert(greatest_maxed_out->HasMaximizedReferenceCount());
      Debug("gc") << "Force zombify " << greatest_maxed_out << std::endl;
      greatest_maxed_out->d_rc = 0;
      markForDeletion(greatest_maxed_out);
    } else {
      reclaimZombies();
    }
  }

  poolRemove( &expr::NodeValue::null() );

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

  // defensive coding, in case destruction-order issues pop up (they often do)
  delete d_resourceManager;
  d_resourceManager = NULL;
  delete d_statisticsRegistry;
  d_statisticsRegistry = NULL;
  delete d_registrations;
  d_registrations = NULL;
  delete d_attrManager;
  d_attrManager = NULL;
  delete d_options;
  d_options = NULL;
}

size_t NodeManager::registerDatatype(std::shared_ptr<DType> dt)
{
  size_t sz = d_ownedDTypes.size();
  d_ownedDTypes.push_back(dt);
  return sz;
}

const DType& NodeManager::getDTypeForIndex(unsigned index) const
{
  Assert(index < d_ownedDTypes.size());
  return *d_ownedDTypes[index];
}

void NodeManager::reclaimZombies() {
  // FIXME multithreading
  Assert(!d_attrManager->inGarbageCollection());

  Debug("gc") << "reclaiming " << d_zombies.size() << " zombie(s)!\n";

  // during reclamation, reclaimZombies() is never supposed to be called
  Assert(!d_inReclaimZombies)
      << "NodeManager::reclaimZombies() not re-entrant!";

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

#ifdef _LIBCPP_VERSION
  NodeValue* last = NULL;
#endif
  for(vector<NodeValue*>::iterator i = zombies.begin();
      i != zombies.end();
      ++i) {
    NodeValue* nv = *i;
#ifdef _LIBCPP_VERSION
    // Work around an apparent bug in libc++'s hash_set<> which can
    // (very occasionally) have an element repeated.
    if(nv == last) {
      continue;
    }
    last = nv;
#endif

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
      if(mk != kind::metakind::VARIABLE && mk != kind::metakind::NULLARY_OPERATOR) {
        poolRemove(nv);
      }

      // whether exit is normal or exceptional, the NVReclaim dtor is
      // called and ensures that d_nodeUnderDeletion is set back to
      // NULL.
      NVReclaim rc(d_nodeUnderDeletion);
      d_nodeUnderDeletion = nv;

      // remove attributes
      { // notify listeners of deleted node
        TNode n;
        n.d_nv = nv;
        nv->d_rc = 1; // so that TNode doesn't assert-fail
        for (NodeManagerListener* listener : d_listeners)
        {
          listener->nmNotifyDeleteNode(n);
        }
        // this would mean that one of the listeners stowed away
        // a reference to this node!
        Assert(nv->d_rc == 1);
      }
      nv->d_rc = 0;
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

std::vector<NodeValue*> NodeManager::TopologicalSort(
    const std::vector<NodeValue*>& roots) {
  std::vector<NodeValue*> order;
  // The stack of nodes to visit. The Boolean value is false when visiting the
  // node in preorder and true when visiting it in postorder.
  std::vector<std::pair<bool, NodeValue*> > stack;
  // Nodes that have been visited in both pre- and postorder
  NodeValueIDSet visited;
  const NodeValueIDSet root_set(roots.begin(), roots.end());

  for (size_t index = 0; index < roots.size(); index++) {
    NodeValue* root = roots[index];
    if (visited.find(root) == visited.end()) {
      stack.push_back(std::make_pair(false, root));
    }
    while (!stack.empty()) {
      NodeValue* current = stack.back().second;
      const bool visited_children = stack.back().first;
      Debug("gc") << "Topological sort " << current << " " << visited_children
                  << std::endl;
      if (visited_children) {
        if (root_set.find(current) != root_set.end()) {
          order.push_back(current);
        }
        stack.pop_back();
      }
      else if (visited.find(current) == visited.end())
      {
        stack.back().first = true;
        visited.insert(current);
        for (unsigned i = 0; i < current->getNumChildren(); ++i) {
          expr::NodeValue* child = current->getChild(i);
          stack.push_back(std::make_pair(false, child));
        }
      }
      else
      {
        stack.pop_back();
      }
    }
  }
  Assert(order.size() == roots.size());
  return order;
} /* NodeManager::TopologicalSort() */

TypeNode NodeManager::getType(TNode n, bool check)
{
  // Many theories' type checkers call Node::getType() directly.  This
  // is incorrect, since "this" might not be the caller's current node
  // manager.  Rather than force the individual typecheckers not to do
  // this (by policy, which would be imperfect and lead to
  // hard-to-find bugs, which it has in the past), we just set this
  // node manager to be current for the duration of this check.
  //
  NodeManagerScope nms(this);

  TypeNode typeNode;
  bool hasType = getAttribute(n, TypeAttr(), typeNode);
  bool needsCheck = check && !getAttribute(n, TypeCheckedAttr());


  Debug("getType") << this << " getting type for " << &n << " " << n << ", check=" << check << ", needsCheck = " << needsCheck << ", hasType = " << hasType << endl;

#ifdef CVC4_DEBUG
  // already did type check eagerly upon creation in node builder
  bool doTypeCheck = false;
#else
  bool doTypeCheck = true;
#endif
  if (needsCheck && doTypeCheck)
  {
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
        Assert(check || m.getMetaKind() != kind::metakind::NULLARY_OPERATOR);
        /* All the children have types, time to compute */
        typeNode = TypeChecker::computeType(this, m, check);
        worklist.pop();
      }
    } // end while

    /* Last type computed in loop should be the type of n */
    Assert(typeNode == getAttribute(n, TypeAttr()));
  } else if( !hasType || needsCheck ) {
    /* We can compute the type top-down, without worrying about
       deep recursion. */
    Assert(check || n.getMetaKind() != kind::metakind::NULLARY_OPERATOR);
    typeNode = TypeChecker::computeType(this, n, check);
  }

  /* The type should be have been computed and stored. */
  Assert(hasAttribute(n, TypeAttr()));
  /* The check should have happened, if we asked for it. */
  Assert(!check || getAttribute(n, TypeCheckedAttr()));

  Debug("getType") << "type of " << &n << " " <<  n << " is " << typeNode << endl;
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

TypeNode NodeManager::mkSequenceType(TypeNode elementType)
{
  CheckArgument(
      !elementType.isNull(), elementType, "unexpected NULL element type");
  CheckArgument(elementType.isFirstClass(),
                elementType,
                "cannot store types that are not first-class in sequences. Try "
                "option --uf-ho.");
  return mkTypeNode(kind::SEQUENCE_TYPE, elementType);
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
  PrettyCheckArgument(!range.isFunctionLike(), range,
                      "cannot create higher-order function types");
  sorts.push_back(range);
  return mkTypeNode(kind::CONSTRUCTOR_TYPE, sorts);
}

TypeNode NodeManager::mkConstructorType(const std::vector<TypeNode>& args,
                                        TypeNode range)
{
  std::vector<TypeNode> sorts = args;
  sorts.push_back(range);
  return mkTypeNode(kind::CONSTRUCTOR_TYPE, sorts);
}

TypeNode NodeManager::TupleTypeCache::getTupleType( NodeManager * nm, std::vector< TypeNode >& types, unsigned index ) {
  if( index==types.size() ){
    if( d_data.isNull() ){
      std::stringstream sst;
      sst << "__cvc4_tuple";
      for (unsigned i = 0; i < types.size(); ++ i) {
        sst << "_" << types[i];
      }
      Datatype dt(nm->toExprManager(), sst.str());
      dt.setTuple();
      std::stringstream ssc;
      ssc << sst.str() << "_ctor";
      DatatypeConstructor c(ssc.str());
      for (unsigned i = 0; i < types.size(); ++ i) {
        std::stringstream ss;
        ss << sst.str() << "_stor_" << i;
        c.addArg(ss.str().c_str(), types[i].toType());
      }
      dt.addConstructor(c);
      d_data = TypeNode::fromType(nm->toExprManager()->mkDatatypeType(dt));
      Debug("tuprec-debug") << "Return type : " << d_data << std::endl;
    }
    return d_data;
  }else{
    return d_children[types[index]].getTupleType( nm, types, index+1 );
  }
}

TypeNode NodeManager::RecTypeCache::getRecordType( NodeManager * nm, const Record& rec, unsigned index ) {
  if( index==rec.getNumFields() ){
    if( d_data.isNull() ){
      const Record::FieldVector& fields = rec.getFields();
      std::stringstream sst;
      sst << "__cvc4_record";
      for(Record::FieldVector::const_iterator i = fields.begin(); i != fields.end(); ++i) {
        sst << "_" << (*i).first << "_" << (*i).second;
      }
      Datatype dt(nm->toExprManager(), sst.str());
      dt.setRecord();
      std::stringstream ssc;
      ssc << sst.str() << "_ctor";
      DatatypeConstructor c(ssc.str());
      for(Record::FieldVector::const_iterator i = fields.begin(); i != fields.end(); ++i) {
        c.addArg((*i).first, (*i).second);
      }
      dt.addConstructor(c);
      d_data = TypeNode::fromType(nm->toExprManager()->mkDatatypeType(dt));
      Debug("tuprec-debug") << "Return type : " << d_data << std::endl;
    }
    return d_data;
  }else{
    return d_children[TypeNode::fromType( rec[index].second )][rec[index].first].getRecordType( nm, rec, index+1 );
  }
}

TypeNode NodeManager::mkFunctionType(const std::vector<TypeNode>& sorts)
{
  Assert(sorts.size() >= 2);
  CheckArgument(!sorts[sorts.size() - 1].isFunction(),
                sorts[sorts.size() - 1],
                "must flatten function types");
  return mkTypeNode(kind::FUNCTION_TYPE, sorts);
}

TypeNode NodeManager::mkPredicateType(const std::vector<TypeNode>& sorts)
{
  Assert(sorts.size() >= 1);
  std::vector<TypeNode> sortNodes;
  sortNodes.insert(sortNodes.end(), sorts.begin(), sorts.end());
  sortNodes.push_back(booleanType());
  return mkFunctionType(sortNodes);
}

TypeNode NodeManager::mkFunctionType(const TypeNode& domain,
                                     const TypeNode& range)
{
  std::vector<TypeNode> sorts;
  sorts.push_back(domain);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

TypeNode NodeManager::mkFunctionType(const std::vector<TypeNode>& argTypes,
                                     const TypeNode& range)
{
  Assert(argTypes.size() >= 1);
  std::vector<TypeNode> sorts(argTypes);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

TypeNode NodeManager::mkTupleType(const std::vector<TypeNode>& types) {
  std::vector< TypeNode > ts;
  Debug("tuprec-debug") << "Make tuple type : ";
  for (unsigned i = 0; i < types.size(); ++ i) {
    CheckArgument(!types[i].isFunctionLike(), types, "cannot put function-like types in tuples");
    ts.push_back( types[i] );
    Debug("tuprec-debug") << types[i] << " ";
  }
  Debug("tuprec-debug") << std::endl;
  return d_tt_cache.getTupleType( this, ts );
}

TypeNode NodeManager::mkRecordType(const Record& rec) {
  return d_rt_cache.getRecordType( this, rec );
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
  Assert(constructor.getKind() == kind::SORT_TYPE
         && constructor.getNumChildren() == 0)
      << "expected a sort constructor";
  Assert(children.size() > 0) << "expected non-zero # of children";
  Assert(hasAttribute(constructor.d_nv, expr::SortArityAttr())
         && hasAttribute(constructor.d_nv, expr::VarNameAttr()))
      << "expected a sort constructor";
  std::string name = getAttribute(constructor.d_nv, expr::VarNameAttr());
  Assert(getAttribute(constructor.d_nv, expr::SortArityAttr())
         == children.size())
      << "arity mismatch in application of sort constructor";
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
                                        size_t arity,
                                        uint32_t flags)
{
  Assert(arity > 0);
  NodeBuilder<> nb(this, kind::SORT_TYPE);
  Node sortTag = NodeBuilder<0>(this, kind::SORT_TAG);
  nb << sortTag;
  TypeNode type = nb.constructTypeNode();
  setAttribute(type, expr::VarNameAttr(), name);
  setAttribute(type, expr::SortArityAttr(), arity);
  for(std::vector<NodeManagerListener*>::iterator i = d_listeners.begin(); i != d_listeners.end(); ++i) {
    (*i)->nmNotifyNewSortConstructor(type, flags);
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

Node NodeManager::getBoundVarListForFunctionType( TypeNode tn ) {
  Assert(tn.isFunction());
  Node bvl = tn.getAttribute(LambdaBoundVarListAttr());
  if( bvl.isNull() ){
    std::vector< Node > vars;
    for( unsigned i=0; i<tn.getNumChildren()-1; i++ ){
      vars.push_back(mkBoundVar(tn[i]));
    }
    bvl = mkNode(kind::BOUND_VAR_LIST, vars);
    Trace("functions") << "Make standard bound var list " << bvl << " for " << tn << std::endl;
    tn.setAttribute(LambdaBoundVarListAttr(),bvl);
  }
  return bvl;
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

Node NodeManager::mkBooleanTermVariable() {
  Node n = NodeBuilder<0>(this, kind::BOOLEAN_TERM_VARIABLE);
  n.setAttribute(TypeAttr(), booleanType());
  n.setAttribute(TypeCheckedAttr(), true);
  return n;
}

Node NodeManager::mkNullaryOperator(const TypeNode& type, Kind k) {
  std::map< TypeNode, Node >::iterator it = d_unique_vars[k].find( type );
  if( it==d_unique_vars[k].end() ){
    Node n = NodeBuilder<0>(this, k).constructNode();
    setAttribute(n, TypeAttr(), type);
    //setAttribute(n, TypeCheckedAttr(), true);
    d_unique_vars[k][type] = n;
    Assert(n.getMetaKind() == kind::metakind::NULLARY_OPERATOR);
    return n;
  }else{
    return it->second;
  }
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

Kind NodeManager::getKindForFunction(TNode fun)
{
  TypeNode tn = fun.getType();
  if (tn.isFunction())
  {
    return kind::APPLY_UF;
  }
  else if (tn.isConstructor())
  {
    return kind::APPLY_CONSTRUCTOR;
  }
  else if (tn.isSelector())
  {
    return kind::APPLY_SELECTOR;
  }
  else if (tn.isTester())
  {
    return kind::APPLY_TESTER;
  }
  return kind::UNDEFINED_KIND;
}

}/* CVC4 namespace */
