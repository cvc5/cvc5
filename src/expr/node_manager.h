/*********************                                                        */
/*! \file node_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A manager for Nodes
 **
 ** A manager for Nodes.
 **
 ** Reviewed by Chris Conway, Apr 5 2010 (bug #65).
 **/

#include "cvc4_private.h"

/* circular dependency; force node.h first */
//#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"

#ifndef __CVC4__NODE_MANAGER_H
#define __CVC4__NODE_MANAGER_H

#include <vector>
#include <string>
#include <ext/hash_set>

#include "base/tls.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_value.h"
#include "util/subrange_bound.h"
#include "options/options.h"

namespace CVC4 {

class StatisticsRegistry;
class ResourceManager;

namespace expr {
  namespace attr {
    class AttributeUniqueId;
    class AttributeManager;
  }/* CVC4::expr::attr namespace */

  class TypeChecker;
}/* CVC4::expr namespace */

/**
 * An interface that an interested party can implement and then subscribe
 * to NodeManager events via NodeManager::subscribeEvents(this).
 */
class NodeManagerListener {
 public:
  virtual ~NodeManagerListener() {}
  virtual void nmNotifyNewSort(TypeNode tn, uint32_t flags) {}
  virtual void nmNotifyNewSortConstructor(TypeNode tn) {}
  virtual void nmNotifyInstantiateSortConstructor(TypeNode ctor, TypeNode sort,
                                                  uint32_t flags) {}
  virtual void nmNotifyNewDatatypes(
      const std::vector<DatatypeType>& datatypes) {}
  virtual void nmNotifyNewVar(TNode n, uint32_t flags) {}
  virtual void nmNotifyNewSkolem(TNode n, const std::string& comment,
                                 uint32_t flags) {}
  /**
   * Notify a listener of a Node that's being GCed.  If this function stores a
   * reference
   * to the Node somewhere, very bad things will happen.
   */
  virtual void nmNotifyDeleteNode(TNode n) {}
}; /* class NodeManagerListener */

class NodeManager {
  template <unsigned nchild_thresh> friend class CVC4::NodeBuilder;
  friend class NodeManagerScope;
  friend class expr::NodeValue;
  friend class expr::TypeChecker;

  // friends so they can access mkVar() here, which is private
  friend Expr ExprManager::mkVar(const std::string&, Type, uint32_t flags);
  friend Expr ExprManager::mkVar(Type, uint32_t flags);

  // friend so it can access NodeManager's d_listeners and notify clients
  friend std::vector<DatatypeType> ExprManager::mkMutualDatatypeTypes(std::vector<Datatype>&, std::set<Type>&);

  /** Predicate for use with STL algorithms */
  struct NodeValueReferenceCountNonZero {
    bool operator()(expr::NodeValue* nv) { return nv->d_rc > 0; }
  };

  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValuePoolHashFunction,
                              expr::NodeValuePoolEq> NodeValuePool;
  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueIDHashFunction,
                              expr::NodeValueIDEquality> NodeValueIDSet;

  static CVC4_THREADLOCAL(NodeManager*) s_current;

  Options* d_options;
  StatisticsRegistry* d_statisticsRegistry;

  ResourceManager* d_resourceManager;

  /**
   * A list of registrations on d_options to that call into d_resourceManager.
   * These must be garbage collected before d_options and d_resourceManager.
   */
  ListenerRegistrationList* d_registrations;

  NodeValuePool d_nodeValuePool;

  size_t next_id;

  expr::attr::AttributeManager* d_attrManager;

  /** The associated ExprManager */
  ExprManager* d_exprManager;

  /**
   * The node value we're currently freeing.  This unique node value
   * is permitted to have outstanding TNodes to it (in "soft"
   * contexts, like as a key in attribute tables), even though
   * normally it's an error to have a TNode to a node value with a
   * reference count of 0.  Being "under deletion" also enables
   * assertions that inc() is not called on it.  (A poorly-behaving
   * attribute cleanup function could otherwise create a "Node" that
   * points to the node value that is in the process of being deleted,
   * springing it back to life.)
   */
  expr::NodeValue* d_nodeUnderDeletion;

  /**
   * True iff we are in reclaimZombies().  This avoids unnecessary
   * recursion; a NodeValue being deleted might zombify other
   * NodeValues, but these shouldn't trigger a (recursive) call to
   * reclaimZombies().
   */
  bool d_inReclaimZombies;

  /**
   * The set of zombie nodes.  We may want to revisit this design, as
   * we might like to delete nodes in least-recently-used order.  But
   * we also need to avoid processing a zombie twice.
   */
  NodeValueIDSet d_zombies;

  /**
   * NodeValues with maxed out reference counts. These live as long as the
   * NodeManager. They have a custom deallocation procedure at the very end.
   */
  std::vector<expr::NodeValue*> d_maxedOut;

  /**
   * A set of operator singletons (w.r.t.  to this NodeManager
   * instance) for operators.  Conceptually, Nodes with kind, say,
   * PLUS, are APPLYs of a PLUS operator to arguments.  This array
   * holds the set of operators for these things.  A PLUS operator is
   * a Node with kind "BUILTIN", and if you call
   * plusOperator->getConst<CVC4::Kind>(), you get kind::PLUS back.
   */
  Node d_operators[kind::LAST_KIND];

  /** unique vars per (Kind,Type) */
  std::map< Kind, std::map< TypeNode, Node > > d_unique_vars;

  /**
   * A list of subscribers for NodeManager events.
   */
  std::vector<NodeManagerListener*> d_listeners;

  /** A list of datatypes owned by this node manager. */
  std::vector<Datatype*> d_ownedDatatypes;

  /**
   * A map of tuple and record types to their corresponding datatype.
   */
  class TupleTypeCache {
  public:
    std::map< TypeNode, TupleTypeCache > d_children;
    TypeNode d_data;
    TypeNode getTupleType( NodeManager * nm, std::vector< TypeNode >& types, unsigned index = 0 );
  };
  class RecTypeCache {
  public:
    std::map< TypeNode, std::map< std::string, RecTypeCache > > d_children;
    TypeNode d_data;
    TypeNode getRecordType( NodeManager * nm, const Record& rec, unsigned index = 0 );
  };
  TupleTypeCache d_tt_cache;
  RecTypeCache d_rt_cache;

  /**
   * Keep a count of all abstract values produced by this NodeManager.
   * Abstract values have a type attribute, so if multiple SmtEngines
   * are attached to this NodeManager, we don't want their abstract
   * values to overlap.
   */
  unsigned d_abstractValueCount;

  /**
   * A counter used to produce unique skolem names.
   *
   * Note that it is NOT incremented when skolems are created using
   * SKOLEM_EXACT_NAME, so it is NOT a count of the skolems produced
   * by this node manager.
   */
  unsigned d_skolemCounter;

  /**
   * Look up a NodeValue in the pool associated to this NodeManager.
   * The NodeValue argument need not be a "completely-constructed"
   * NodeValue.  In particular, "non-inlined" constants are permitted
   * (see below).
   *
   * For non-CONSTANT metakinds, nv's d_kind and d_nchildren should be
   * correctly set, and d_children[0..n-1] should be valid (extant)
   * NodeValues for lookup.
   *
   * For CONSTANT metakinds, nv's d_kind should be set correctly.
   * Normally a CONSTANT would have d_nchildren == 0 and the constant
   * value inlined in the d_children space.  However, here we permit
   * "non-inlined" NodeValues to avoid unnecessary copying.  For
   * these, d_nchildren == 1, and d_nchildren is a pointer to the
   * constant value.
   *
   * The point of this complex design is to permit efficient lookups
   * (without fully constructing a NodeValue).  In the case that the
   * argument is not fully constructed, and this function returns
   * NULL, the caller should fully construct an equivalent one before
   * calling poolInsert().  NON-FULLY-CONSTRUCTED NODEVALUES are not
   * permitted in the pool!
   */
  inline expr::NodeValue* poolLookup(expr::NodeValue* nv) const;

  /**
   * Insert a NodeValue into the NodeManager's pool.
   *
   * It is an error to insert a NodeValue already in the pool.
   * Enquire first with poolLookup().
   */
  inline void poolInsert(expr::NodeValue* nv);

  /**
   * Remove a NodeValue from the NodeManager's pool.
   *
   * It is an error to request the removal of a NodeValue from the
   * pool that is not in the pool.
   */
  inline void poolRemove(expr::NodeValue* nv);

  /**
   * Determine if nv is currently being deleted by the NodeManager.
   */
  inline bool isCurrentlyDeleting(const expr::NodeValue* nv) const {
    return d_nodeUnderDeletion == nv;
  }

  /**
   * Register a NodeValue as a zombie.
   */
  inline void markForDeletion(expr::NodeValue* nv) {
    Assert(nv->d_rc == 0);

    // if d_reclaiming is set, make sure we don't call
    // reclaimZombies(), because it's already running.
    if(Debug.isOn("gc")) {
      Debug("gc") << "zombifying node value " << nv
                  << " [" << nv->d_id << "]: ";
      nv->printAst(Debug("gc"));
      Debug("gc") << (d_inReclaimZombies ? " [CURRENTLY-RECLAIMING]" : "")
                  << std::endl;
    }
    d_zombies.insert(nv);  // FIXME multithreading

    if(safeToReclaimZombies()) {
      if(d_zombies.size() > 5000) {
        reclaimZombies();
      }
    }
  }

  /**
   * Register a NodeValue as having a maxed out reference count. This NodeValue
   * will live as long as its containing NodeManager.
   */
  inline void markRefCountMaxedOut(expr::NodeValue* nv) {
    Assert(nv->HasMaximizedReferenceCount());
    if(Debug.isOn("gc")) {
      Debug("gc") << "marking node value " << nv
                  << " [" << nv->d_id << "]: as maxed out" << std::endl;
    }
    d_maxedOut.push_back(nv);
  }

  /**
   * Reclaim all zombies.
   */
  void reclaimZombies();

  /**
   * It is safe to collect zombies.
   */
  bool safeToReclaimZombies() const;

  /**
   * Returns a reverse topological sort of a list of NodeValues. The NodeValues
   * must be valid and have ids. The NodeValues are not modified (including ref
   * counts).
   */
  static std::vector<expr::NodeValue*> TopologicalSort(
      const std::vector<expr::NodeValue*>& roots);

  /**
   * This template gives a mechanism to stack-allocate a NodeValue
   * with enough space for N children (where N is a compile-time
   * constant).  You use it like this:
   *
   *   NVStorage<4> nvStorage;
   *   NodeValue& nvStack = reinterpret_cast<NodeValue&>(nvStorage);
   *
   * ...and then you can use nvStack as a NodeValue that you know has
   * room for 4 children.
   */
  template <size_t N>
  struct NVStorage {
    expr::NodeValue nv;
    expr::NodeValue* child[N];
  };/* struct NodeManager::NVStorage<N> */

  /* A note on isAtomic() and isAtomicFormula() (in CVC3 parlance)..
   *
   * It has been decided for now to hold off on implementations of
   * these functions, as they may only be needed in CNF conversion,
   * where it's pointless to do a lazy isAtomic determination by
   * searching through the DAG, and storing it, since the result will
   * only be used once.  For more details see the 4/27/2010 CVC4
   * developer's meeting notes at:
   *
   * http://goedel.cims.nyu.edu/wiki/Meeting_Minutes_-_April_27,_2010#isAtomic.28.29_and_isAtomicFormula.28.29
   */
  // bool containsDecision(TNode); // is "atomic"
  // bool properlyContainsDecision(TNode); // all children are atomic

  // undefined private copy constructor (disallow copy)
  NodeManager(const NodeManager&) CVC4_UNDEFINED;

  NodeManager& operator=(const NodeManager&) CVC4_UNDEFINED;

  void init();

  /**
   * Create a variable with the given name and type.  NOTE that no
   * lookup is done on the name.  If you mkVar("a", type) and then
   * mkVar("a", type) again, you have two variables.  The NodeManager
   * version of this is private to avoid internal uses of mkVar() from
   * within CVC4.  Such uses should employ mkSkolem() instead.
   */
  Node mkVar(const std::string& name, const TypeNode& type, uint32_t flags = ExprManager::VAR_FLAG_NONE);
  Node* mkVarPtr(const std::string& name, const TypeNode& type, uint32_t flags = ExprManager::VAR_FLAG_NONE);

  /** Create a variable with the given type. */
  Node mkVar(const TypeNode& type, uint32_t flags = ExprManager::VAR_FLAG_NONE);
  Node* mkVarPtr(const TypeNode& type, uint32_t flags = ExprManager::VAR_FLAG_NONE);
  
public:

  explicit NodeManager(ExprManager* exprManager);
  explicit NodeManager(ExprManager* exprManager, const Options& options);
  ~NodeManager();

  /** The node manager in the current public-facing CVC4 library context */
  static NodeManager* currentNM() { return s_current; }
  /** The resource manager associated with the current node manager */
  static ResourceManager* currentResourceManager() { return s_current->d_resourceManager; }

  /** Get this node manager's options (const version) */
  const Options& getOptions() const {
    return *d_options;
  }

  /** Get this node manager's options (non-const version) */
  Options& getOptions() {
    return *d_options;
  }

  /** Get this node manager's resource manager */
  ResourceManager* getResourceManager() throw() { return d_resourceManager; }

  /** Get this node manager's statistics registry */
  StatisticsRegistry* getStatisticsRegistry() const throw() {
    return d_statisticsRegistry;
  }

  /** Subscribe to NodeManager events */
  void subscribeEvents(NodeManagerListener* listener) {
    Assert(std::find(d_listeners.begin(), d_listeners.end(), listener) == d_listeners.end(), "listener already subscribed");
    d_listeners.push_back(listener);
  }

  /** Unsubscribe from NodeManager events */
  void unsubscribeEvents(NodeManagerListener* listener) {
    std::vector<NodeManagerListener*>::iterator elt = std::find(d_listeners.begin(), d_listeners.end(), listener);
    Assert(elt != d_listeners.end(), "listener not subscribed");
    d_listeners.erase(elt);
  }
  
  /** register datatype */
  unsigned registerDatatype(Datatype* dt);
  /** get datatype for index */
  const Datatype & getDatatypeForIndex( unsigned index ) const;

  /** Get a Kind from an operator expression */
  static inline Kind operatorToKind(TNode n);

  // general expression-builders

  /** Create a node with one child. */
  Node mkNode(Kind kind, TNode child1);
  Node* mkNodePtr(Kind kind, TNode child1);

  /** Create a node with two children. */
  Node mkNode(Kind kind, TNode child1, TNode child2);
  Node* mkNodePtr(Kind kind, TNode child1, TNode child2);

  /** Create a node with three children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3);
  Node* mkNodePtr(Kind kind, TNode child1, TNode child2, TNode child3);

  /** Create a node with four children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4);
  Node* mkNodePtr(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4);

  /** Create a node with five children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4, TNode child5);
  Node* mkNodePtr(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4, TNode child5);

  /** Create a node with an arbitrary number of children. */
  template <bool ref_count>
  Node mkNode(Kind kind, const std::vector<NodeTemplate<ref_count> >& children);
  template <bool ref_count>
  Node* mkNodePtr(Kind kind, const std::vector<NodeTemplate<ref_count> >& children);

  /** Create a node (with no children) by operator. */
  Node mkNode(TNode opNode);
  Node* mkNodePtr(TNode opNode);

  /** Create a node with one child by operator. */
  Node mkNode(TNode opNode, TNode child1);
  Node* mkNodePtr(TNode opNode, TNode child1);

  /** Create a node with two children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2);
  Node* mkNodePtr(TNode opNode, TNode child1, TNode child2);

  /** Create a node with three children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2, TNode child3);
  Node* mkNodePtr(TNode opNode, TNode child1, TNode child2, TNode child3);

  /** Create a node with four children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2, TNode child3,
              TNode child4);
  Node* mkNodePtr(TNode opNode, TNode child1, TNode child2, TNode child3,
              TNode child4);

  /** Create a node with five children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2, TNode child3,
              TNode child4, TNode child5);
  Node* mkNodePtr(TNode opNode, TNode child1, TNode child2, TNode child3,
              TNode child4, TNode child5);

  /** Create a node by applying an operator to the children. */
  template <bool ref_count>
  Node mkNode(TNode opNode, const std::vector<NodeTemplate<ref_count> >& children);
  template <bool ref_count>
  Node* mkNodePtr(TNode opNode, const std::vector<NodeTemplate<ref_count> >& children);

  Node mkBoundVar(const std::string& name, const TypeNode& type);
  Node* mkBoundVarPtr(const std::string& name, const TypeNode& type);

  Node mkBoundVar(const TypeNode& type);
  Node* mkBoundVarPtr(const TypeNode& type);

  /**
   * Optional flags used to control behavior of NodeManager::mkSkolem().
   * They should be composed with a bitwise OR (e.g.,
   * "SKOLEM_NO_NOTIFY | SKOLEM_EXACT_NAME").  Of course, SKOLEM_DEFAULT
   * cannot be composed in such a manner.
   */
  enum SkolemFlags {
    SKOLEM_DEFAULT = 0,   /**< default behavior */
    SKOLEM_NO_NOTIFY = 1, /**< do not notify subscribers */
    SKOLEM_EXACT_NAME = 2,/**< do not make the name unique by adding the id */
    SKOLEM_IS_GLOBAL = 4  /**< global vars appear in models even after a pop */
  };/* enum SkolemFlags */

  /**
   * Create a skolem constant with the given name, type, and comment.
   *
   * @param prefix the name of the new skolem variable is the prefix
   * appended with a unique ID.  This way a family of skolem variables
   * can be made with unique identifiers, used in dump, tracing, and
   * debugging output.  Use SKOLEM_EXECT_NAME flag if you don't want
   * a unique ID appended and use prefix as the name.
   *
   * @param type the type of the skolem variable to create
   *
   * @param comment a comment for dumping output; if declarations are
   * being dumped, this is included in a comment before the declaration
   * and can be quite useful for debugging
   *
   * @param flags an optional mask of bits from SkolemFlags to control
   * mkSkolem() behavior
   */
  Node mkSkolem(const std::string& prefix, const TypeNode& type,
                const std::string& comment = "", int flags = SKOLEM_DEFAULT);

  /** Create a instantiation constant with the given type. */
  Node mkInstConstant(const TypeNode& type);
  
  /** Create a boolean term variable. */
  Node mkBooleanTermVariable();

  /** Make a new abstract value with the given type. */
  Node mkAbstractValue(const TypeNode& type);
  
  /** make unique (per Type,Kind) variable. */
  Node mkUniqueVar(const TypeNode& type, Kind k);

  /**
   * Create a constant of type T.  It will have the appropriate
   * CONST_* kind defined for T.
   */
  template <class T>
  Node mkConst(const T&);

  template <class T>
  TypeNode mkTypeConst(const T&);

  template <class NodeClass, class T>
  NodeClass mkConstInternal(const T&);

  /** Create a node with children. */
  TypeNode mkTypeNode(Kind kind, TypeNode child1);
  TypeNode mkTypeNode(Kind kind, TypeNode child1, TypeNode child2);
  TypeNode mkTypeNode(Kind kind, TypeNode child1, TypeNode child2,
                      TypeNode child3);
  TypeNode mkTypeNode(Kind kind, const std::vector<TypeNode>& children);

  /**
   * Determine whether Nodes of a particular Kind have operators.
   * @returns true if Nodes of Kind k have operators.
   */
  static inline bool hasOperator(Kind k);

  /**
   * Get the (singleton) operator of an OPERATOR-kinded kind.  The
   * returned node n will have kind BUILTIN, and calling
   * n.getConst<CVC4::Kind>() will yield k.
   */
  inline TNode operatorOf(Kind k) {
    AssertArgument( kind::metaKindOf(k) == kind::metakind::OPERATOR, k,
                    "Kind is not an OPERATOR-kinded kind "
                    "in NodeManager::operatorOf()" );
    return d_operators[k];
  }

  /**
   * Retrieve an attribute for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(expr::NodeValue* nv,
                                                    const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for
   * <code>nv</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(expr::NodeValue* nv,
                           const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a node, and, if so,
   * retrieve it.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default
   * value of the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for
   * <code>nv</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(expr::NodeValue* nv,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /**
   * Set an attribute for a node.  If the node doesn't have the
   * attribute, this function assigns one.  If the node has one, this
   * overwrites it.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to set
   * @param value the value of <code>attr</code> for <code>nv</code>
   */
  template <class AttrKind>
  inline void setAttribute(expr::NodeValue* nv,
                           const AttrKind& attr,
                           const typename AttrKind::value_type& value);

  /**
   * Retrieve an attribute for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type
  getAttribute(TNode n, const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(TNode n,
                           const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TNode and, if so, retieve
   * it.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default value of
   * the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(TNode n,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /**
   * Set an attribute for a node.  If the node doesn't have the
   * attribute, this function assigns one.  If the node has one, this
   * overwrites it.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to set
   * @param value the value of <code>attr</code> for <code>n</code>
   */
  template <class AttrKind>
  inline void setAttribute(TNode n,
                           const AttrKind& attr,
                           const typename AttrKind::value_type& value);

  /**
   * Retrieve an attribute for a TypeNode.
   *
   * @param n the type node
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type
  getAttribute(TypeNode n, const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TypeNode.
   *
   * @param n the type node
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(TypeNode n,
                           const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TypeNode and, if so, retieve
   * it.
   *
   * @param n the type node
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default value of
   * the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(TypeNode n,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /**
   * Set an attribute for a type node.  If the node doesn't have the
   * attribute, this function assigns one.  If the type node has one,
   * this overwrites it.
   *
   * @param n the type node
   * @param attr an instance of the attribute kind to set
   * @param value the value of <code>attr</code> for <code>n</code>
   */
  template <class AttrKind>
  inline void setAttribute(TypeNode n,
                           const AttrKind& attr,
                           const typename AttrKind::value_type& value);

  /** Get the (singleton) type for Booleans. */
  inline TypeNode booleanType();

  /** Get the (singleton) type for integers. */
  inline TypeNode integerType();

  /** Get the (singleton) type for reals. */
  inline TypeNode realType();

  /** Get the (singleton) type for strings. */
  inline TypeNode stringType();

  /** Get the (singleton) type for RegExp. */
  inline TypeNode regExpType();

  /** Get the (singleton) type for rounding modes. */
  inline TypeNode roundingModeType();

  /** Get the bound var list type. */
  inline TypeNode boundVarListType();

  /** Get the instantiation pattern type. */
  inline TypeNode instPatternType();

  /** Get the instantiation pattern type. */
  inline TypeNode instPatternListType();

  /**
   * Get the (singleton) type for builtin operators (that is, the type
   * of the Node returned from Node::getOperator() when the operator
   * is built-in, like EQUAL). */
  inline TypeNode builtinOperatorType();

  /**
   * Make a function type from domain to range.
   *
   * @param domain the domain type
   * @param range the range type
   * @returns the functional type domain -> range
   */
  inline TypeNode mkFunctionType(const TypeNode& domain, const TypeNode& range);

  /**
   * Make a function type with input types from
   * argTypes. <code>argTypes</code> must have at least one element.
   *
   * @param argTypes the domain is a tuple (argTypes[0], ..., argTypes[n])
   * @param range the range type
   * @returns the functional type (argTypes[0], ..., argTypes[n]) -> range
   */
  inline TypeNode mkFunctionType(const std::vector<TypeNode>& argTypes,
                                 const TypeNode& range);

  /**
   * Make a function type with input types from
   * <code>sorts[0..sorts.size()-2]</code> and result type
   * <code>sorts[sorts.size()-1]</code>. <code>sorts</code> must have
   * at least 2 elements.
   */
  inline TypeNode mkFunctionType(const std::vector<TypeNode>& sorts);

  /**
   * Make a predicate type with input types from
   * <code>sorts</code>. The result with be a function type with range
   * <code>BOOLEAN</code>. <code>sorts</code> must have at least one
   * element.
   */
  inline TypeNode mkPredicateType(const std::vector<TypeNode>& sorts);

  /**
   * Make a tuple type with types from
   * <code>types</code>. <code>types</code> must have at least one
   * element.
   *
   * @param types a vector of types
   * @returns the tuple type (types[0], ..., types[n])
   */
  TypeNode mkTupleType(const std::vector<TypeNode>& types);

  /**
   * Make a record type with the description from rec.
   *
   * @param rec a description of the record
   * @returns the record type
   */
  TypeNode mkRecordType(const Record& rec);

  /**
   * Make a symbolic expression type with types from
   * <code>types</code>. <code>types</code> may have any number of
   * elements.
   *
   * @param types a vector of types
   * @returns the symbolic expression type (types[0], ..., types[n])
   */
  inline TypeNode mkSExprType(const std::vector<TypeNode>& types);

  /** Make the type of floating-point with <code>exp</code> bit exponent and
      <code>sig</code> bit significand */
  inline TypeNode mkFloatingPointType(unsigned exp, unsigned sig);  
  inline TypeNode mkFloatingPointType(FloatingPointSize fs);

  /** Make the type of bitvectors of size <code>size</code> */
  inline TypeNode mkBitVectorType(unsigned size);

  /** Make the type of arrays with the given parameterization */
  inline TypeNode mkArrayType(TypeNode indexType, TypeNode constituentType);

  /** Make the type of arrays with the given parameterization */
  inline TypeNode mkSetType(TypeNode elementType);

  /** Make a type representing a constructor with the given parameterization */
  TypeNode mkConstructorType(const DatatypeConstructor& constructor, TypeNode range);

  /** Make a type representing a selector with the given parameterization */
  inline TypeNode mkSelectorType(TypeNode domain, TypeNode range);

  /** Make a type representing a tester with given parameterization */
  inline TypeNode mkTesterType(TypeNode domain);

  /** Make a new (anonymous) sort of arity 0. */
  TypeNode mkSort(uint32_t flags = ExprManager::SORT_FLAG_NONE);

  /** Make a new sort with the given name of arity 0. */
  TypeNode mkSort(const std::string& name, uint32_t flags = ExprManager::SORT_FLAG_NONE);

  /** Make a new sort by parameterizing the given sort constructor. */
  TypeNode mkSort(TypeNode constructor,
                  const std::vector<TypeNode>& children,
                  uint32_t flags = ExprManager::SORT_FLAG_NONE);

  /** Make a new sort with the given name and arity. */
  TypeNode mkSortConstructor(const std::string& name, size_t arity);

  /**
   * Make a predicate subtype type defined by the given LAMBDA
   * expression.  A TypeCheckingExceptionPrivate can be thrown if
   * lambda is not a LAMBDA, or is ill-typed, or if CVC4 fails at
   * proving that the resulting predicate subtype is inhabited.
   */
  TypeNode mkPredicateSubtype(Expr lambda)
    throw(TypeCheckingExceptionPrivate);

  /**
   * Make a predicate subtype type defined by the given LAMBDA
   * expression and whose non-emptiness is witnessed by the given
   * witness.  A TypeCheckingExceptionPrivate can be thrown if lambda
   * is not a LAMBDA, or is ill-typed, or if the witness is not a
   * witness or ill-typed.
   */
  TypeNode mkPredicateSubtype(Expr lambda, Expr witness)
    throw(TypeCheckingExceptionPrivate);

  /**
   * Make an integer subrange type as defined by the argument.
   */
  TypeNode mkSubrangeType(const SubrangeBounds& bounds)
    throw(TypeCheckingExceptionPrivate);

  /**
   * Get the type for the given node and optionally do type checking.
   *
   * Initial type computation will be near-constant time if
   * type checking is not requested. Results are memoized, so that
   * subsequent calls to getType() without type checking will be
   * constant time.
   *
   * Initial type checking is linear in the size of the expression.
   * Again, the results are memoized, so that subsequent calls to
   * getType(), with or without type checking, will be constant
   * time.
   *
   * NOTE: A TypeCheckingException can be thrown even when type
   * checking is not requested. getType() will always return a
   * valid and correct type and, thus, an exception will be thrown
   * when no valid or correct type can be computed (e.g., if the
   * arguments to a bit-vector operation aren't bit-vectors). When
   * type checking is not requested, getType() will do the minimum
   * amount of checking required to return a valid result.
   *
   * @param n the Node for which we want a type
   * @param check whether we should check the type as we compute it
   * (default: false)
   */
  TypeNode getType(TNode n, bool check = false)
    throw(TypeCheckingExceptionPrivate, AssertionException);

  /**
   * Convert a node to an expression.  Uses the ExprManager
   * associated to this NodeManager.
   */
  inline Expr toExpr(TNode n);

  /**
   * Convert an expression to a node.
   */
  static inline Node fromExpr(const Expr& e);

  /**
   * Convert a node manager to an expression manager.
   */
  inline ExprManager* toExprManager();

  /**
   * Convert an expression manager to a node manager.
   */
  static inline NodeManager* fromExprManager(ExprManager* exprManager);

  /**
   * Convert a type node to a type.
   */
  inline Type toType(TypeNode tn);

  /**
   * Convert a type to a type node.
   */
  static inline TypeNode fromType(Type t);

  /** Reclaim zombies while there are more than k nodes in the pool (if possible).*/
  void reclaimZombiesUntil(uint32_t k);

  /** Reclaims all zombies (if possible).*/
  void reclaimAllZombies();

  /** Size of the node pool. */
  size_t poolSize() const;

  /** Deletes a list of attributes from the NM's AttributeManager.*/
  void deleteAttributes(const std::vector< const expr::attr::AttributeUniqueId* >& ids);

  /**
   * This function gives developers a hook into the NodeManager.
   * This can be changed in node_manager.cpp without recompiling most of cvc4.
   *
   * debugHook is a debugging only function, and should not be present in
   * any published code!
   */
  void debugHook(int debugFlag);
};/* class NodeManager */

/**
 * This class changes the "current" thread-global
 * <code>NodeManager</code> when it is created and reinstates the
 * previous thread-global <code>NodeManager</code> when it is
 * destroyed, effectively maintaining a set of nested
 * <code>NodeManager</code> scopes.  This is especially useful on
 * public-interface calls into the CVC4 library, where CVC4's notion
 * of the "current" <code>NodeManager</code> should be set to match
 * the calling context.  See, for example, the implementations of
 * public calls in the <code>ExprManager</code> and
 * <code>SmtEngine</code> classes.
 *
 * The client must be careful to create and destroy
 * <code>NodeManagerScope</code> objects in a well-nested manner (such
 * as on the stack). You may create a <code>NodeManagerScope</code>
 * with <code>new</code> and destroy it with <code>delete</code>, or
 * place it as a data member of an object that is, but if the scope of
 * these <code>new</code>/<code>delete</code> pairs isn't properly
 * maintained, the incorrect "current" <code>NodeManager</code>
 * pointer may be restored after a delete.
 */
class NodeManagerScope {
  /** The old NodeManager, to be restored on destruction. */
  NodeManager* d_oldNodeManager;
  Options::OptionsScope d_optionsScope;
public:

  NodeManagerScope(NodeManager* nm)
      : d_oldNodeManager(NodeManager::s_current)
      , d_optionsScope(nm ? nm->d_options : NULL) {
    // There are corner cases where nm can be NULL and it's ok.
    // For example, if you write { Expr e; }, then when the null
    // Expr is destructed, there's no active node manager.
    //Assert(nm != NULL);
    NodeManager::s_current = nm;
    //Options::s_current = nm ? nm->d_options : NULL;
    Debug("current") << "node manager scope: "
                     << NodeManager::s_current << "\n";
  }

  ~NodeManagerScope() {
    NodeManager::s_current = d_oldNodeManager;
    //Options::s_current = d_oldNodeManager ? d_oldNodeManager->d_options : NULL;
    Debug("current") << "node manager scope: "
                     << "returning to " << NodeManager::s_current << "\n";
  }
};/* class NodeManagerScope */

/** Get the (singleton) type for booleans. */
inline TypeNode NodeManager::booleanType() {
  return TypeNode(mkTypeConst<TypeConstant>(BOOLEAN_TYPE));
}

/** Get the (singleton) type for integers. */
inline TypeNode NodeManager::integerType() {
  return TypeNode(mkTypeConst<TypeConstant>(INTEGER_TYPE));
}

/** Get the (singleton) type for reals. */
inline TypeNode NodeManager::realType() {
  return TypeNode(mkTypeConst<TypeConstant>(REAL_TYPE));
}

/** Get the (singleton) type for strings. */
inline TypeNode NodeManager::stringType() {
  return TypeNode(mkTypeConst<TypeConstant>(STRING_TYPE));
}

/** Get the (singleton) type for regexps. */
inline TypeNode NodeManager::regExpType() {
  return TypeNode(mkTypeConst<TypeConstant>(REGEXP_TYPE));
}

/** Get the (singleton) type for rounding modes. */
inline TypeNode NodeManager::roundingModeType() {
  return TypeNode(mkTypeConst<TypeConstant>(ROUNDINGMODE_TYPE));
}

/** Get the bound var list type. */
inline TypeNode NodeManager::boundVarListType() {
  return TypeNode(mkTypeConst<TypeConstant>(BOUND_VAR_LIST_TYPE));
}

/** Get the instantiation pattern type. */
inline TypeNode NodeManager::instPatternType() {
  return TypeNode(mkTypeConst<TypeConstant>(INST_PATTERN_TYPE));
}

/** Get the instantiation pattern type. */
inline TypeNode NodeManager::instPatternListType() {
  return TypeNode(mkTypeConst<TypeConstant>(INST_PATTERN_LIST_TYPE));
}

/** Get the (singleton) type for builtin operators. */
inline TypeNode NodeManager::builtinOperatorType() {
  return TypeNode(mkTypeConst<TypeConstant>(BUILTIN_OPERATOR_TYPE));
}

/** Make a function type from domain to range. */
inline TypeNode NodeManager::mkFunctionType(const TypeNode& domain, const TypeNode& range) {
  std::vector<TypeNode> sorts;
  sorts.push_back(domain);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

inline TypeNode NodeManager::mkFunctionType(const std::vector<TypeNode>& argTypes, const TypeNode& range) {
  Assert(argTypes.size() >= 1);
  std::vector<TypeNode> sorts(argTypes);
  sorts.push_back(range);
  return mkFunctionType(sorts);
}

inline TypeNode
NodeManager::mkFunctionType(const std::vector<TypeNode>& sorts) {
  Assert(sorts.size() >= 2);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0; i < sorts.size(); ++ i) {
    CheckArgument(!sorts[i].isFunctionLike(), sorts,
                  "cannot create higher-order function types");
    sortNodes.push_back(sorts[i]);
  }
  return mkTypeNode(kind::FUNCTION_TYPE, sortNodes);
}

inline TypeNode
NodeManager::mkPredicateType(const std::vector<TypeNode>& sorts) {
  Assert(sorts.size() >= 1);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0; i < sorts.size(); ++ i) {
    CheckArgument(!sorts[i].isFunctionLike(), sorts,
                  "cannot create higher-order function types");
    sortNodes.push_back(sorts[i]);
  }
  sortNodes.push_back(booleanType());
  return mkTypeNode(kind::FUNCTION_TYPE, sortNodes);
}

inline TypeNode NodeManager::mkSExprType(const std::vector<TypeNode>& types) {
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0; i < types.size(); ++ i) {
    typeNodes.push_back(types[i]);
  }
  return mkTypeNode(kind::SEXPR_TYPE, typeNodes);
}

inline TypeNode NodeManager::mkBitVectorType(unsigned size) {
  return TypeNode(mkTypeConst<BitVectorSize>(BitVectorSize(size)));
}

inline TypeNode NodeManager::mkFloatingPointType(unsigned exp, unsigned sig) {
  return TypeNode(mkTypeConst<FloatingPointSize>(FloatingPointSize(exp,sig)));
}

inline TypeNode NodeManager::mkFloatingPointType(FloatingPointSize fs) {
  return TypeNode(mkTypeConst<FloatingPointSize>(fs));
}

inline TypeNode NodeManager::mkArrayType(TypeNode indexType,
                                         TypeNode constituentType) {
  CheckArgument(!indexType.isNull(), indexType,
                "unexpected NULL index type");
  CheckArgument(!constituentType.isNull(), constituentType,
                "unexpected NULL constituent type");
  CheckArgument(!indexType.isFunctionLike(), indexType,
                "cannot index arrays by a function-like type");
  CheckArgument(!constituentType.isFunctionLike(), constituentType,
                "cannot store function-like types in arrays");
  Debug("arrays") << "making array type " << indexType << " "
                  << constituentType << std::endl;
  return mkTypeNode(kind::ARRAY_TYPE, indexType, constituentType);
}

inline TypeNode NodeManager::mkSetType(TypeNode elementType) {
  CheckArgument(!elementType.isNull(), elementType,
                "unexpected NULL element type");
  // TODO: Confirm meaning of isFunctionLike(). --K
  CheckArgument(!elementType.isFunctionLike(), elementType,
                "cannot store function-like types in sets");
  Debug("sets") << "making sets type " << elementType << std::endl;
  return mkTypeNode(kind::SET_TYPE, elementType);
}

inline TypeNode NodeManager::mkSelectorType(TypeNode domain, TypeNode range) {
  CheckArgument(!domain.isFunctionLike(), domain,
                "cannot create higher-order function types");
  CheckArgument(!range.isFunctionLike(), range,
                "cannot create higher-order function types");
  return mkTypeNode(kind::SELECTOR_TYPE, domain, range);
}

inline TypeNode NodeManager::mkTesterType(TypeNode domain) {
  CheckArgument(!domain.isFunctionLike(), domain,
                "cannot create higher-order function types");
  return mkTypeNode(kind::TESTER_TYPE, domain );
}

inline expr::NodeValue* NodeManager::poolLookup(expr::NodeValue* nv) const {
  NodeValuePool::const_iterator find = d_nodeValuePool.find(nv);
  if(find == d_nodeValuePool.end()) {
    return NULL;
  } else {
    return *find;
  }
}

inline void NodeManager::poolInsert(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) == d_nodeValuePool.end(),
         "NodeValue already in the pool!");
  d_nodeValuePool.insert(nv);// FIXME multithreading
}

inline void NodeManager::poolRemove(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) != d_nodeValuePool.end(),
         "NodeValue is not in the pool!");

  d_nodeValuePool.erase(nv);// FIXME multithreading
}

inline Expr NodeManager::toExpr(TNode n) {
  return Expr(d_exprManager, new Node(n));
}

inline Node NodeManager::fromExpr(const Expr& e) {
  return e.getNode();
}

inline ExprManager* NodeManager::toExprManager() {
  return d_exprManager;
}

inline NodeManager* NodeManager::fromExprManager(ExprManager* exprManager) {
  return exprManager->getNodeManager();
}

inline Type NodeManager::toType(TypeNode tn) {
  return Type(this, new TypeNode(tn));
}

inline TypeNode NodeManager::fromType(Type t) {
  return *Type::getTypeNode(t);
}

}/* CVC4 namespace */

#define __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP
#include "expr/metakind.h"
#undef __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP

#include "expr/node_builder.h"

namespace CVC4 {

// general expression-builders

inline bool NodeManager::hasOperator(Kind k) {
  switch(kind::MetaKind mk = kind::metaKindOf(k)) {

  case kind::metakind::INVALID:
  case kind::metakind::VARIABLE:
    return false;

  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    return true;

  case kind::metakind::CONSTANT:
    return false;

  default:
    Unhandled(mk);
  }
}

inline Kind NodeManager::operatorToKind(TNode n) {
  return kind::operatorToKind(n.d_nv);
}

inline Node NodeManager::mkNode(Kind kind, TNode child1) {
  NodeBuilder<1> nb(this, kind);
  nb << child1;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(Kind kind, TNode child1) {
  NodeBuilder<1> nb(this, kind);
  nb << child1;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2) {
  NodeBuilder<2> nb(this, kind);
  nb << child1 << child2;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(Kind kind, TNode child1, TNode child2) {
  NodeBuilder<2> nb(this, kind);
  nb << child1 << child2;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder<3> nb(this, kind);
  nb << child1 << child2 << child3;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(Kind kind, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder<3> nb(this, kind);
  nb << child1 << child2 << child3;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3, TNode child4) {
  NodeBuilder<4> nb(this, kind);
  nb << child1 << child2 << child3 << child4;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(Kind kind, TNode child1, TNode child2,
                                TNode child3, TNode child4) {
  NodeBuilder<4> nb(this, kind);
  nb << child1 << child2 << child3 << child4;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3, TNode child4, TNode child5) {
  NodeBuilder<5> nb(this, kind);
  nb << child1 << child2 << child3 << child4 << child5;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(Kind kind, TNode child1, TNode child2,
                                    TNode child3, TNode child4, TNode child5) {
  NodeBuilder<5> nb(this, kind);
  nb << child1 << child2 << child3 << child4 << child5;
  return nb.constructNodePtr();
}

// N-ary version
template <bool ref_count>
inline Node NodeManager::mkNode(Kind kind,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  NodeBuilder<> nb(this, kind);
  nb.append(children);
  return nb.constructNode();
}

template <bool ref_count>
inline Node* NodeManager::mkNodePtr(Kind kind,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  NodeBuilder<> nb(this, kind);
  nb.append(children);
  return nb.constructNodePtr();
}

// for operators
inline Node NodeManager::mkNode(TNode opNode) {
  NodeBuilder<1> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode) {
  NodeBuilder<1> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1) {
  NodeBuilder<2> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode, TNode child1) {
  NodeBuilder<2> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2) {
  NodeBuilder<3> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode, TNode child1, TNode child2) {
  NodeBuilder<3> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder<4> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder<4> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2,
                                TNode child3, TNode child4) {
  NodeBuilder<5> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3 << child4;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode, TNode child1, TNode child2,
                                TNode child3, TNode child4) {
  NodeBuilder<5> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3 << child4;
  return nb.constructNodePtr();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2,
                                TNode child3, TNode child4, TNode child5) {
  NodeBuilder<6> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3 << child4 << child5;
  return nb.constructNode();
}

inline Node* NodeManager::mkNodePtr(TNode opNode, TNode child1, TNode child2,
                                    TNode child3, TNode child4, TNode child5) {
  NodeBuilder<6> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3 << child4 << child5;
  return nb.constructNodePtr();
}

// N-ary version for operators
template <bool ref_count>
inline Node NodeManager::mkNode(TNode opNode,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  NodeBuilder<> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb.append(children);
  return nb.constructNode();
}

template <bool ref_count>
inline Node* NodeManager::mkNodePtr(TNode opNode,
                                    const std::vector<NodeTemplate<ref_count> >&
                                    children) {
  NodeBuilder<> nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb.append(children);
  return nb.constructNodePtr();
}


inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1) {
  return (NodeBuilder<1>(this, kind) << child1).constructTypeNode();
}

inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1,
                                        TypeNode child2) {
  return (NodeBuilder<2>(this, kind) << child1 << child2).constructTypeNode();
}

inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1,
                                        TypeNode child2, TypeNode child3) {
  return (NodeBuilder<3>(this, kind) << child1 << child2 << child3).constructTypeNode();
}

// N-ary version for types
inline TypeNode NodeManager::mkTypeNode(Kind kind,
                                        const std::vector<TypeNode>& children) {
  return NodeBuilder<>(this, kind).append(children).constructTypeNode();
}

template <class T>
Node NodeManager::mkConst(const T& val) {
  return mkConstInternal<Node, T>(val);
}

template <class T>
TypeNode NodeManager::mkTypeConst(const T& val) {
  return mkConstInternal<TypeNode, T>(val);
}

template <class NodeClass, class T>
NodeClass NodeManager::mkConstInternal(const T& val) {

  // typedef typename kind::metakind::constantMap<T>::OwningTheory theory_t;
  NVStorage<1> nvStorage;
  expr::NodeValue& nvStack = reinterpret_cast<expr::NodeValue&>(nvStorage);

  nvStack.d_id = 0;
  nvStack.d_kind = kind::metakind::ConstantMap<T>::kind;
  nvStack.d_rc = 0;
  nvStack.d_nchildren = 1;

#if defined(__GNUC__) && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6))
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Warray-bounds"
#endif

  nvStack.d_children[0] =
    const_cast<expr::NodeValue*>(reinterpret_cast<const expr::NodeValue*>(&val));
  expr::NodeValue* nv = poolLookup(&nvStack);

#if defined(__GNUC__) && (__GNUC__ > 4 || (__GNUC__ == 4 && __GNUC_MINOR__ >= 6))
#pragma GCC diagnostic pop
#endif

  if(nv != NULL) {
    return NodeClass(nv);
  }

  nv = (expr::NodeValue*)
    std::malloc(sizeof(expr::NodeValue) + sizeof(T));
  if(nv == NULL) {
    throw std::bad_alloc();
  }

  nv->d_nchildren = 0;
  nv->d_kind = kind::metakind::ConstantMap<T>::kind;
  nv->d_id = next_id++;// FIXME multithreading
  nv->d_rc = 0;

  //OwningTheory::mkConst(val);
  new (&nv->d_children) T(val);

  poolInsert(nv);
  if(Debug.isOn("gc")) {
    Debug("gc") << "creating node value " << nv
                << " [" << nv->d_id << "]: ";
    nv->printAst(Debug("gc"));
    Debug("gc") << std::endl;
  }

  return NodeClass(nv);
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_MANAGER_H */
