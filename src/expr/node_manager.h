/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A manager for Nodes.
 */

#include "cvc5_private.h"

/* circular dependency; force node.h first */
//#include "expr/attribute.h"
#include "expr/node.h"
#include "expr/type_node.h"

#ifndef CVC5__NODE_MANAGER_H
#define CVC5__NODE_MANAGER_H

#include <string>
#include <unordered_set>
#include <vector>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_value.h"
#include "util/floatingpoint_size.h"

namespace cvc5 {

using Record = std::vector<std::pair<std::string, TypeNode>>;

namespace api {
class Solver;
}

class ResourceManager;
class SkolemManager;
class BoundVarManager;

class DType;

namespace expr {
  namespace attr {
    class AttributeUniqueId;
    class AttributeManager;
    }  // namespace attr

  class TypeChecker;
  }  // namespace expr

/**
 * An interface that an interested party can implement and then subscribe
 * to NodeManager events via NodeManager::subscribeEvents(this).
 */
class NodeManagerListener {
 public:
  virtual ~NodeManagerListener() {}
  virtual void nmNotifyNewSort(TypeNode tn, uint32_t flags) {}
  virtual void nmNotifyNewSortConstructor(TypeNode tn, uint32_t flags) {}
  virtual void nmNotifyInstantiateSortConstructor(TypeNode ctor, TypeNode sort,
                                                  uint32_t flags) {}
  virtual void nmNotifyNewDatatypes(const std::vector<TypeNode>& datatypes,
                                    uint32_t flags)
  {
  }
  virtual void nmNotifyNewVar(TNode n) {}
  virtual void nmNotifyNewSkolem(TNode n, const std::string& comment,
                                 uint32_t flags) {}
  /**
   * Notify a listener of a Node that's being GCed.  If this function stores a
   * reference
   * to the Node somewhere, very bad things will happen.
   */
  virtual void nmNotifyDeleteNode(TNode n) {}
}; /* class NodeManagerListener */

class NodeManager
{
  friend class api::Solver;
  friend class expr::NodeValue;
  friend class expr::TypeChecker;
  friend class SkolemManager;

  friend class NodeBuilder;
  friend class NodeManagerScope;

 public:
  /**
   * Return true if given kind is n-ary. The test is based on n-ary kinds
   * having their maximal arity as the maximal possible number of children
   * of a node.
   */
  static bool isNAryKind(Kind k);

 private:
  /** Predicate for use with STL algorithms */
  struct NodeValueReferenceCountNonZero {
    bool operator()(expr::NodeValue* nv) { return nv->d_rc > 0; }
  };

  typedef std::unordered_set<expr::NodeValue*,
                             expr::NodeValuePoolHashFunction,
                             expr::NodeValuePoolEq> NodeValuePool;
  typedef std::unordered_set<expr::NodeValue*,
                             expr::NodeValueIDHashFunction,
                             expr::NodeValueIDEquality> NodeValueIDSet;

  static thread_local NodeManager* s_current;

  /** The skolem manager */
  std::unique_ptr<SkolemManager> d_skManager;
  /** The bound variable manager */
  std::unique_ptr<BoundVarManager> d_bvManager;

  NodeValuePool d_nodeValuePool;

  size_t next_id;

  expr::attr::AttributeManager* d_attrManager;

  /**
   * The node value we're currently freeing.  This unique node value
   * is permitted to have outstanding TNodes to it (in "soft"
   * contexts, like as a key in attribute tables), even though
   * normally it's an error to have a TNode to a node value with a
   * reference count of 0.  Being "under deletion" also enables
   * assertions that inc() is not called on it.
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
   * plusOperator->getConst<cvc5::Kind>(), you get kind::PLUS back.
   */
  Node d_operators[kind::LAST_KIND];

  /** unique vars per (Kind,Type) */
  std::map< Kind, std::map< TypeNode, Node > > d_unique_vars;

  /**
   * A list of subscribers for NodeManager events.
   */
  std::vector<NodeManagerListener*> d_listeners;

  /** A list of datatypes owned by this node manager */
  std::vector<std::unique_ptr<DType> > d_dtypes;

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

    // `d_zombies` uses the node id to hash and compare nodes. If `d_zombies`
    // already contains a node value with the same id as `nv`, but the pointers
    // are different, then the wrong `NodeManager` was in scope for one of the
    // two nodes when it reached refcount zero.
    Assert(d_zombies.find(nv) == d_zombies.end() || *d_zombies.find(nv) == nv);

    d_zombies.insert(nv);

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

  // undefined private copy constructor (disallow copy)
  NodeManager(const NodeManager&) = delete;

  NodeManager& operator=(const NodeManager&) = delete;

  void init();

  /**
   * Create a variable with the given name and type.  NOTE that no
   * lookup is done on the name.  If you mkVar("a", type) and then
   * mkVar("a", type) again, you have two variables.  The NodeManager
   * version of this is private to avoid internal uses of mkVar() from
   * within cvc5.  Such uses should employ SkolemManager::mkSkolem() instead.
   */
  Node mkVar(const std::string& name, const TypeNode& type);

  /** Create a variable with the given type. */
  Node mkVar(const TypeNode& type);

  /**
   * Create a skolem constant with the given name, type, and comment. For
   * details, see SkolemManager::mkDummySkolem, which calls this method.
   *
   * This method is intentionally private. To create skolems, one should
   * call a method from SkolemManager for allocating a skolem in a standard
   * way, or otherwise use SkolemManager::mkDummySkolem.
   */
  Node mkSkolem(const std::string& prefix,
                const TypeNode& type,
                const std::string& comment = "",
                int flags = SKOLEM_DEFAULT);

 public:
  explicit NodeManager();
  ~NodeManager();

  /** The node manager in the current public-facing cvc5 library context */
  static NodeManager* currentNM() { return s_current; }
  /** Get this node manager's skolem manager */
  SkolemManager* getSkolemManager() { return d_skManager.get(); }
  /** Get this node manager's bound variable manager */
  BoundVarManager* getBoundVarManager() { return d_bvManager.get(); }

  /** Subscribe to NodeManager events */
  void subscribeEvents(NodeManagerListener* listener) {
    Assert(std::find(d_listeners.begin(), d_listeners.end(), listener)
           == d_listeners.end())
        << "listener already subscribed";
    d_listeners.push_back(listener);
  }

  /** Unsubscribe from NodeManager events */
  void unsubscribeEvents(NodeManagerListener* listener) {
    std::vector<NodeManagerListener*>::iterator elt = std::find(d_listeners.begin(), d_listeners.end(), listener);
    Assert(elt != d_listeners.end()) << "listener not subscribed";
    d_listeners.erase(elt);
  }

  /**
   * Return the datatype at the given index owned by this class. Type nodes are
   * associated with datatypes through the DatatypeIndexConstant class. The
   * argument index is intended to be a value taken from that class.
   *
   * Type nodes must access their DTypes through a level of indirection to
   * prevent cycles in the Node AST (as DTypes themselves contain Nodes), which
   * would lead to memory leaks. Thus TypeNode are given a DatatypeIndexConstant
   * which is used as an index to retrieve the DType via this call.
   */
  const DType& getDTypeForIndex(size_t index) const;

  /** Get a Kind from an operator expression */
  static inline Kind operatorToKind(TNode n);

  /** Get corresponding application kind for function
   *
   * Different functional nodes are applied differently, according to their
   * type. For example, uninterpreted functions (of FUNCTION_TYPE) are applied
   * via APPLY_UF, while constructors (of CONSTRUCTOR_TYPE) via
   * APPLY_CONSTRUCTOR. This method provides the correct application according
   * to which functional type fun has.
   *
   * @param fun The functional node
   * @return the correct application kind for fun. If fun's type is not function
   * like (see TypeNode::isFunctionLike), then UNDEFINED_KIND is returned.
   */
  static Kind getKindForFunction(TNode fun);

  // general expression-builders
  //
  /** Create a node with no child. */
  Node mkNode(Kind kind);

  /** Create a node with one child. */
  Node mkNode(Kind kind, TNode child1);

  /** Create a node with two children. */
  Node mkNode(Kind kind, TNode child1, TNode child2);

  /** Create a node with three children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3);

  /** Create a node with an arbitrary number of children. */
  template <bool ref_count>
  Node mkNode(Kind kind, const std::vector<NodeTemplate<ref_count> >& children);

  /** Create a node using an initializer list.
   *
   * This function serves two purposes:
   * - We can avoid creating a temporary vector in some cases, e.g., when we
   *   want to create a node with a fixed, large number of children
   * - It makes sure that calls to `mkNode` that braced-init-lists work as
   *   expected, e.g., mkNode(REGEXP_EMPTY, {}) will call this overload instead
   *   of creating a node with a null node as a child.
   */
  Node mkNode(Kind kind, std::initializer_list<TNode> children);

  /**
   * Create an AND node with arbitrary number of children. This returns the
   * true node if children is empty, or the single node in children if
   * it contains only one node.
   *
   * We define construction of AND as a special case here since it is widely
   * used for e.g. constructing explanations.
   */
  template <bool ref_count>
  Node mkAnd(const std::vector<NodeTemplate<ref_count> >& children);

  /**
   * Create an OR node with arbitrary number of children. This returns the
   * false node if children is empty, or the single node in children if
   * it contains only one node.
   *
   * We define construction of OR as a special case here since it is widely
   * used for e.g. constructing explanations or lemmas.
   */
  template <bool ref_count>
  Node mkOr(const std::vector<NodeTemplate<ref_count> >& children);

  /** Create a node (with no children) by operator. */
  Node mkNode(TNode opNode);

  /** Create a node with one child by operator. */
  Node mkNode(TNode opNode, TNode child1);

  /** Create a node with two children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2);

  /** Create a node with three children by operator. */
  Node mkNode(TNode opNode, TNode child1, TNode child2, TNode child3);

  /** Create a node by applying an operator to the children. */
  template <bool ref_count>
  Node mkNode(TNode opNode, const std::vector<NodeTemplate<ref_count> >& children);

  /**
   * Create a node by applying an operator to an arbitrary number of children.
   *
   * Analoguous to `mkNode(Kind, std::initializer_list<TNode>)`.
   */
  Node mkNode(TNode opNode, std::initializer_list<TNode> children);

  Node mkBoundVar(const std::string& name, const TypeNode& type);

  Node mkBoundVar(const TypeNode& type);

  /** get the canonical bound variable list for function type tn */
  Node getBoundVarListForFunctionType( TypeNode tn );

  /**
   * Create an Node by applying an associative operator to the children.
   * If <code>children.size()</code> is greater than the max arity for
   * <code>kind</code>, then the expression will be broken up into
   * suitably-sized chunks, taking advantage of the associativity of
   * <code>kind</code>. For example, if kind <code>FOO</code> has max arity
   * 2, then calling <code>mkAssociative(FOO,a,b,c)</code> will return
   * <code>(FOO (FOO a b) c)</code> or <code>(FOO a (FOO b c))</code>.
   * The order of the arguments will be preserved in a left-to-right
   * traversal of the resulting tree.
   */
  Node mkAssociative(Kind kind, const std::vector<Node>& children);

  /**
   * Create an Node by applying an binary left-associative operator to the
   * children. For example, mkLeftAssociative( f, { a, b, c } ) returns
   * f( f( a, b ), c ).
   */
  Node mkLeftAssociative(Kind kind, const std::vector<Node>& children);
  /**
   * Create an Node by applying an binary right-associative operator to the
   * children. For example, mkRightAssociative( f, { a, b, c } ) returns
   * f( a, f( b, c ) ).
   */
  Node mkRightAssociative(Kind kind, const std::vector<Node>& children);

  /** make chain
   *
   * Given a kind k and arguments t_1, ..., t_n, this returns the
   * conjunction of:
   *  (k t_1 t_2) .... (k t_{n-1} t_n)
   * It is expected that k is a kind denoting a predicate, and args is a list
   * of terms of size >= 2 such that the terms above are well-typed.
   */
  Node mkChain(Kind kind, const std::vector<Node>& children);

  /**
   * Optional flags used to control behavior of NodeManager::mkSkolem().
   * They should be composed with a bitwise OR (e.g.,
   * "SKOLEM_NO_NOTIFY | SKOLEM_EXACT_NAME").  Of course, SKOLEM_DEFAULT
   * cannot be composed in such a manner.
   */
  enum SkolemFlags
  {
    SKOLEM_DEFAULT = 0,    /**< default behavior */
    SKOLEM_NO_NOTIFY = 1,  /**< do not notify subscribers */
    SKOLEM_EXACT_NAME = 2, /**< do not make the name unique by adding the id */
    SKOLEM_IS_GLOBAL = 4,  /**< global vars appear in models even after a pop */
    SKOLEM_BOOL_TERM_VAR = 8 /**< vars requiring kind BOOLEAN_TERM_VARIABLE */
  };                         /* enum SkolemFlags */

  /** Create a instantiation constant with the given type. */
  Node mkInstConstant(const TypeNode& type);

  /** Create a boolean term variable. */
  Node mkBooleanTermVariable();

  /** Make a new abstract value with the given type. */
  Node mkAbstractValue(const TypeNode& type);

  /** make unique (per Type,Kind) variable. */
  Node mkNullaryOperator(const TypeNode& type, Kind k);

  /**
  * Create a singleton set from the given element n.
  * @param t the element type of the returned set.
  *          Note that the type of n needs to be a subtype of t.
  * @param n the single element in the singleton.
  * @return a singleton set constructed from the element n.
  */
  Node mkSingleton(const TypeNode& t, const TNode n);

  /**
  * Create a bag from the given element n along with its multiplicity m.
  * @param t the element type of the returned bag.
  *          Note that the type of n needs to be a subtype of t.
  * @param n the element that is used to to construct the bag
  * @param m the multiplicity of the element n
  * @return a bag that contains m occurrences of n.
  */
  Node mkBag(const TypeNode& t, const TNode n, const TNode m);

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
   * n.getConst<cvc5::Kind>() will yield k.
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
  TypeNode booleanType();

  /** Get the (singleton) type for integers. */
  TypeNode integerType();

  /** Get the (singleton) type for reals. */
  TypeNode realType();

  /** Get the (singleton) type for strings. */
  TypeNode stringType();

  /** Get the (singleton) type for RegExp. */
  TypeNode regExpType();

  /** Get the (singleton) type for rounding modes. */
  TypeNode roundingModeType();

  /** Get the bound var list type. */
  TypeNode boundVarListType();

  /** Get the instantiation pattern type. */
  TypeNode instPatternType();

  /** Get the instantiation pattern type. */
  TypeNode instPatternListType();

  /**
   * Get the (singleton) type for builtin operators (that is, the type
   * of the Node returned from Node::getOperator() when the operator
   * is built-in, like EQUAL). */
  TypeNode builtinOperatorType();

  /**
   * Make a function type from domain to range.
   *
   * @param domain the domain type
   * @param range the range type
   * @returns the functional type domain -> range
   */
  TypeNode mkFunctionType(const TypeNode& domain,
                          const TypeNode& range);

  /**
   * Make a function type with input types from
   * argTypes. <code>argTypes</code> must have at least one element.
   *
   * @param argTypes the domain is a tuple (argTypes[0], ..., argTypes[n])
   * @param range the range type
   * @returns the functional type (argTypes[0], ..., argTypes[n]) -> range
   */
  TypeNode mkFunctionType(const std::vector<TypeNode>& argTypes,
                          const TypeNode& range);

  /**
   * Make a function type with input types from
   * <code>sorts[0..sorts.size()-2]</code> and result type
   * <code>sorts[sorts.size()-1]</code>. <code>sorts</code> must have
   * at least 2 elements.
   *
   * @param sorts The argument and range sort of the function type, where the
   * range type is the last in this vector.
   * @return the function type
   */
  TypeNode mkFunctionType(const std::vector<TypeNode>& sorts);

  /**
   * Make a predicate type with input types from
   * <code>sorts</code>. The result with be a function type with range
   * <code>BOOLEAN</code>. <code>sorts</code> must have at least one
   * element.
   */
  TypeNode mkPredicateType(const std::vector<TypeNode>& sorts);

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
   * @returns the symbolic expression type
   */
  TypeNode sExprType();

  /** Make the type of floating-point with <code>exp</code> bit exponent and
      <code>sig</code> bit significand */
  TypeNode mkFloatingPointType(unsigned exp, unsigned sig);
  TypeNode mkFloatingPointType(FloatingPointSize fs);

  /** Make the type of bitvectors of size <code>size</code> */
  TypeNode mkBitVectorType(unsigned size);

  /** Make the type of arrays with the given parameterization */
  inline TypeNode mkArrayType(TypeNode indexType, TypeNode constituentType);

  /** Make the type of set with the given parameterization */
  inline TypeNode mkSetType(TypeNode elementType);

  /** Make the type of bags with the given parameterization */
  TypeNode mkBagType(TypeNode elementType);

  /** Make the type of sequences with the given parameterization */
  TypeNode mkSequenceType(TypeNode elementType);

  /** Bits for use in mkDatatypeType() flags.
   *
   * DATATYPE_FLAG_PLACEHOLDER indicates that the type should not be printed
   * out as a definition, for example, in models or during dumping.
   */
  enum
  {
    DATATYPE_FLAG_NONE = 0,
    DATATYPE_FLAG_PLACEHOLDER = 1
  }; /* enum */

  /** Make a type representing the given datatype. */
  TypeNode mkDatatypeType(DType& datatype, uint32_t flags = DATATYPE_FLAG_NONE);

  /**
   * Make a set of types representing the given datatypes, which may be
   * mutually recursive.
   */
  std::vector<TypeNode> mkMutualDatatypeTypes(
      const std::vector<DType>& datatypes, uint32_t flags = DATATYPE_FLAG_NONE);

  /**
   * Make a set of types representing the given datatypes, which may
   * be mutually recursive.  unresolvedTypes is a set of SortTypes
   * that were used as placeholders in the Datatypes for the Datatypes
   * of the same name.  This is just a more complicated version of the
   * above mkMutualDatatypeTypes() function, but is required to handle
   * complex types.
   *
   * For example, unresolvedTypes might contain the single sort "list"
   * (with that name reported from SortType::getName()).  The
   * datatypes list might have the single datatype
   *
   *   DATATYPE
   *     list = cons(car:ARRAY INT OF list, cdr:list) | nil;
   *   END;
   *
   * To represent the Type of the array, the user had to create a
   * placeholder type (an uninterpreted sort) to stand for "list" in
   * the type of "car".  It is this placeholder sort that should be
   * passed in unresolvedTypes.  If the datatype was of the simpler
   * form:
   *
   *   DATATYPE
   *     list = cons(car:list, cdr:list) | nil;
   *   END;
   *
   * then no complicated Type needs to be created, and the above,
   * simpler form of mkMutualDatatypeTypes() is enough.
   */
  std::vector<TypeNode> mkMutualDatatypeTypes(
      const std::vector<DType>& datatypes,
      const std::set<TypeNode>& unresolvedTypes,
      uint32_t flags = DATATYPE_FLAG_NONE);

  /**
   * Make a type representing a constructor with the given argument (subfield)
   * types and return type range.
   */
  TypeNode mkConstructorType(const std::vector<TypeNode>& args, TypeNode range);

  /** Make a type representing a selector with the given parameterization */
  TypeNode mkSelectorType(TypeNode domain, TypeNode range);

  /** Make a type representing a tester with given parameterization */
  TypeNode mkTesterType(TypeNode domain);

  /** Make a type representing an updater with the given parameterization */
  TypeNode mkDatatypeUpdateType(TypeNode domain, TypeNode range);

  /** Bits for use in mkSort() flags. */
  enum
  {
    SORT_FLAG_NONE = 0,
    SORT_FLAG_PLACEHOLDER = 1
  }; /* enum */

  /** Make a new (anonymous) sort of arity 0. */
  TypeNode mkSort(uint32_t flags = SORT_FLAG_NONE);

  /** Make a new sort with the given name of arity 0. */
  TypeNode mkSort(const std::string& name, uint32_t flags = SORT_FLAG_NONE);

  /** Make a new sort by parameterizing the given sort constructor. */
  TypeNode mkSort(TypeNode constructor,
                  const std::vector<TypeNode>& children,
                  uint32_t flags = SORT_FLAG_NONE);

  /** Make a new sort with the given name and arity. */
  TypeNode mkSortConstructor(const std::string& name,
                             size_t arity,
                             uint32_t flags = SORT_FLAG_NONE);

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
  TypeNode getType(TNode n, bool check = false);

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
   * This can be changed in node_manager.cpp without recompiling most of cvc5.
   *
   * debugHook is a debugging only function, and should not be present in
   * any published code!
   */
  void debugHook(int debugFlag);
}; /* class NodeManager */

/**
 * This class changes the "current" thread-global
 * <code>NodeManager</code> when it is created and reinstates the
 * previous thread-global <code>NodeManager</code> when it is
 * destroyed, effectively maintaining a set of nested
 * <code>NodeManager</code> scopes.  This is especially useful on
 * public-interface calls into the cvc5 library, where cvc5's notion
 * of the "current" <code>NodeManager</code> should be set to match
 * the calling context.  See, for example, the implementations of
 * public calls in the <code>SmtEngine</code> class.
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
public:
 NodeManagerScope(NodeManager* nm) : d_oldNodeManager(NodeManager::s_current)
 {
   NodeManager::s_current = nm;
   Debug("current") << "node manager scope: " << NodeManager::s_current << "\n";
  }

  ~NodeManagerScope() {
    NodeManager::s_current = d_oldNodeManager;
    Debug("current") << "node manager scope: "
                     << "returning to " << NodeManager::s_current << "\n";
  }
};/* class NodeManagerScope */

inline TypeNode NodeManager::mkArrayType(TypeNode indexType,
                                         TypeNode constituentType) {
  CheckArgument(!indexType.isNull(), indexType,
                "unexpected NULL index type");
  CheckArgument(!constituentType.isNull(), constituentType,
                "unexpected NULL constituent type");
  Debug("arrays") << "making array type " << indexType << " "
                  << constituentType << std::endl;
  return mkTypeNode(kind::ARRAY_TYPE, indexType, constituentType);
}

inline TypeNode NodeManager::mkSetType(TypeNode elementType) {
  CheckArgument(!elementType.isNull(), elementType,
                "unexpected NULL element type");
  Debug("sets") << "making sets type " << elementType << std::endl;
  return mkTypeNode(kind::SET_TYPE, elementType);
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
  Assert(d_nodeValuePool.find(nv) == d_nodeValuePool.end())
      << "NodeValue already in the pool!";
  d_nodeValuePool.insert(nv);// FIXME multithreading
}

inline void NodeManager::poolRemove(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) != d_nodeValuePool.end())
      << "NodeValue is not in the pool!";

  d_nodeValuePool.erase(nv);// FIXME multithreading
}

}  // namespace cvc5

#define CVC5__NODE_MANAGER_NEEDS_CONSTANT_MAP
#include "expr/metakind.h"
#undef CVC5__NODE_MANAGER_NEEDS_CONSTANT_MAP

#include "expr/node_builder.h"

namespace cvc5 {

// general expression-builders

inline bool NodeManager::hasOperator(Kind k) {
  switch(kind::MetaKind mk = kind::metaKindOf(k)) {

  case kind::metakind::INVALID:
  case kind::metakind::VARIABLE:
  case kind::metakind::NULLARY_OPERATOR:
    return false;

  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    return true;

  case kind::metakind::CONSTANT:
    return false;

  default: Unhandled() << mk;
  }
}

inline Kind NodeManager::operatorToKind(TNode n) {
  return kind::operatorToKind(n.d_nv);
}

inline Node NodeManager::mkNode(Kind kind)
{
  NodeBuilder nb(this, kind);
  return nb.constructNode();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1) {
  NodeBuilder nb(this, kind);
  nb << child1;
  return nb.constructNode();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2) {
  NodeBuilder nb(this, kind);
  nb << child1 << child2;
  return nb.constructNode();
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder nb(this, kind);
  nb << child1 << child2 << child3;
  return nb.constructNode();
}

// N-ary version
template <bool ref_count>
inline Node NodeManager::mkNode(Kind kind,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  NodeBuilder nb(this, kind);
  nb.append(children);
  return nb.constructNode();
}

template <bool ref_count>
Node NodeManager::mkAnd(const std::vector<NodeTemplate<ref_count> >& children)
{
  if (children.empty())
  {
    return mkConst(true);
  }
  else if (children.size() == 1)
  {
    return children[0];
  }
  return mkNode(kind::AND, children);
}

template <bool ref_count>
Node NodeManager::mkOr(const std::vector<NodeTemplate<ref_count> >& children)
{
  if (children.empty())
  {
    return mkConst(false);
  }
  else if (children.size() == 1)
  {
    return children[0];
  }
  return mkNode(kind::OR, children);
}

// for operators
inline Node NodeManager::mkNode(TNode opNode) {
  NodeBuilder nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  return nb.constructNode();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1) {
  NodeBuilder nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1;
  return nb.constructNode();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2) {
  NodeBuilder nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2;
  return nb.constructNode();
}

inline Node NodeManager::mkNode(TNode opNode, TNode child1, TNode child2,
                                TNode child3) {
  NodeBuilder nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb << child1 << child2 << child3;
  return nb.constructNode();
}

// N-ary version for operators
template <bool ref_count>
inline Node NodeManager::mkNode(TNode opNode,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  NodeBuilder nb(this, operatorToKind(opNode));
  if(opNode.getKind() != kind::BUILTIN) {
    nb << opNode;
  }
  nb.append(children);
  return nb.constructNode();
}

inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1) {
  return (NodeBuilder(this, kind) << child1).constructTypeNode();
}

inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1,
                                        TypeNode child2) {
  return (NodeBuilder(this, kind) << child1 << child2).constructTypeNode();
}

inline TypeNode NodeManager::mkTypeNode(Kind kind, TypeNode child1,
                                        TypeNode child2, TypeNode child3) {
  return (NodeBuilder(this, kind) << child1 << child2 << child3)
      .constructTypeNode();
}

// N-ary version for types
inline TypeNode NodeManager::mkTypeNode(Kind kind,
                                        const std::vector<TypeNode>& children) {
  return NodeBuilder(this, kind).append(children).constructTypeNode();
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
  // This method indirectly calls `NodeValue::inc()`, which relies on having
  // the correct `NodeManager` in scope.
  NodeManagerScope nms(this);

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

}  // namespace cvc5

#endif /* CVC5__NODE_MANAGER_H */
