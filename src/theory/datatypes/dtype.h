/*********************                                                        */
/*! \file dtype.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a datatype definition
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__DATATYPES__DATATYPE_H
#define CVC4__THEORY__DATATYPES__DATATYPE_H

#include <functional>
#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "base/exception.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "util/hash.h"

namespace CVC4 {

// messy; Node needs DType (because it's the payload of a
// CONSTANT-kinded expression), and DType needs Node.
//class  DType;
class  DTypeIndexConstant;
  
// FIXME
typedef TypeNode DTypeType;
  
class  NodeManager;

class DTypeConstructor;
class DTypeConstructorArg;

class DTypeConstructorIterator {
  const std::vector<DTypeConstructor>* d_v;
  size_t d_i;

  friend class DType;

  DTypeConstructorIterator(const std::vector<DTypeConstructor>& v, bool start) : d_v(&v), d_i(start ? 0 : v.size()) {
  }

public:
  typedef const DTypeConstructor& value_type;
  const DTypeConstructor& operator*() const { return (*d_v)[d_i]; }
  const DTypeConstructor* operator->() const { return &(*d_v)[d_i]; }
  DTypeConstructorIterator& operator++() { ++d_i; return *this; }
  DTypeConstructorIterator operator++(int) { DTypeConstructorIterator i(*this); ++d_i; return i; }
  bool operator==(const DTypeConstructorIterator& other) const { return d_v == other.d_v && d_i == other.d_i; }
  bool operator!=(const DTypeConstructorIterator& other) const { return d_v != other.d_v || d_i != other.d_i; }
};/* class DTypeConstructorIterator */

class DTypeConstructorArgIterator {
  const std::vector<DTypeConstructorArg>* d_v;
  size_t d_i;

  friend class DTypeConstructor;

  DTypeConstructorArgIterator(const std::vector<DTypeConstructorArg>& v, bool start) : d_v(&v), d_i(start ? 0 : v.size()) {
  }

public:
  typedef const DTypeConstructorArg& value_type;
  const DTypeConstructorArg& operator*() const { return (*d_v)[d_i]; }
  const DTypeConstructorArg* operator->() const { return &(*d_v)[d_i]; }
  DTypeConstructorArgIterator& operator++() { ++d_i; return *this; }
  DTypeConstructorArgIterator operator++(int) { DTypeConstructorArgIterator i(*this); ++d_i; return i; }
  bool operator==(const DTypeConstructorArgIterator& other) const { return d_v == other.d_v && d_i == other.d_i; }
  bool operator!=(const DTypeConstructorArgIterator& other) const { return d_v != other.d_v || d_i != other.d_i; }
};/* class DTypeConstructorArgIterator */

/**
 * An exception that is thrown when a datatype resolution fails.
 */
class DTypeResolutionException : public Exception {
 public:
  inline DTypeResolutionException(std::string msg);
};/* class DatatypeResolutionException */

/**
 * A holder type (used in calls to DTypeConstructor::addArg())
 * to allow a DType to refer to itself.  Self-typed fields of
 * DTypes will be properly typed when a Type is created for the
 * DType by the ExprManager (which calls DType::resolve()).
 */
class DTypeSelfType {
};/* class DTypeSelfType */

/**
 * An unresolved type (used in calls to
 * DTypeConstructor::addArg()) to allow a DType to refer to
 * itself or to other mutually-recursive DTypes.  Unresolved-type
 * fields of DTypes will be properly typed when a Type is created
 * for the DType by the NodeManager (which calls
 * DType::resolve()).
 */
class  DTypeUnresolvedType {
  std::string d_name;
public:
  inline DTypeUnresolvedType(std::string name);
  inline std::string getName() const;
};/* class DTypeUnresolvedType */

/**
 * A DType constructor argument (i.e., a DType field).
 */
class  DTypeConstructorArg {
  friend class DTypeConstructor;
  friend class DType;

 public:
  /** Get the name of this constructor argument. */
  std::string getName() const;

  /**
   * Get the selector for this constructor argument; this call is
   * only permitted after resolution.
   */
  Node getSelector() const;

  /**
   * Get the associated constructor for this constructor argument;
   * this call is only permitted after resolution.
   */
  Node getConstructor() const;

  /**
   * Get the type of the selector for this constructor argument;
   * this call is only permitted after resolution.
   */
  TypeNode getType() const;

  /**
   * Get the range type of this argument.
   */
  TypeNode getRangeType() const;

  /**
   * Returns true iff this constructor argument has been resolved.
   */
  bool isResolved() const;

  /** prints this datatype constructor argument to stream */
  void toStream(std::ostream& out) const;

 private:
  /** the name of this selector */
  std::string d_name;
  /** the selector expression */
  Node d_selector;
  /** the constructor associated with this selector */
  Node d_constructor;
  /** whether this class has been resolved */
  bool d_resolved;
  /** is this selector unresolved? */
  bool isUnresolvedSelf() const;
  /** constructor */
  DTypeConstructorArg(std::string name, Node selector);
};/* class DTypeConstructorArg */

class Printer;

/** sygus datatype constructor printer
 *
 * This is a virtual class that is used to specify
 * a custom printing callback for sygus terms. This is
 * useful for sygus grammars that include defined
 * functions or let expressions.
 */
class SygusPrintCallbackInternal
{
 public:
  SygusPrintCallbackInternal() {}
  virtual ~SygusPrintCallbackInternal() {}
  /**
   * Writes the term that sygus datatype expression e
   * encodes to stream out. p is the printer that
   * requested that expression e be written on output
   * stream out. Calls may be made to p to print
   * subterms of e.
   */
  virtual void toStreamSygus(const Printer* p,
                             std::ostream& out,
                             Node e) const = 0;
};

/**
 * A constructor for a DType.
 */
class  DTypeConstructor {
  friend class DType;

 public:
  /** The type for iterators over constructor arguments. */
  typedef DTypeConstructorArgIterator iterator;
  /** The (const) type for iterators over constructor arguments. */
  typedef DTypeConstructorArgIterator const_iterator;

  /**
   * Create a new DType constructor with the given name for the
   * constructor and the same name (prefixed with "is_") for the
   * tester.  The actual constructor and tester (meaning, the Nodes
   * representing operators for these entities) aren't created until
   * resolution time.
   */
  explicit DTypeConstructor(std::string name);

  /**
   * Create a new DType constructor with the given name for the
   * constructor and the given name for the tester.  The actual
   * constructor and tester aren't created until resolution time.
   * weight is the value that this constructor carries when computing size.
   * For example, if A, B, C have weights 0, 1, and 3 respectively, then
   * C( B( A() ), B( A() ) ) has size 5.
   */
  DTypeConstructor(std::string name,
                      std::string tester,
                      unsigned weight = 1);

  ~DTypeConstructor() {}
  /**
   * Add an argument (i.e., a data field) of the given name and type
   * to this DType constructor.  Selector names need not be unique;
   * they are for convenience and pretty-printing only.
   */
  void addArg(std::string selectorName, TypeNode selectorType);

  /**
   * Add an argument (i.e., a data field) of the given name to this
   * DType constructor that refers to an as-yet-unresolved
   * DType (which may be mutually-recursive).  Selector names need
   * not be unique; they are for convenience and pretty-printing only.
   */
  void addArg(std::string selectorName, DTypeUnresolvedType selectorType);

  /**
   * Add a self-referential (i.e., a data field) of the given name
   * to this DType constructor that refers to the enclosing
   * DType.  For example, using the familiar "nat" DType, to
   * create the "pred" field for "succ" constructor, one uses
   * succ::addArg("pred", DTypeSelfType())---the actual Type
   * cannot be passed because the DType is still under
   * construction.  Selector names need not be unique; they are for
   * convenience and pretty-printing only.
   *
   * This is a special case of
   * DTypeConstructor::addArg(std::string, DTypeUnresolvedType).
   */
  void addArg(std::string selectorName, DTypeSelfType);

  /** Get the name of this DType constructor. */
  std::string getName() const;

  /**
   * Get the constructor operator of this DType constructor.  The
   * DType must be resolved.
   */
  Node getConstructor() const;

  /**
   * Get the tester operator of this DType constructor.  The
   * DType must be resolved.
   */
  Node getTester() const;

  /** get sygus op
   *
   * This method returns the operator or
   * term that this constructor represents
   * in the sygus encoding. This may be a
   * builtin operator, defined function, variable,
   * or constant that this constructor encodes in this
   * deep embedding.
   */
  Node getSygusOp() const;
  /** is this a sygus identity function?
   *
   * This returns true if the sygus operator of this datatype constructor is
   * of the form (lambda (x) x).
   */
  bool isSygusIdFunc() const;
  /** get sygus print callback
   *
   * This class stores custom ways of printing
   * sygus datatype constructors, for instance,
   * to handle defined or let expressions that
   * appear in user-provided grammars.
   */
  std::shared_ptr<SygusPrintCallbackInternal> getSygusPrintCallbackInternal() const;
  /** get weight
   *
   * Get the weight of this constructor. This value is used when computing the
   * size of datatype terms that involve this constructor.
   */
  unsigned getWeight() const;

  /**
   * Get the tester name for this DType constructor.
   */
  std::string getTesterName() const;

  /**
   * Get the number of arguments (so far) of this DType constructor.
   */
  inline size_t getNumArgs() const;

  /**
   * Get the specialized constructor type for a parametric
   * constructor; this call is only permitted after resolution.
   * Given a (concrete) returnType, the constructor's concrete
   * type in this parametric datatype is returned.
   *
   * For instance, if the datatype is list[T], with constructor
   * "cons[T]" of type "T -> list[T] -> list[T]", then calling
   * this function with "list[int]" will return the concrete
   * "cons" constructor type for lists of int---namely,
   * "int -> list[int] -> list[int]".
   */
  TypeNode getSpecializedConstructorType(TypeNode returnType) const;

  /**
   * Return the cardinality of this constructor (the product of the
   * cardinalities of its arguments).
   */
  Cardinality getCardinality(TypeNode t) const;

  /**
   * Return true iff this constructor is finite (it is nullary or
   * each of its argument types are finite).  This function can
   * only be called for resolved constructors.
   */
  bool isFinite(TypeNode t) const;
  /**
   * Return true iff this constructor is finite (it is nullary or
   * each of its argument types are finite) under assumption
   * uninterpreted sorts are finite.  This function can
   * only be called for resolved constructors.
   */
  bool isInterpretedFinite(TypeNode t) const;

  /**
   * Returns true iff this DType constructor has already been
   * resolved.
   */
  inline bool isResolved() const;

  /** Get the beginning iterator over DTypeConstructor args. */
  inline iterator begin();
  /** Get the ending iterator over DTypeConstructor args. */
  inline iterator end();
  /** Get the beginning const_iterator over DTypeConstructor args. */
  inline const_iterator begin() const;
  /** Get the ending const_iterator over DTypeConstructor args. */
  inline const_iterator end() const;

  /** Get the ith DTypeConstructor arg. */
  const DTypeConstructorArg& operator[](size_t index) const;

  /**
   * Get the DTypeConstructor arg named.  This is a linear search
   * through the arguments, so in the case of multiple,
   * similarly-named arguments, the first is returned.
   */
  const DTypeConstructorArg& operator[](std::string name) const;

  /**
   * Get the selector named.  This is a linear search
   * through the arguments, so in the case of multiple,
   * similarly-named arguments, the selector for the first
   * is returned.
   */
  Node getSelector(std::string name) const;
  /**
   * Get argument type. Returns the return type of the i^th selector of this
   * constructor.
   */
  TypeNode getArgType(unsigned i) const;

  /** get selector internal
   *
   * This gets selector for the index^th argument
   * of this constructor. The type dtt is the datatype
   * type whose datatype is the owner of this constructor,
   * where this type may be an instantiated parametric datatype.
   *
   * If shared selectors are enabled,
   * this returns a shared (constructor-agnotic) selector, which
   * in the terminology of "DTypes with Shared Selectors", is:
   *   sel_{dtt}^{T,atos(T,C,index)}
   * where C is this constructor, and T is the type
   * of the index^th field of this constructor.
   * The semantics of sel_{dtt}^{T,n}( t ) is the n^th field of
   * type T of constructor term t if one exists, or is
   * unconstrained otherwise.
   */
  Node getSelectorInternal(TypeNode dtt, size_t index) const;

  /** get selector index internal
   *
   * This gets the argument number of this constructor
   * that the selector sel accesses. It returns -1 if the
   * selector sel is not a selector for this constructor.
   *
   * In the terminology of "DTypes with Shared Selectors",
   * if sel is sel_{dtt}^{T,index} for some (T, index), where
   * dtt is the datatype type whose datatype is the owner
   * of this constructor, then this method returns
   *   stoa(T,C,index)
   */
  int getSelectorIndexInternal( Node sel ) const;

  /** involves external type
   *
   * Get whether this constructor has a subfield
   * in any constructor that is not a datatype type.
   */
  bool involvesExternalType() const;
  /** involves external type
   *
   * Get whether this constructor has a subfield
   * in any constructor that is an uninterpreted type.
   */
  bool involvesUninterpretedType() const;

  /** set sygus
   *
   * Set that this constructor is a sygus datatype constructor that encodes
   * operator op. spc is the sygus callback of this datatype constructor,
   * which is stored in a shared pointer.
   */
  void setSygus(Node op, std::shared_ptr<SygusPrintCallbackInternal> spc);

  /**
   * Get the list of arguments to this constructor.
   */
  const std::vector<DTypeConstructorArg>* getArgs() const;

  /** prints this datatype constructor to stream */
  void toStream(std::ostream& out) const;

 private:
  /** the name of the constructor */
  std::string d_name;
  /** the constructor expression */
  Node d_constructor;
  /** the tester for this constructor */
  Node d_tester;
  /** the arguments of this constructor */
  std::vector<DTypeConstructorArg> d_args;
  /** sygus operator */
  Node d_sygus_op;
  /** sygus print callback */
  std::shared_ptr<SygusPrintCallbackInternal> d_sygus_pc;
  /** weight */
  unsigned d_weight;

  /** shared selectors for each type
   *
   * This stores the shared (constructor-agnotic)
   * selectors that access the fields of this datatype.
   * In the terminology of "DTypes with Shared Selectors",
   * this stores:
   *   sel_{dtt}^{T1,atos(T1,C,1)}, ...,
   *   sel_{dtt}^{Tn,atos(Tn,C,n)}
   * where C is this constructor, which has type
   * T1 x ... x Tn -> dtt above.
   * We store this information for (possibly multiple)
   * datatype types dtt, since this constructor may be
   * for a parametric datatype, where dtt is an instantiated
   * parametric datatype.
   */
  mutable std::map<TypeNode, std::vector<Node> > d_shared_selectors;
  /** for each type, a cache mapping from shared selectors to
   * its argument index for this constructor.
   */
  mutable std::map<TypeNode, std::map<Node, unsigned> > d_shared_selector_index;
  /** resolve
   *
   * This resolves (initializes) the constructor. For details
   * on how datatypes and their constructors are resolved, see
   * documentation for DType::resolve.
   */
  void resolve(NodeManager* em,
               DTypeType self,
               const std::map<std::string, DTypeType>& resolutions,
               const std::vector<TypeNode>& placeholders,
               const std::vector<TypeNode>& replacements,
               const std::vector<SortConstructorType>& paramTypes,
               const std::vector<DTypeType>& paramReplacements,
               size_t cindex);

  /** Helper function for resolving parametric datatypes.
   *
   * This replaces instances of the SortConstructorType produced for unresolved
   * parametric datatypes, with the corresponding resolved DTypeType.  For
   * example, take the parametric definition of a list,
   *    list[T] = cons(car : T, cdr : list[T]) | null.
   * If "range" is the unresolved parametric datatype:
   *   DATATYPE list =
   *    cons(car: SORT_TAG_1,
   *         cdr: SORT_TAG_2(SORT_TAG_1)) | null END;,
   * this function will return the resolved type:
   *   DATATYPE list =
   *    cons(car: SORT_TAG_1,
   *         cdr: (list PARAMETERIC_DATATYPE SORT_TAG_1)) | null END;
   */
  TypeNode doParametricSubstitution(
      TypeNode range,
      const std::vector<SortConstructorType>& paramTypes,
      const std::vector<DTypeType>& paramReplacements);

  /** compute the cardinality of this datatype */
  Cardinality computeCardinality(TypeNode t, std::vector<TypeNode>& processing) const;
  /** compute whether this datatype is well-founded */
  bool computeWellFounded(std::vector<TypeNode>& processing) const;
  /** compute ground term
   *
   * This method is used for constructing a term that is an application
   * of this constructor whose type is t.
   *
   * The argument processing is the set of datatype types we are currently
   * traversing. This is used to avoid infinite loops.
   *
   * The argument gt caches the ground terms we have computed so far.
   *
   * The argument isValue is whether we are constructing a constant value. If
   * this flag is false, we are constructing a canonical ground term that is
   * not necessarily constant.
   */
  Node computeGroundTerm(TypeNode t,
                         std::vector<TypeNode>& processing,
                         std::map<TypeNode, Node>& gt,
                         bool isValue) const;
  /** compute shared selectors
   * This computes the maps d_shared_selectors and d_shared_selector_index.
   */
  void computeSharedSelectors(TypeNode domainType) const;
};/* class DTypeConstructor */

/**
 * The representation of an inductive datatype.
 *
 * This is far more complicated than it first seems.  Consider this
 * datatype definition:
 *
 *   DATATYPE nat =
 *     succ(pred: nat)
 *   | zero
 *   END;
 *
 * You cannot define "nat" until you have a Type for it, but you
 * cannot have a Type for it until you fill in the type of the "pred"
 * selector, which needs the Type.  So we have a chicken-and-egg
 * problem.  It's even more complicated when we have mutual recursion
 * between datatypes, since the CVC presentation language does not
 * require forward-declarations.  Here, we define trees of lists that
 * contain trees of lists (etc):
 *
 *   DATATYPE
 *     tree = node(left: tree, right: tree) | leaf(list),
 *     list = cons(car: tree, cdr: list) | nil
 *   END;
 *
 * Note that while parsing the "tree" definition, we have to take it
 * on faith that "list" is a valid type.  We build DType objects to
 * describe "tree" and "list", and their constructors and constructor
 * arguments, but leave any unknown types (including self-references)
 * in an "unresolved" state.  After parsing the whole DATATYPE block,
 * we create a DTypeType through
 * NodeManager::mkMutualDTypeTypes().  The NodeManager creates a
 * DTypeType for each, but before "releasing" this type into the
 * wild, it does a round of in-place "resolution" on each DType by
 * calling DType::resolve() with a map of string -> DTypeType to
 * allow the datatype to construct the necessary testers and
 * selectors.
 *
 * An additional point to make is that we want to ease the burden on
 * both the parser AND the users of the CVC4 API, so this class takes
 * on the task of generating its own selectors and testers, for
 * instance.  That means that, after reifying the DType with the
 * NodeManager, the parser needs to go through the (now-resolved)
 * DType and request the constructor, selector, and tester terms.
 * See src/parser/parser.cpp for how this is done.  For API usage
 * ideas, see test/unit/util/datatype_black.h.
 *
 * DTypes may also be defined parametrically, such as this example:
 *
 *  DATATYPE
 *    list[T] = cons(car : T, cdr : list[T]) | null,
 *    tree = node(children : list[tree]) | leaf
 *  END;
 *
 * Here, the definition of the parametric datatype list, where T is a type variable.
 * In other words, this defines a family of types list[C] where C is any concrete
 * type.  DTypes can be parameterized over multiple type variables using the
 * syntax sym[ T1, ..., Tn ] = ...,
 *
 */
class  DType {
  friend class DTypeConstructor;
public:
  /**
   * Get the datatype of a constructor, selector, or tester operator.
   */
  static const DType& datatypeOf(Node item) ;

  /**
   * Get the index of a constructor or tester in its datatype, or the
   * index of a selector in its constructor.  (Zero is always the
   * first index.)
   */
  static size_t indexOf(Node item) ;

  /**
   * Get the index of constructor corresponding to selector.  (Zero is
   * always the first index.)
   */
  static size_t cindexOf(Node item) ;

  /**
   * Same as above, but without checks. These methods should be used by
   * internal (Node-level) code.
   */
  static size_t indexOfInternal(Node item);
  static size_t cindexOfInternal(Node item);

  /** The type for iterators over constructors. */
  typedef DTypeConstructorIterator iterator;
  /** The (const) type for iterators over constructors. */
  typedef DTypeConstructorIterator const_iterator;

  /** Create a new DType of the given name. */
  inline explicit DType(std::string name, bool isCo = false);

  /**
   * Create a new DType of the given name, with the given
   * parameterization.
   */
  inline DType(std::string name, const std::vector<TypeNode>& params, bool isCo = false);

  ~DType();

  /** Add a constructor to this DType.
   *
   * Notice that constructor names need not
   * be unique; they are for convenience and pretty-printing only.
   */
  void addConstructor(const DTypeConstructor& c);

  /** set sygus
   *
   * This marks this datatype as a sygus datatype.
   * A sygus datatype is one that represents terms of type st
   * via a deep embedding described in Section 4 of
   * Reynolds et al. CAV 2015. We say that this sygus datatype
   * "encodes" its sygus type st in the following.
   *
   * st : the type this datatype encodes (this can be Int, Bool, etc.),
   * bvl : the list of arguments for the synth-fun
   * allow_const : whether all constants are (implicitly) allowed by the
   * datatype
   * allow_all : whether all terms are (implicitly) allowed by the datatype
   *
   * Notice that allow_const/allow_all do not reflect the constructors
   * for this datatype, and instead are used solely for relaxing constraints
   * when doing solution reconstruction (Figure 5 of Reynolds et al.
   * CAV 2015).
   */
  void setSygus( TypeNode st, Node bvl, bool allow_const, bool allow_all );
  /** add sygus constructor
   *
   * This adds a sygus constructor to this datatype, where
   * this datatype should be currently unresolved.
   *
   * op : the builtin operator, constant, or variable that
   *      this constructor encodes
   * cname : the name of the constructor (for printing only)
   * cargs : the arguments of the constructor
   * spc : an (optional) callback that is used for custom printing. This is
   *       to accomodate user-provided grammars in the sygus format.
   *
   * It should be the case that cargs are sygus datatypes that
   * encode the arguments of op. For example, a sygus constructor
   * with op = PLUS should be such that cargs.size()>=2 and
   * the sygus type of cargs[i] is Real/Int for each i.
   *
   * weight denotes the value added by the constructor when computing the size
   * of datatype terms. Passing a value <0 denotes the default weight for the
   * constructor, which is 0 for nullary constructors and 1 for non-nullary
   * constructors.
   */
  void addSygusConstructor(Node op,
                           const std::string& cname,
                           const std::vector<TypeNode>& cargs,
                           std::shared_ptr<SygusPrintCallbackInternal> spc = nullptr,
                           int weight = -1);

  /** set that this datatype is a tuple */
  void setTuple();

  /** Get the name of this DType. */
  inline std::string getName() const;

  /** Get the number of constructors (so far) for this DType. */
  inline size_t getNumConstructors() const;

  /** Is this datatype parametric? */
  inline bool isParametric() const;

  /** Get the nubmer of type parameters */
  inline size_t getNumParameters() const;

  /** Get parameter */
  inline TypeNode getParameter( unsigned int i ) const;

  /** Get parameters */
  inline std::vector<TypeNode> getParameters() const;

  /** is this a co-datatype? */
  inline bool isCodatatype() const;

  /** is this a sygus datatype? */
  inline bool isSygus() const;

  /** is this a tuple datatype? */
  inline bool isTuple() const;

  /** get the record representation for this datatype */
  inline Record * getRecord() const;

  /**
   * Return the cardinality of this datatype.
   * The DType must be resolved.
   *
   * The version of this method that takes type t is required
   * for parametric datatypes, where t is an instantiated
   * parametric datatype type whose datatype is this class.
   */
  Cardinality getCardinality(TypeNode t) const;
  Cardinality getCardinality() const;

  /**
   * Return true iff this DType has finite cardinality. If the
   * datatype is not well-founded, this method returns false. The
   * DType must be resolved or an exception is thrown.
   *
   * The version of this method that takes type t is required
   * for parametric datatypes, where t is an instantiated
   * parametric datatype type whose datatype is this class.
   */
  bool isFinite(TypeNode t) const;
  bool isFinite() const;

  /**
   * Return true iff this  DType is finite (all constructors are
   * finite, i.e., there  are finitely  many ground terms) under the
   * assumption unintepreted sorts are finite. If the
   * datatype is  not well-founded, this method returns false.  The
   * DType must be resolved or an exception is thrown.
   *
   * The versions of these methods that takes type t is required
   * for parametric datatypes, where t is an instantiated
   * parametric datatype type whose datatype is this class.
   */
  bool isInterpretedFinite(TypeNode t) const;
  bool isInterpretedFinite() const;

  /** is well-founded
   *
   * Return true iff this datatype is well-founded (there exist finite
   * values of this type).
   * This datatype must be resolved or an exception is thrown.
   */
  bool isWellFounded() const;

  /** is recursive singleton
   *
   * Return true iff this datatype is a recursive singleton
   * (a recursive singleton is a recursive datatype with only
   * one infinite value). For details, see Reynolds et al. CADE 2015.
   *
   * The versions of these methods that takes type t is required
   * for parametric datatypes, where t is an instantiated
   * parametric datatype type whose datatype is this class.
   */
  bool isRecursiveSingleton(TypeNode t) const;
  bool isRecursiveSingleton() const;

  /** recursive single arguments
   *
   * Get recursive singleton argument types (uninterpreted sorts that the
   * cardinality of this datatype is dependent upon). For example, for :
   *   stream :=  cons( head1 : U1, head2 : U2, tail : stream )
   * Then, the recursive singleton argument types of stream are { U1, U2 },
   * since if U1 and U2 have cardinality one, then stream has cardinality
   * one as well.
   *
   * The versions of these methods that takes Type t is required
   * for parametric datatypes, where t is an instantiated
   * parametric datatype type whose datatype is this class.
  */
  unsigned getNumRecursiveSingletonArgTypes(TypeNode t) const;
  TypeNode getRecursiveSingletonArgType(TypeNode t, unsigned i) const;
  unsigned getNumRecursiveSingletonArgTypes() const;
  TypeNode getRecursiveSingletonArgType(unsigned i) const;

  /**
   * Construct and return a ground term of this DType.  The
   * DType must be both resolved and well-founded, or else an
   * exception is thrown.
   *
   * This method takes a type t, which is a datatype type whose
   * datatype is this class, which may be an instantiated datatype
   * type if this datatype is parametric.
   */
  Node mkGroundTerm(TypeNode t) const;
  /** Make ground value
   *
   * Same as above, but constructs a constant value instead of a ground term.
   * These two notions typically coincide. However, for uninterpreted sorts,
   * they do not: mkGroundTerm returns a fresh variable whereas mkValue returns
   * an uninterpreted constant. The motivation for mkGroundTerm is that
   * unintepreted constants should never appear in lemmas. The motivation for
   * mkGroundValue is for things like type enumeration and model construction.
   */
  Node mkGroundValue(TypeNode t) const;

  /**
   * Get the DTypeType associated to this DType.  Can only be
   * called post-resolution.
   */
  DTypeType getDTypeType() const;

  /**
   * Get the DTypeType associated to this (parameterized) DType.  Can only be
   * called post-resolution.
   */
  DTypeType getDTypeType(const std::vector<TypeNode>& params) const;

  /**
   * Return true iff the two DTypes are the same.
   *
   * We need == for mkConst(DType) to properly work---since if the
   * DType Node requested is the same as an already-existing one,
   * we need to return that one.  For that, we have a hash and
   * operator==.  We provide != for symmetry.  We don't provide
   * operator<() etc. because given two DType Nodes, you could
   * simply compare those rather than the (bare) DTypes.  This
   * means, though, that DType cannot be stored in a sorted list or
   * RB tree directly, so maybe we can consider adding these
   * comparison operators later on.
   */
  bool operator==(const DType& other) const;
  /** Return true iff the two DTypes are not the same. */
  inline bool operator!=(const DType& other) const;

  /** Return true iff this DType has already been resolved. */
  inline bool isResolved() const;

  /** Get the beginning iterator over DTypeConstructors. */
  inline iterator begin();
  /** Get the ending iterator over DTypeConstructors. */
  inline iterator end();
  /** Get the beginning const_iterator over DTypeConstructors. */
  inline const_iterator begin() const;
  /** Get the ending const_iterator over DTypeConstructors. */
  inline const_iterator end() const;

  /** Get the ith DTypeConstructor. */
  const DTypeConstructor& operator[](size_t index) const;

  /**
   * Get the DTypeConstructor named.  This is a linear search
   * through the constructors, so in the case of multiple,
   * similarly-named constructors, the first is returned.
   */
  const DTypeConstructor& operator[](std::string name) const;
 
  /**
   * Get the constructor operator for the named constructor.
   * This is a linear search through the constructors, so in
   * the case of multiple, similarly-named constructors, the
   * first is returned.
   *
   * This DType must be resolved.
   */
  Node getConstructor(std::string name) const;

  /** get sygus type
   * This gets the built-in type associated with
   * this sygus datatype, i.e. the type of the
   * term that this sygus datatype encodes.
   */
  TypeNode getSygusType() const;

  /** get sygus var list
   * This gets the variable list of the function
   * to synthesize using this sygus datatype.
   * For example, if we are synthesizing a binary
   * function f where solutions are of the form:
   *   f = (lambda (xy) t[x,y])
   * In this case, this method returns the
   * bound variable list containing x and y.
   */
  Node getSygusVarList() const;
  /** get sygus allow constants
   *
   * Does this sygus datatype allow constants?
   * Notice that this is not a property of the
   * constructors of this datatype. Instead, it is
   * an auxiliary flag (provided in the call
   * to setSygus).
   */
  bool getSygusAllowConst() const;
  /** get sygus allow all
   *
   * Does this sygus datatype allow all terms?
   * Notice that this is not a property of the
   * constructors of this datatype. Instead, it is
   * an auxiliary flag (provided in the call
   * to setSygus).
   */
  bool getSygusAllowAll() const;

  /** involves external type
   * Get whether this datatype has a subfield
   * in any constructor that is not a datatype type.
   */
  bool involvesExternalType() const;
  /** involves uninterpreted type
   * Get whether this datatype has a subfield
   * in any constructor that is an uninterpreted type.
   */
  bool involvesUninterpretedType() const;

  /**
   * Get the list of constructors.
   */
  const std::vector<DTypeConstructor>* getConstructors() const;

  /** prints this datatype to stream */
  void toStream(std::ostream& out) const;

 private:
  /** name of this datatype */
  std::string d_name;
  /** the type parameters of this datatype (if this is a parametric datatype)
   */
  std::vector<TypeNode> d_params;
  /** whether the datatype is a codatatype. */
  bool d_isCo;
  /** whether the datatype is a tuple */
  bool d_isTuple;
  /** the constructors of this datatype */
  std::vector<DTypeConstructor> d_constructors;
  /** whether this datatype has been resolved */
  bool d_resolved;
  TypeNode d_self;
  /** cache for involves external type */
  bool d_involvesExt;
  /** cache for involves uninterpreted type */
  bool d_involvesUt;
  /** the builtin type that this sygus type encodes */
  TypeNode d_sygus_type;
  /** the variable list for the sygus function to synthesize */
  Node d_sygus_bvl;
  /** whether all constants are allowed as solutions */
  bool d_sygus_allow_const;
  /** whether all terms are allowed as solutions */
  bool d_sygus_allow_all;

  /** the cardinality of this datatype
  * "mutable" because computing the cardinality can be expensive,
  * and so it's computed just once, on demand---this is the cache
  */
  mutable Cardinality d_card;

  /** is this type a recursive singleton type?
   * The range of this map stores
   * 0 if the field has not been computed,
   * 1 if this datatype is a recursive singleton type,
   * -1 if this datatype is not a recursive singleton type.
   * For definition of (co)recursive singleton, see
   * Section 2 of Reynolds et al. CADE 2015.
   */
  mutable std::map<TypeNode, int> d_card_rec_singleton;
  /** if d_card_rec_singleton is true,
  * This datatype has infinite cardinality if at least one of the
  * following uninterpreted sorts having cardinality > 1.
  */
  mutable std::map<TypeNode, std::vector<TypeNode> > d_card_u_assume;
  /** cache of whether this datatype is well-founded */
  mutable int d_well_founded;
  /** cache of ground term for this datatype */
  mutable std::map<TypeNode, Node> d_ground_term;
  /** cache of ground values for this datatype */
  mutable std::map<TypeNode, Node> d_ground_value;
  /** cache of shared selectors for this datatype */
  mutable std::map<TypeNode, std::map<TypeNode, std::map<unsigned, Node> > >
      d_shared_sel;

  /**
   * DTypes refer to themselves, recursively, and we have a
   * chicken-and-egg problem.  The DTypeType around the DType
   * cannot exist until the DType is finalized, and the DType
   * cannot refer to the DTypeType representing itself until it
   * exists.  resolve() is called by the NodeManager when a type is
   * ultimately requested of the DType specification (that is, when
   * NodeManager::mkDTypeType() or NodeManager::mkMutualDTypeTypes()
   * is called).  Has the effect of freezing the object, too; that is,
   * addConstructor() will fail after a call to resolve().
   *
   * The basic goal of resolution is to assign constructors, selectors,
   * and testers.  To do this, any UnresolvedType/SelfType references
   * must be cleared up.  This is the purpose of the "resolutions" map;
   * it includes any mutually-recursive datatypes that are currently
   * under resolution.  The four vectors come in two pairs (so, really
   * they are two maps).  placeholders->replacements give type variables
   * that should be resolved in the case of parametric datatypes.
   *
   * @param em the NodeManager at play
   * @param resolutions a map of strings to DTypeTypes currently under
   * resolution
   * @param placeholders the types in these DTypes under resolution that must
   * be replaced
   * @param replacements the corresponding replacements
   * @param paramTypes the sort constructors in these DTypes under resolution
   * that must be replaced
   * @param paramReplacements the corresponding (parametric) DTypeTypes
   */
  void resolve(NodeManager* em,
               const std::map<std::string, DTypeType>& resolutions,
               const std::vector<TypeNode>& placeholders,
               const std::vector<TypeNode>& replacements,
               const std::vector<SortConstructorType>& paramTypes,
               const std::vector<DTypeType>& paramReplacements);
  friend class NodeManager;  // for access to resolve()

  /** compute the cardinality of this datatype */
  Cardinality computeCardinality(TypeNode t, std::vector<TypeNode>& processing) const;
  /** compute whether this datatype is a recursive singleton */
  bool computeCardinalityRecSingleton(TypeNode t,
                                      std::vector<TypeNode>& processing,
                                      std::vector<TypeNode>& u_assume) const;
  /** compute whether this datatype is well-founded */
  bool computeWellFounded(std::vector<TypeNode>& processing) const;
  /** compute ground term
   *
   * This method checks if there is a term of this datatype whose type is t
   * that is finitely constructable. As needed, it traverses its subfield types.
   *
   * The argument processing is the set of datatype types we are currently
   * traversing.
   *
   * The argument isValue is whether we are constructing a constant value. If
   * this flag is false, we are constructing a canonical ground term that is
   * not necessarily constant.
   */
  Node computeGroundTerm(TypeNode t,
                         std::vector<TypeNode>& processing,
                         bool isValue) const;
  /** Get the shared selector
   *
   * This returns the index^th (constructor-agnostic)
   * selector for type t. The type dtt is the datatype
   * type whose datatype is this class, where this may
   * be an instantiated parametric datatype.
   *
   * In the terminology of "DTypes with Shared Selectors",
   * this returns the term sel_{dtt}^{t,index}.
   */
  Node getSharedSelector(TypeNode dtt, TypeNode t, unsigned index) const;
  /**
   * Helper for mkGroundTerm and mkGroundValue above.
   */
  Node mkGroundTermInternal(TypeNode t, bool isValue) const;
};/* class DType */

/**
 * A hash function for DTypes.  Needed to store them in hash sets
 * and hash maps.
 */
struct  DTypeHashFunction {
  inline size_t operator()(const DType& dt) const {
    return std::hash<std::string>()(dt.getName());
  }
  inline size_t operator()(const DType* dt) const {
    return std::hash<std::string>()(dt->getName());
  }
  inline size_t operator()(const DTypeConstructor& dtc) const {
    return std::hash<std::string>()(dtc.getName());
  }
  inline size_t operator()(const DTypeConstructor* dtc) const {
    return std::hash<std::string>()(dtc->getName());
  }
};/* struct DTypeHashFunction */



/* stores an index to DType residing in NodeManager */
class  DTypeIndexConstant {
 public:
  DTypeIndexConstant(unsigned index);

  unsigned getIndex() const { return d_index; }
  bool operator==(const DTypeIndexConstant& uc) const
  {
    return d_index == uc.d_index;
  }
  bool operator!=(const DTypeIndexConstant& uc) const
  {
    return !(*this == uc);
  }
  bool operator<(const DTypeIndexConstant& uc) const
  {
    return d_index < uc.d_index;
  }
  bool operator<=(const DTypeIndexConstant& uc) const
  {
    return d_index <= uc.d_index;
  }
  bool operator>(const DTypeIndexConstant& uc) const
  {
    return !(*this <= uc);
  }
  bool operator>=(const DTypeIndexConstant& uc) const
  {
    return !(*this < uc);
  }
private:
  const unsigned d_index;
};/* class DTypeIndexConstant */

std::ostream& operator<<(std::ostream& out, const DTypeIndexConstant& dic) ;

struct  DTypeIndexConstantHashFunction {
  inline size_t operator()(const DTypeIndexConstant& dic) const {
    return IntegerHashFunction()(dic.getIndex());
  }
};/* struct DTypeIndexConstantHashFunction */



// FUNCTION DECLARATIONS FOR OUTPUT STREAMS

std::ostream& operator<<(std::ostream& os, const DType& dt) ;
std::ostream& operator<<(std::ostream& os, const DTypeConstructor& ctor) ;
std::ostream& operator<<(std::ostream& os, const DTypeConstructorArg& arg) ;

// INLINE FUNCTIONS

inline DTypeResolutionException::DTypeResolutionException(std::string msg) :
  Exception(msg) {
}

inline DTypeUnresolvedType::DTypeUnresolvedType(std::string name) :
  d_name(name) {
}

inline std::string DTypeUnresolvedType::getName() const { return d_name; }
inline DType::DType(std::string name, bool isCo)
    : d_name(name),
      d_params(),
      d_isCo(isCo),
      d_isTuple(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygus_allow_const(false),
      d_sygus_allow_all(false),
      d_card(CardinalityUnknown()),
      d_well_founded(0) {}

inline DType::DType(std::string name, const std::vector<TypeNode>& params,
                          bool isCo)
    : d_name(name),
      d_params(params),
      d_isCo(isCo),
      d_isTuple(false),
      d_constructors(),
      d_resolved(false),
      d_self(),
      d_involvesExt(false),
      d_involvesUt(false),
      d_sygus_allow_const(false),
      d_sygus_allow_all(false),
      d_card(CardinalityUnknown()),
      d_well_founded(0) {}

inline std::string DType::getName() const { return d_name; }
inline size_t DType::getNumConstructors() const
{
  return d_constructors.size();
}

inline bool DType::isParametric() const { return d_params.size() > 0; }
inline size_t DType::getNumParameters() const { return d_params.size(); }
inline TypeNode DType::getParameter( unsigned int i ) const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameter of a non-parametric datatype.");
  CheckArgument(i < d_params.size(), i,
                "Type parameter index out of range for datatype.");
  return d_params[i];
}

inline std::vector<TypeNode> DType::getParameters() const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameters of a non-parametric datatype.");
  return d_params;
}

inline bool DType::isCodatatype() const {
  return d_isCo;
}

inline bool DType::isSygus() const {
  return !d_sygus_type.isNull();
}

inline bool DType::isTuple() const {
  return d_isTuple;
}

inline bool DType::operator!=(const DType& other) const
{
  return !(*this == other);
}

inline bool DType::isResolved() const { return d_resolved; }
inline DType::iterator DType::begin()
{
  return iterator(d_constructors, true);
}

inline DType::iterator DType::end()
{
  return iterator(d_constructors, false);
}

inline DType::const_iterator DType::begin() const
{
  return const_iterator(d_constructors, true);
}

inline DType::const_iterator DType::end() const
{
  return const_iterator(d_constructors, false);
}

inline bool DTypeConstructor::isResolved() const
{
  return !d_tester.isNull();
}

inline size_t DTypeConstructor::getNumArgs() const { return d_args.size(); }
inline bool DTypeConstructorArg::isResolved() const
{
  // We could just write:
  //
  //   return !d_selector.isNull() && d_selector.getType().isSelector();
  //
  // HOWEVER, this causes problems in NodeManager tear-down, because
  // the attributes are removed before the pool is purged.  When the
  // pool is purged, this triggers an equality test between DTypes,
  // and this triggers a call to isResolved(), which breaks because
  // d_selector has no type after attributes are stripped.
  //
  // This problem, coupled with the fact that this function is called
  // _often_, means we should just use a boolean flag.
  //
  return d_resolved;
}

inline DTypeConstructor::iterator DTypeConstructor::begin()
{
  return iterator(d_args, true);
}

inline DTypeConstructor::iterator DTypeConstructor::end()
{
  return iterator(d_args, false);
}

inline DTypeConstructor::const_iterator DTypeConstructor::begin() const
{
  return const_iterator(d_args, true);
}

inline DTypeConstructor::const_iterator DTypeConstructor::end() const
{
  return const_iterator(d_args, false);
}

}

#endif
