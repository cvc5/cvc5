/*********************                                                        */
/*! \file datatype.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a Datatype definition
 **
 ** A class representing a Datatype definition for the theory of
 ** inductive datatypes.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__DATATYPE_H
#define __CVC4__DATATYPE_H

#include <functional>
#include <iostream>
#include <string>
#include <vector>
#include <map>

namespace CVC4 {
  // messy; Expr needs Datatype (because it's the payload of a
  // CONSTANT-kinded expression), and Datatype needs Expr.
  //class CVC4_PUBLIC Datatype;
  class CVC4_PUBLIC DatatypeIndexConstant;
}/* CVC4 namespace */

#include "base/exception.h"
#include "expr/expr.h"
#include "expr/type.h"
#include "util/hash.h"


namespace CVC4 {

class CVC4_PUBLIC ExprManager;

class CVC4_PUBLIC DatatypeConstructor;
class CVC4_PUBLIC DatatypeConstructorArg;

class CVC4_PUBLIC DatatypeConstructorIterator {
  const std::vector<DatatypeConstructor>* d_v;
  size_t d_i;

  friend class Datatype;

  DatatypeConstructorIterator(const std::vector<DatatypeConstructor>& v, bool start) : d_v(&v), d_i(start ? 0 : v.size()) {
  }

public:
  typedef const DatatypeConstructor& value_type;
  const DatatypeConstructor& operator*() const { return (*d_v)[d_i]; }
  const DatatypeConstructor* operator->() const { return &(*d_v)[d_i]; }
  DatatypeConstructorIterator& operator++() { ++d_i; return *this; }
  DatatypeConstructorIterator operator++(int) { DatatypeConstructorIterator i(*this); ++d_i; return i; }
  bool operator==(const DatatypeConstructorIterator& other) const { return d_v == other.d_v && d_i == other.d_i; }
  bool operator!=(const DatatypeConstructorIterator& other) const { return d_v != other.d_v || d_i != other.d_i; }
};/* class DatatypeConstructorIterator */

class CVC4_PUBLIC DatatypeConstructorArgIterator {
  const std::vector<DatatypeConstructorArg>* d_v;
  size_t d_i;

  friend class DatatypeConstructor;

  DatatypeConstructorArgIterator(const std::vector<DatatypeConstructorArg>& v, bool start) : d_v(&v), d_i(start ? 0 : v.size()) {
  }

public:
  typedef const DatatypeConstructorArg& value_type;
  const DatatypeConstructorArg& operator*() const { return (*d_v)[d_i]; }
  const DatatypeConstructorArg* operator->() const { return &(*d_v)[d_i]; }
  DatatypeConstructorArgIterator& operator++() { ++d_i; return *this; }
  DatatypeConstructorArgIterator operator++(int) { DatatypeConstructorArgIterator i(*this); ++d_i; return i; }
  bool operator==(const DatatypeConstructorArgIterator& other) const { return d_v == other.d_v && d_i == other.d_i; }
  bool operator!=(const DatatypeConstructorArgIterator& other) const { return d_v != other.d_v || d_i != other.d_i; }
};/* class DatatypeConstructorArgIterator */

/**
 * An exception that is thrown when a datatype resolution fails.
 */
class CVC4_PUBLIC DatatypeResolutionException : public Exception {
public:
  inline DatatypeResolutionException(std::string msg);
};/* class DatatypeResolutionException */

/**
 * A holder type (used in calls to DatatypeConstructor::addArg())
 * to allow a Datatype to refer to itself.  Self-typed fields of
 * Datatypes will be properly typed when a Type is created for the
 * Datatype by the ExprManager (which calls Datatype::resolve()).
 */
class CVC4_PUBLIC DatatypeSelfType {
};/* class DatatypeSelfType */

/**
 * An unresolved type (used in calls to
 * DatatypeConstructor::addArg()) to allow a Datatype to refer to
 * itself or to other mutually-recursive Datatypes.  Unresolved-type
 * fields of Datatypes will be properly typed when a Type is created
 * for the Datatype by the ExprManager (which calls
 * Datatype::resolve()).
 */
class CVC4_PUBLIC DatatypeUnresolvedType {
  std::string d_name;
public:
  inline DatatypeUnresolvedType(std::string name);
  inline std::string getName() const throw();
};/* class DatatypeUnresolvedType */

/**
 * A Datatype constructor argument (i.e., a Datatype field).
 */
class CVC4_PUBLIC DatatypeConstructorArg {
  friend class DatatypeConstructor;
  friend class Datatype;
public:

  /** Get the name of this constructor argument. */
  std::string getName() const throw();

  /**
   * Get the selector for this constructor argument; this call is
   * only permitted after resolution.
   */
  Expr getSelector() const;

  /**
   * Get the associated constructor for this constructor argument;
   * this call is only permitted after resolution.
   */
  Expr getConstructor() const;

  /**
   * Get the type of the selector for this constructor argument;
   * this call is only permitted after resolution.
   */
  SelectorType getType() const;

  /**
   * Get the range type of this argument.
   */
  Type getRangeType() const;

  /**
   * Get the name of the type of this constructor argument
   * (Datatype field).  Can be used for not-yet-resolved Datatypes
   * (in which case the name of the unresolved type, or "[self]"
   * for a self-referential type is returned).
   */
  std::string getTypeName() const;

  /**
   * Returns true iff this constructor argument has been resolved.
   */
  bool isResolved() const throw();
private:
  /** the name of this selector */
  std::string d_name;
  /** the selector expression */
  Expr d_selector;
  /** the constructor associated with this selector */
  Expr d_constructor;
  /** whether this class has been resolved */
  bool d_resolved;
  /** is this selector unresolved? */
  bool isUnresolvedSelf() const throw();  
  /** constructor */
  DatatypeConstructorArg(std::string name, Expr selector);
};/* class DatatypeConstructorArg */

/**
 * A constructor for a Datatype.
 */
class CVC4_PUBLIC DatatypeConstructor {
  friend class Datatype;
public:
  /** The type for iterators over constructor arguments. */
  typedef DatatypeConstructorArgIterator iterator;
  /** The (const) type for iterators over constructor arguments. */
  typedef DatatypeConstructorArgIterator const_iterator;

  /**
   * Create a new Datatype constructor with the given name for the
   * constructor and the same name (prefixed with "is_") for the
   * tester.  The actual constructor and tester (meaning, the Exprs
   * representing operators for these entities) aren't created until
   * resolution time.
   */
  explicit DatatypeConstructor(std::string name);

  /**
   * Create a new Datatype constructor with the given name for the
   * constructor and the given name for the tester.  The actual
   * constructor and tester aren't created until resolution time.
   */
  DatatypeConstructor(std::string name, std::string tester);

  /**
   * Add an argument (i.e., a data field) of the given name and type
   * to this Datatype constructor.  Selector names need not be unique;
   * they are for convenience and pretty-printing only.
   */
  void addArg(std::string selectorName, Type selectorType);

  /**
   * Add an argument (i.e., a data field) of the given name to this
   * Datatype constructor that refers to an as-yet-unresolved
   * Datatype (which may be mutually-recursive).  Selector names need
   * not be unique; they are for convenience and pretty-printing only.
   */
  void addArg(std::string selectorName, DatatypeUnresolvedType selectorType);

  /**
   * Add a self-referential (i.e., a data field) of the given name
   * to this Datatype constructor that refers to the enclosing
   * Datatype.  For example, using the familiar "nat" Datatype, to
   * create the "pred" field for "succ" constructor, one uses
   * succ::addArg("pred", DatatypeSelfType())---the actual Type
   * cannot be passed because the Datatype is still under
   * construction.  Selector names need not be unique; they are for
   * convenience and pretty-printing only.
   *
   * This is a special case of
   * DatatypeConstructor::addArg(std::string, DatatypeUnresolvedType).
   */
  void addArg(std::string selectorName, DatatypeSelfType);

  /** Get the name of this Datatype constructor. */
  std::string getName() const throw();

  /**
   * Get the constructor operator of this Datatype constructor.  The
   * Datatype must be resolved.
   */
  Expr getConstructor() const;

  /**
   * Get the tester operator of this Datatype constructor.  The
   * Datatype must be resolved.
   */
  Expr getTester() const;

  /** get sygus op 
   * 
   * This method returns the operator or 
   * term that this constructor represents
   * in the sygus encoding. This may be a
   * builtin operator, defined function, variable, 
   * or constant that this constructor encodes in this 
   * deep embedding.
   */
  Expr getSygusOp() const;
  /** get sygus let body 
   * 
   * The sygus official format 
   * (http://www.sygus.org/SyGuS-COMP2015.html)
   * allows for let expressions to occur in grammars.
   * 
   * TODO (#1344) refactor this
   */
  Expr getSygusLetBody() const;
  /** get number of sygus let args 
   * TODO (#1344) refactor this
   */
  unsigned getNumSygusLetArgs() const;
  /** get sygus let arg 
   * TODO (#1344) refactor this
   */
  Expr getSygusLetArg( unsigned i ) const;
  /** get number of let arguments that should be printed as arguments to let
   * TODO (#1344) refactor this
   */
  unsigned getNumSygusLetInputArgs() const;
  /** is this a sygus identity function?
   * TODO (#1344) refactor this
   */
  bool isSygusIdFunc() const;

  /**
   * Get the tester name for this Datatype constructor.
   */
  std::string getTesterName() const throw();

  /**
   * Get the number of arguments (so far) of this Datatype constructor.
   */
  inline size_t getNumArgs() const throw();

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
  Type getSpecializedConstructorType(Type returnType) const;

  /**
   * Return the cardinality of this constructor (the product of the
   * cardinalities of its arguments).
   */
  Cardinality getCardinality( Type t ) const throw(IllegalArgumentException);

  /**
   * Return true iff this constructor is finite (it is nullary or
   * each of its argument types are finite).  This function can
   * only be called for resolved constructors.
   */
  bool isFinite( Type t ) const throw(IllegalArgumentException);
  /**
   * Return true iff this constructor is finite (it is nullary or
   * each of its argument types are finite) under assumption
   * uninterpreted sorts are finite.  This function can
   * only be called for resolved constructors.
   */
  bool isInterpretedFinite( Type t ) const throw(IllegalArgumentException);

  /**
   * Returns true iff this Datatype constructor has already been
   * resolved.
   */
  inline bool isResolved() const throw();

  /** Get the beginning iterator over DatatypeConstructor args. */
  inline iterator begin() throw();
  /** Get the ending iterator over DatatypeConstructor args. */
  inline iterator end() throw();
  /** Get the beginning const_iterator over DatatypeConstructor args. */
  inline const_iterator begin() const throw();
  /** Get the ending const_iterator over DatatypeConstructor args. */
  inline const_iterator end() const throw();

  /** Get the ith DatatypeConstructor arg. */
  const DatatypeConstructorArg& operator[](size_t index) const;

  /**
   * Get the DatatypeConstructor arg named.  This is a linear search
   * through the arguments, so in the case of multiple,
   * similarly-named arguments, the first is returned.
   */
  const DatatypeConstructorArg& operator[](std::string name) const;

  /**
   * Get the selector named.  This is a linear search
   * through the arguments, so in the case of multiple,
   * similarly-named arguments, the selector for the first
   * is returned.
   */
  Expr getSelector(std::string name) const;


  /** get selector internal
   * 
   * This gets selector for the index^th argument 
   * of this constructor. The type dtt is the datatype 
   * type whose datatype is the owner of this constructor, 
   * where this type may be an instantiated parametric datatype.
   * 
   * If shared selectors are enabled, 
   * this returns a shared (constructor-agnotic) selector, which
   * in the terminology of "Datatypes with Shared Selectors", is:
   *   sel_{dtt}^{T,atos(T,C,index)}
   * where C is this constructor, and T is the type 
   * of the index^th field of this constructor.
   */
  Expr getSelectorInternal( Type dtt, size_t index ) const;
  
  /** get selector index internal
   * 
   * This gets the argument number of this constructor 
   * that the selector sel accesses. It returns -1 if the 
   * selector sel is not a selector for this constructor.
   * 
   * In the terminology of "Datatypes with Shared Selectors", 
   * if sel is sel_{dtt}^{T,index} for some (T, index), where 
   * dtt is the datatype type whose datatype is the owner 
   * of this constructor, then this method returns
   *   stoa(T,C,index)
   */
  int getSelectorIndexInternal( Expr sel ) const;
  
  /** involves external type
   * Get whether this constructor has a subfield 
   * in any constructor that is not a datatype type.
   */
  bool involvesExternalType() const;
  /** involves external type
   * Get whether this constructor has a subfield 
   * in any constructor that is an uninterpreted type.
   */  
  bool involvesUninterpretedType() const;

  /** set sygus
   * 
   * Set that this constructor is a sygus datatype 
   * constructor that encodes operator op.
   * The remaining arguments are for handling 
   * let expressions in user-provided sygus 
   * grammars (see above).
   */
  void setSygus( Expr op, Expr let_body, std::vector< Expr >& let_args, unsigned num_let_input_argus );
private:
  /** the name of the constructor */
  std::string d_name;
  /** the constructor expression */
  Expr d_constructor;
  /** the tester for this constructor */
  Expr d_tester;
  /** the arguments of this constructor */
  std::vector<DatatypeConstructorArg> d_args;
  /** sygus operator */
  Expr d_sygus_op;
  /** sygus let body */
  Expr d_sygus_let_body;
  /** sygus let args */
  std::vector< Expr > d_sygus_let_args;
  /** sygus num let input args */
  unsigned d_sygus_num_let_input_args;
  
  /** shared selectors for each type 
   * This stores the shared (constructor-agnotic) 
   * selectors that access the fields of this datatype.
   * In the terminology of "Datatypes with Shared Selectors", 
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
  mutable std::map< Type, std::vector< Expr > > d_shared_selectors;
  /** for each type, a cache mapping from shared selectors to
   * its argument index for this constructor.
   */
  mutable std::map< Type, std::map< Expr, unsigned > > d_shared_selector_index;
  /** resolve */
  void resolve(ExprManager* em, DatatypeType self,
               const std::map<std::string, DatatypeType>& resolutions,
               const std::vector<Type>& placeholders,
               const std::vector<Type>& replacements,
               const std::vector< SortConstructorType >& paramTypes,
               const std::vector< DatatypeType >& paramReplacements, size_t cindex)
    throw(IllegalArgumentException, DatatypeResolutionException);

  /** Helper function for resolving parametric datatypes.
      This replaces instances of the SortConstructorType produced for unresolved
      parametric datatypes, with the corresponding resolved DatatypeType.  For example, take
      the parametric definition of a list, list[T] = cons(car : T, cdr : list[T]) | null.
      If "range" is the unresolved parametric datatype:
        DATATYPE list = cons(car: SORT_TAG_1, cdr: SORT_TAG_2(SORT_TAG_1)) | null END;,
      this function will return the resolved type:
        DATATYPE list = cons(car: SORT_TAG_1, cdr: (list PARAMETERIC_DATATYPE SORT_TAG_1)) | null END;
    */
  Type doParametricSubstitution(Type range,
                                const std::vector< SortConstructorType >& paramTypes,
                                const std::vector< DatatypeType >& paramReplacements);

  /** compute the cardinality of this datatype */
  Cardinality computeCardinality( Type t, std::vector< Type >& processing ) const throw(IllegalArgumentException);
  /** compute whether this datatype is well-founded */
  bool computeWellFounded( std::vector< Type >& processing ) const throw(IllegalArgumentException);
  /** compute ground term */
  Expr computeGroundTerm( Type t, std::vector< Type >& processing, std::map< Type, Expr >& gt ) const throw(IllegalArgumentException);
  /** compute shared selectors 
   * This computes the maps d_shared_selectors and d_shared_selector_index.
   */
  void computeSharedSelectors( Type domainType ) const;  
};/* class DatatypeConstructor */

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
 * on faith that "list" is a valid type.  We build Datatype objects to
 * describe "tree" and "list", and their constructors and constructor
 * arguments, but leave any unknown types (including self-references)
 * in an "unresolved" state.  After parsing the whole DATATYPE block,
 * we create a DatatypeType through
 * ExprManager::mkMutualDatatypeTypes().  The ExprManager creates a
 * DatatypeType for each, but before "releasing" this type into the
 * wild, it does a round of in-place "resolution" on each Datatype by
 * calling Datatype::resolve() with a map of string -> DatatypeType to
 * allow the datatype to construct the necessary testers and
 * selectors.
 *
 * An additional point to make is that we want to ease the burden on
 * both the parser AND the users of the CVC4 API, so this class takes
 * on the task of generating its own selectors and testers, for
 * instance.  That means that, after reifying the Datatype with the
 * ExprManager, the parser needs to go through the (now-resolved)
 * Datatype and request the constructor, selector, and tester terms.
 * See src/parser/parser.cpp for how this is done.  For API usage
 * ideas, see test/unit/util/datatype_black.h.
 *
 * Datatypes may also be defined parametrically, such as this example:
 *
 *  DATATYPE
 *    list[T] = cons(car : T, cdr : list[T]) | null,
 *    tree = node(children : list[tree]) | leaf
 *  END;
 *
 * Here, the definition of the parametric datatype list, where T is a type variable.
 * In other words, this defines a family of types list[C] where C is any concrete
 * type.  Datatypes can be parameterized over multiple type variables using the
 * syntax sym[ T1, ..., Tn ] = ...,
 *
 */
class CVC4_PUBLIC Datatype {
  friend class DatatypeConstructor;
public:
  /**
   * Get the datatype of a constructor, selector, or tester operator.
   */
  static const Datatype& datatypeOf(Expr item) CVC4_PUBLIC;

  /**
   * Get the index of a constructor or tester in its datatype, or the
   * index of a selector in its constructor.  (Zero is always the
   * first index.)
   */
  static size_t indexOf(Expr item) CVC4_PUBLIC;

  /**
   * Get the index of constructor corresponding to selector.  (Zero is
   * always the first index.)
   */
  static size_t cindexOf(Expr item) CVC4_PUBLIC;

  /** The type for iterators over constructors. */
  typedef DatatypeConstructorIterator iterator;
  /** The (const) type for iterators over constructors. */
  typedef DatatypeConstructorIterator const_iterator;

  /** Create a new Datatype of the given name. */
  inline explicit Datatype(std::string name, bool isCo = false);

  /**
   * Create a new Datatype of the given name, with the given
   * parameterization.
   */
  inline Datatype(std::string name, const std::vector<Type>& params, bool isCo = false);

  ~Datatype();

  /** Add a constructor to this Datatype. 
   * 
   * Notice that constructor names need not
   * be unique; they are for convenience and pretty-printing only.
   */
  void addConstructor(const DatatypeConstructor& c);

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
   * allow_const : whether all constants are (implicitly) allowed by the datatype
   * allow_all : whether all terms are (implicitly) allowed by the datatype
   * 
   * Notice that allow_const/allow_all do not reflect the constructors 
   * for this datatype, and instead are used solely for relaxing constraints 
   * when doing solution reconstruction (Figure 5 of Reynolds et al. 
   * CAV 2015).
   */
  void setSygus( Type st, Expr bvl, bool allow_const, bool allow_all );
  /** add sygus constructor 
   * 
   * This adds a sygus constructor to this datatype, where
   * this datatype should be currently unresolved.
   * 
   * op : the builtin operator, constant, or variable that 
   *      this constructor encodes
   * cname : the name of the constructor (for printing only)
   * cargs : the arguments of the constructor
   * 
   * It should be the case that cargs are sygus datatypes that 
   * encode the arguments of op. For example, a sygus constructor 
   * with op = PLUS should be such that cargs.size()>=2 and 
   * the sygus type of cargs[i] is Real/Int for each i.
   */
  void addSygusConstructor( CVC4::Expr op, std::string& cname, std::vector< CVC4::Type >& cargs );
  /** add sygus constructor (for let expression constructors)
   * 
   * This adds a sygus constructor to this datatype, where
   * this datatype should be currently unresolved.
   * 
   * In contrast to the above function, the constructor we
   * add corresponds to a let expression if let_body is 
   * non-null. For details, see documentation for 
   * DatatypeConstructor::getSygusLetBody above.
   */
  void addSygusConstructor( CVC4::Expr op, std::string& cname, std::vector< CVC4::Type >& cargs,
                            CVC4::Expr& let_body, std::vector< CVC4::Expr >& let_args, unsigned let_num_input_args );
                                    
  /** set that this datatype is a tuple */
  void setTuple();

  /** set that this datatype is a record */
  void setRecord();

  /** Get the name of this Datatype. */
  inline std::string getName() const throw();

  /** Get the number of constructors (so far) for this Datatype. */
  inline size_t getNumConstructors() const throw();

  /** Is this datatype parametric? */
  inline bool isParametric() const throw();

  /** Get the nubmer of type parameters */
  inline size_t getNumParameters() const throw();

  /** Get parameter */
  inline Type getParameter( unsigned int i ) const;

  /** Get parameters */
  inline std::vector<Type> getParameters() const;

  /** is this a co-datatype? */
  inline bool isCodatatype() const;

  /** is this a sygus datatype? */
  inline bool isSygus() const;

  /** is this a tuple datatype? */
  inline bool isTuple() const;

  /** is this a record datatype? */
  inline bool isRecord() const;

  /** get the record representation for this datatype */
  inline Record * getRecord() const;

  /**
   * Return the cardinality of this datatype.  
   * The Datatype must be resolved.
   * 
   * The version of this method that takes Type t is required 
   * for parametric datatypes, where t is an instantiated 
   * parametric datatype type whose datatype is this class.
   */
  Cardinality getCardinality( Type t ) const throw(IllegalArgumentException);
  Cardinality getCardinality() const throw(IllegalArgumentException);

  /**
   * Return true iff this Datatype has finite cardinality. If the
   * datatype is not well-founded, this method returns false. The
   * Datatype must be resolved or an exception is thrown.
   * 
   * The version of this method that takes Type t is required 
   * for parametric datatypes, where t is an instantiated 
   * parametric datatype type whose datatype is this class.
   */
  bool isFinite( Type t ) const throw(IllegalArgumentException);
  bool isFinite() const throw(IllegalArgumentException);
  
  /**
   * Return true iff this  Datatype is finite (all constructors are
   * finite, i.e., there  are finitely  many ground terms) under the
   * assumption unintepreted sorts are finite. If the
   * datatype is  not well-founded, this method returns false.  The
   * Datatype must be resolved or an exception is thrown.
   * 
   * The versions of these methods that takes Type t is required 
   * for parametric datatypes, where t is an instantiated 
   * parametric datatype type whose datatype is this class.
   */
  bool isInterpretedFinite( Type t ) const throw(IllegalArgumentException);
  bool isInterpretedFinite() const throw(IllegalArgumentException);

  /** is well-founded
   * 
   * Return true iff this datatype is well-founded (there exist finite
   * values of this type). 
   * This datatype must be resolved or an exception is thrown.
   */
  bool isWellFounded() const throw(IllegalArgumentException);

  /** is recursive singleton 
   * 
   * Return true iff this datatype is a recursive singleton 
   * (a recursive singleton is a recursive datatype with only 
   * one infinite value). For details, see Reynolds et al. CADE 2015.
   * 
   * The versions of these methods that takes Type t is required 
   * for parametric datatypes, where t is an instantiated 
   * parametric datatype type whose datatype is this class.
   */
  bool isRecursiveSingleton( Type t ) const throw(IllegalArgumentException);
  bool isRecursiveSingleton() const throw(IllegalArgumentException);


  /** recursive single arguments 
   * 
   * Get recursive singleton argument types (uninterpreted sorts that the cardinality 
   * of this datatype is dependent upon). For example, for :
   *   stream :=  cons( head1 : U1, head2 : U2, tail : stream )
   * Then, the recursive singleton argument types of stream are { U1, U2 }, since
   * if U1 and U2 have cardinality one, then stream has cardinality one as well.
   * 
   * The versions of these methods that takes Type t is required 
   * for parametric datatypes, where t is an instantiated 
   * parametric datatype type whose datatype is this class.
  */
  unsigned getNumRecursiveSingletonArgTypes( Type t ) const throw(IllegalArgumentException);
  Type getRecursiveSingletonArgType( Type t, unsigned i ) const throw(IllegalArgumentException);
  unsigned getNumRecursiveSingletonArgTypes() const throw(IllegalArgumentException);
  Type getRecursiveSingletonArgType( unsigned i ) const throw(IllegalArgumentException);

  /**
   * Construct and return a ground term of this Datatype.  The
   * Datatype must be both resolved and well-founded, or else an
   * exception is thrown.
   * 
   * This method takes a Type t, which is a datatype type whose 
   * datatype is this class, which may be an instantiated datatype 
   * type if this datatype is parametric.
   */
  Expr mkGroundTerm( Type t ) const throw(IllegalArgumentException);

  /**
   * Get the DatatypeType associated to this Datatype.  Can only be
   * called post-resolution.
   */
  DatatypeType getDatatypeType() const throw(IllegalArgumentException);

  /**
   * Get the DatatypeType associated to this (parameterized) Datatype.  Can only be
   * called post-resolution.
   */
  DatatypeType getDatatypeType(const std::vector<Type>& params) const throw(IllegalArgumentException);

  /**
   * Return true iff the two Datatypes are the same.
   *
   * We need == for mkConst(Datatype) to properly work---since if the
   * Datatype Expr requested is the same as an already-existing one,
   * we need to return that one.  For that, we have a hash and
   * operator==.  We provide != for symmetry.  We don't provide
   * operator<() etc. because given two Datatype Exprs, you could
   * simply compare those rather than the (bare) Datatypes.  This
   * means, though, that Datatype cannot be stored in a sorted list or
   * RB tree directly, so maybe we can consider adding these
   * comparison operators later on.
   */
  bool operator==(const Datatype& other) const throw();
  /** Return true iff the two Datatypes are not the same. */
  inline bool operator!=(const Datatype& other) const throw();

  /** Return true iff this Datatype has already been resolved. */
  inline bool isResolved() const throw();

  /** Get the beginning iterator over DatatypeConstructors. */
  inline iterator begin() throw();
  /** Get the ending iterator over DatatypeConstructors. */
  inline iterator end() throw();
  /** Get the beginning const_iterator over DatatypeConstructors. */
  inline const_iterator begin() const throw();
  /** Get the ending const_iterator over DatatypeConstructors. */
  inline const_iterator end() const throw();

  /** Get the ith DatatypeConstructor. */
  const DatatypeConstructor& operator[](size_t index) const;

  /**
   * Get the DatatypeConstructor named.  This is a linear search
   * through the constructors, so in the case of multiple,
   * similarly-named constructors, the first is returned.
   */
  const DatatypeConstructor& operator[](std::string name) const;
 
  /**
   * Get the constructor operator for the named constructor.
   * This is a linear search through the constructors, so in
   * the case of multiple, similarly-named constructors, the
   * first is returned.
   *
   * This Datatype must be resolved.
   */
  Expr getConstructor(std::string name) const;

  /** get sygus type 
   * This gets the built-in type associated with
   * this sygus datatype, i.e. the type of the
   * term that this sygus datatype encodes.
   */
  Type getSygusType() const;
  
  /** get sygus var list
   * This gets the variable list of the function
   * to synthesize using this sygus datatype. 
   * For example, if we are synthesizing a binary
   * function f where solutions are of the form: 
   *   f = (\ xy. t[x,y])
   * In this case, this method returns the 
   * bound variable list containing x and y.
   */
  Expr getSygusVarList() const;
  /** get sygus allow constants
   * 
   * Does this sygus datatype allow constants? 
   * Notice that this is not a property of the 
   * constructors of this datatype. Instead, it is
   * pan auxiliary flag (provided in the call
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
  /** get sygus evaluation function
   * 
   * This gets the evaluation function for this datatype 
   * for the deep embedding. This is a function of type:
   *   D x T1 x ... x Tn -> T
   * where:
   *   D is the datatype type for this datatype,
   *   T1...Tn are the types of the variables in 
   *     getSygusVarList(),
   *   T is getSygusType().
   */
  Expr getSygusEvaluationFunc() const;

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
  
private:
  /** name of this datatype */
  std::string d_name;
  /** the type parameters of this datatype (if this is a parametric datatype) 
   */
  std::vector<Type> d_params;
  /** whether the datatype is a codatatype. */
  bool d_isCo;
  /** whether the datatype is a tuple */
  bool d_isTuple;
  /** whether the datatype is a record */
  bool d_isRecord;
  /** the data of the record for this datatype (if applicable) */
  Record * d_record;
  /** the constructors of this datatype */
  std::vector<DatatypeConstructor> d_constructors;
  /** whether this datatype has been resolved */
  bool d_resolved;
  Type d_self;
  /** cache for involves external type */
  bool d_involvesExt;
  /** cache for involves uninterpreted type */
  bool d_involvesUt;
  /** the builtin type that this sygus type encodes */
  Type d_sygus_type;
  /** the variable list for the sygus function to synthesize */
  Expr d_sygus_bvl;
  /** whether all constants are allowed as solutions */
  bool d_sygus_allow_const;
  /** whether all terms are allowed as solutions */
  bool d_sygus_allow_all;
  /** the evaluation function for this sygus datatype */
  Expr d_sygus_eval;

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
  mutable std::map< Type, int > d_card_rec_singleton;
  /** if d_card_rec_singleton is true,
  * This datatype has infinite cardinality if at least one of the 
  * following uninterpreted sorts having cardinality > 1.
  */
  mutable std::map< Type, std::vector< Type > > d_card_u_assume;
  /** cache of whether this datatype is well-founded */
  mutable int d_well_founded;
  /** cache of ground term for this datatype */
  mutable std::map< Type, Expr > d_ground_term;
  /** cache of shared selectors for this datatype */
  mutable std::map< Type, std::map< Type, std::map< unsigned, Expr > > > d_shared_sel;

  /**
   * Datatypes refer to themselves, recursively, and we have a
   * chicken-and-egg problem.  The DatatypeType around the Datatype
   * cannot exist until the Datatype is finalized, and the Datatype
   * cannot refer to the DatatypeType representing itself until it
   * exists.  resolve() is called by the ExprManager when a Type is
   * ultimately requested of the Datatype specification (that is, when
   * ExprManager::mkDatatypeType() or ExprManager::mkMutualDatatypeTypes()
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
   * @param em the ExprManager at play
   * @param resolutions a map of strings to DatatypeTypes currently under resolution
   * @param placeholders the types in these Datatypes under resolution that must be replaced
   * @param replacements the corresponding replacements
   * @param paramTypes the sort constructors in these Datatypes under resolution that must be replaced
   * @param paramReplacements the corresponding (parametric) DatatypeTypes
   */
  void resolve(ExprManager* em,
               const std::map<std::string, DatatypeType>& resolutions,
               const std::vector<Type>& placeholders,
               const std::vector<Type>& replacements,
               const std::vector< SortConstructorType >& paramTypes,
               const std::vector< DatatypeType >& paramReplacements)
    throw(IllegalArgumentException, DatatypeResolutionException);
  friend class ExprManager;// for access to resolve()

  /** compute the cardinality of this datatype */
  Cardinality computeCardinality( Type t, std::vector< Type >& processing ) const throw(IllegalArgumentException);
  /** compute whether this datatype is a recursive singleton */
  bool computeCardinalityRecSingleton( Type t, std::vector< Type >& processing, std::vector< Type >& u_assume ) const throw(IllegalArgumentException);
  /** compute whether this datatype is well-founded */
  bool computeWellFounded( std::vector< Type >& processing ) const throw(IllegalArgumentException);
  /** compute ground term */
  Expr computeGroundTerm( Type t, std::vector< Type >& processing ) const throw(IllegalArgumentException);  
  /** Get the shared selector 
   * 
   * This returns the index^th (constructor-agnostic)
   * selector for type t. The type dtt is the datatype 
   * type whose datatype is this class, where this may 
   * be an instantiated parametric datatype.
   * 
   * In the terminology of "Datatypes with Shared Selectors", 
   * this returns the term sel_{dtt}^{t,index}.
   */
  Expr getSharedSelector( Type dtt, Type t, unsigned index ) const;
};/* class Datatype */

/**
 * A hash function for Datatypes.  Needed to store them in hash sets
 * and hash maps.
 */
struct CVC4_PUBLIC DatatypeHashFunction {
  inline size_t operator()(const Datatype& dt) const {
    return std::hash<std::string>()(dt.getName());
  }
  inline size_t operator()(const Datatype* dt) const {
    return std::hash<std::string>()(dt->getName());
  }
  inline size_t operator()(const DatatypeConstructor& dtc) const {
    return std::hash<std::string>()(dtc.getName());
  }
  inline size_t operator()(const DatatypeConstructor* dtc) const {
    return std::hash<std::string>()(dtc->getName());
  }
};/* struct DatatypeHashFunction */



/* stores an index to Datatype residing in NodeManager */
class CVC4_PUBLIC DatatypeIndexConstant {
public:

  DatatypeIndexConstant(unsigned index) throw(IllegalArgumentException);

  ~DatatypeIndexConstant() throw() { }

  const unsigned getIndex() const throw() {
    return d_index;
  }
  bool operator==(const DatatypeIndexConstant& uc) const throw() {
    return d_index == uc.d_index;
  }
  bool operator!=(const DatatypeIndexConstant& uc) const throw() {
    return !(*this == uc);
  }
  bool operator<(const DatatypeIndexConstant& uc) const throw() {
    return d_index < uc.d_index;
  }
  bool operator<=(const DatatypeIndexConstant& uc) const throw() {
    return d_index <= uc.d_index;
  }
  bool operator>(const DatatypeIndexConstant& uc) const throw() {
    return !(*this <= uc);
  }
  bool operator>=(const DatatypeIndexConstant& uc) const throw() {
    return !(*this < uc);
  }
private:
  const unsigned d_index;
};/* class DatatypeIndexConstant */

std::ostream& operator<<(std::ostream& out, const DatatypeIndexConstant& dic) CVC4_PUBLIC;

struct CVC4_PUBLIC DatatypeIndexConstantHashFunction {
  inline size_t operator()(const DatatypeIndexConstant& dic) const {
    return IntegerHashFunction()(dic.getIndex());
  }
};/* struct DatatypeIndexConstantHashFunction */



// FUNCTION DECLARATIONS FOR OUTPUT STREAMS

std::ostream& operator<<(std::ostream& os, const Datatype& dt) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const DatatypeConstructor& ctor) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& os, const DatatypeConstructorArg& arg) CVC4_PUBLIC;

// INLINE FUNCTIONS

inline DatatypeResolutionException::DatatypeResolutionException(std::string msg) :
  Exception(msg) {
}

inline DatatypeUnresolvedType::DatatypeUnresolvedType(std::string name) :
  d_name(name) {
}

inline std::string DatatypeUnresolvedType::getName() const throw() {
  return d_name;
}

inline Datatype::Datatype(std::string name, bool isCo) :
  d_name(name),
  d_params(),
  d_isCo(isCo),
  d_isTuple(false),
  d_isRecord(false),
  d_record(NULL),
  d_constructors(),
  d_resolved(false),
  d_self(),
  d_involvesExt(false),
  d_involvesUt(false),
  d_card(CardinalityUnknown()),
  d_well_founded(0) {
}

inline Datatype::Datatype(std::string name, const std::vector<Type>& params, bool isCo) :
  d_name(name),
  d_params(params),
  d_isCo(isCo),
  d_isTuple(false),
  d_isRecord(false),
  d_record(NULL),
  d_constructors(),
  d_resolved(false),
  d_self(),
  d_involvesExt(false),
  d_involvesUt(false),
  d_card(CardinalityUnknown()),
  d_well_founded(0) {
}

inline std::string Datatype::getName() const throw() {
  return d_name;
}

inline size_t Datatype::getNumConstructors() const throw() {
  return d_constructors.size();
}

inline bool Datatype::isParametric() const throw() {
  return d_params.size() > 0;
}

inline size_t Datatype::getNumParameters() const throw() {
  return d_params.size();
}

inline Type Datatype::getParameter( unsigned int i ) const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameter of a non-parametric datatype.");
  CheckArgument(i < d_params.size(), i,
                "Type parameter index out of range for datatype.");
  return d_params[i];
}

inline std::vector<Type> Datatype::getParameters() const {
  CheckArgument(isParametric(), this,
                "Cannot get type parameters of a non-parametric datatype.");
  return d_params;
}

inline bool Datatype::isCodatatype() const {
  return d_isCo;
}

inline bool Datatype::isSygus() const {
  return !d_sygus_type.isNull();
}

inline bool Datatype::isTuple() const {
  return d_isTuple;
}

inline bool Datatype::isRecord() const {
  return d_isRecord;
}

inline Record * Datatype::getRecord() const {
  return d_record;
}

inline bool Datatype::operator!=(const Datatype& other) const throw() {
  return !(*this == other);
}

inline bool Datatype::isResolved() const throw() {
  return d_resolved;
}

inline Datatype::iterator Datatype::begin() throw() {
  return iterator(d_constructors, true);
}

inline Datatype::iterator Datatype::end() throw() {
  return iterator(d_constructors, false);
}

inline Datatype::const_iterator Datatype::begin() const throw() {
  return const_iterator(d_constructors, true);
}

inline Datatype::const_iterator Datatype::end() const throw() {
  return const_iterator(d_constructors, false);
}

inline bool DatatypeConstructor::isResolved() const throw() {
  return !d_tester.isNull();
}

inline size_t DatatypeConstructor::getNumArgs() const throw() {
  return d_args.size();
}

inline bool DatatypeConstructorArg::isResolved() const throw() {
  // We could just write:
  //
  //   return !d_selector.isNull() && d_selector.getType().isSelector();
  //
  // HOWEVER, this causes problems in ExprManager tear-down, because
  // the attributes are removed before the pool is purged.  When the
  // pool is purged, this triggers an equality test between Datatypes,
  // and this triggers a call to isResolved(), which breaks because
  // d_selector has no type after attributes are stripped.
  //
  // This problem, coupled with the fact that this function is called
  // _often_, means we should just use a boolean flag.
  //
  return d_resolved;
}

inline DatatypeConstructor::iterator DatatypeConstructor::begin() throw() {
  return iterator(d_args, true);
}

inline DatatypeConstructor::iterator DatatypeConstructor::end() throw() {
  return iterator(d_args, false);
}

inline DatatypeConstructor::const_iterator DatatypeConstructor::begin() const throw() {
  return const_iterator(d_args, true);
}

inline DatatypeConstructor::const_iterator DatatypeConstructor::end() const throw() {
  return const_iterator(d_args, false);
}

}/* CVC4 namespace */

#endif /* __CVC4__DATATYPE_H */
