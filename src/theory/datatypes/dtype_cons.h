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

#ifndef CVC4__THEORY__DATATYPES__DTYPE_CONS_H
#define CVC4__THEORY__DATATYPES__DTYPE_CONS_H

#include <map>
#include <string>
#include <vector>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/datatypes/dtype_cons_arg.h"

namespace CVC4 {

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

class DatatypeConstructor;

/**
 * A constructor for a DType.
 */
class DTypeConstructor
{
  friend class DatatypeConstructor;
  friend class DType;

 public:
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
  DTypeConstructor(std::string name, std::string tester, unsigned weight = 1);

  ~DTypeConstructor() {}
  /**
   * Add an argument (i.e., a data field) of the given name and type
   * to this DType constructor.  Selector names need not be unique;
   * they are for convenience and pretty-printing only.
   */
  void addArg(std::string selectorName, TypeNode selectorType);
  void addArg(const DTypeConstructorArg& a);

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

  /**
   * Get the tester name for this DType constructor.
   */
  std::string getTesterName() const;
  //-------------------------------------- sygus
  /** set sygus
   *
   * Set that this constructor is a sygus datatype constructor that encodes
   * operator op. spc is the sygus callback of this datatype constructor,
   * which is stored in a shared pointer.
   */
  void setSygus(Node op, std::shared_ptr<SygusPrintCallbackInternal> spc);
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
  std::shared_ptr<SygusPrintCallbackInternal> getSygusPrintCallbackInternal()
      const;
  /** get weight
   *
   * Get the weight of this constructor. This value is used when computing the
   * size of datatype terms that involve this constructor.
   */
  unsigned getWeight() const;
  //-------------------------------------- end sygus

  /**
   * Get the number of arguments (so far) of this DType constructor.
   */
  size_t getNumArgs() const;
  /**
   * Get the list of arguments to this constructor.
   */
  const std::vector<DTypeConstructorArg>* getArgs() const;
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
  bool isResolved() const;

  /** Get the ith DTypeConstructor arg. */
  const DTypeConstructorArg& operator[](size_t index) const;

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
  int getSelectorIndexInternal(Node sel) const;

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
  bool resolve(TypeNode self,
               const std::map<std::string, TypeNode>& resolutions,
               const std::vector<TypeNode>& placeholders,
               const std::vector<TypeNode>& replacements,
               const std::vector<TypeNode>& paramTypes,
               const std::vector<TypeNode>& paramReplacements,
               size_t cindex);

  /** Helper function for resolving parametric datatypes.
   *
   * This replaces instances of the TypeNode produced for unresolved
   * parametric datatypes, with the corresponding resolved TypeNode.  For
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
      const std::vector<TypeNode>& paramTypes,
      const std::vector<TypeNode>& paramReplacements);

  /** compute the cardinality of this datatype */
  Cardinality computeCardinality(TypeNode t,
                                 std::vector<TypeNode>& processing) const;
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
}; /* class DTypeConstructor */

std::ostream& operator<<(std::ostream& os, const DTypeConstructor& ctor);

}  // namespace CVC4

#endif
