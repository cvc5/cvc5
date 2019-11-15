/*********************                                                        */
/*! \file sygus_type_constructor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief class for simplifying SyGuS grammars after they are encoded into
 ** datatypes.
 **/
#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_TYPE_CONSTRUCTOR_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_TYPE_CONSTRUCTOR_H

#include <string>
#include <vector>

#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Keeps the necessary information for bulding a sygus type:
 *
 * the original typenode, from which the datatype representation can be
 * extracted
 *
 * the operators, names, print callbacks and list of argument types for each
 * constructor
 *
 * the unresolved type node used as placeholder for references of the yet to
 * be built normalized type
 *
 * a datatype to represent the structure of the type node for the normalized
 * type
 */
class SygusTypeConstructor
{
 public:
  /* Stores the original type node and the unresolved placeholder. The
   * datatype for the latter is created with the respective name. */
  SygusTypeConstructor(TypeNode src_tn, TypeNode unres_tn);
  ~SygusTypeConstructor() {}

  /**
   * Adds information in "cons" (operator, name, print callback, argument
   * types) as it is into this type constructor.
   *
   * The argument types of the constructor are overidden to the provided
   * argument consTypes.
   */
  void addConsInfo(const DatatypeConstructor& cons,
                   std::vector<TypeNode>& consTypes);
  /**
   * This adds a constructor that corresponds to the any constant constructor
   * for the given (builtin) type tn.
   */
  void addAnyConstantConstructor(TypeNode tn);
  //------------------------- utilities for eliminating partial operators
  /**
   * Returns the total version of Kind k if it is a partial operator, or
   * otherwise k itself.
   */
  static Kind getEliminateKind(Kind k);
  /**
   * Returns a version of n where all partial functions such as bvudiv
   * have been replaced by their total versions like bvudiv_total.
   */
  static Node eliminatePartialOperators(Node n);
  //------------------------- end utilities for eliminating partial operators

  /** builds a datatype with the information in the type object
   *
   * "dt" is the datatype of the original typenode. It is necessary for
   * retrieving ancillary information during the datatype building, such as
   * its sygus type (e.g. Int). The argument sygusVars overrides the set of
   * sygus variables of dt (which correspond to the formal argument list of
   * a function-to-synthesize).
   *
   * The built datatype and its unresolved type are added to the vectors
   * dts and unres respectively.
   */
  void buildDatatype(Node sygusVars,
                     const Datatype& dt,
                     std::vector<Datatype>& dts,
                     std::vector<TypeNode>& unres);

  //---------- information stored from original type node

  /* The original typenode this SygusTypeConstructor is built from */
  TypeNode d_tn;

  //---------- information to build normalized type node

  /* Operators for each constructor. */
  std::vector<Node> d_ops;
  /* Names for each constructor. */
  std::vector<std::string> d_cons_names;
  /* Print callbacks for each constructor */
  std::vector<std::shared_ptr<SygusPrintCallback>> d_pc;
  /* Weights for each constructor */
  std::vector<int> d_weight;
  /* List of argument types for each constructor */
  std::vector<std::vector<TypeNode>> d_cons_args_t;
  /* Unresolved type node placeholder */
  TypeNode d_unres_tn;
  /* Datatype to represent type's structure */
  Datatype d_dt;
}; /* class SygusTypeConstructor */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
