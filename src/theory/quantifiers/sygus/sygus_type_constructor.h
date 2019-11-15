/*********************                                                        */
/*! \file sygus_type_constructor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class for constructing SyGuS datatypes.
 **/
#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_TYPE_CONSTRUCTOR_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_TYPE_CONSTRUCTOR_H

#include <string>
#include <vector>

#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/type_node.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {
  
/** Attribute true for variables that represent any constant */
struct SygusAnyConstAttributeId
{
};
typedef expr::Attribute<SygusAnyConstAttributeId, bool> SygusAnyConstAttribute;
  
namespace quantifiers {

/** 
 * Keeps the necessary information for bulding a sygus type, which includes
 * the operators, names, print callbacks and list of argument types for each
 * constructor.
 *
 * It also maintains a datatype to represent the structure of the type node.
 */
class SygusTypeConstructor
{
 public:
  /* Stores the original type node and the unresolved placeholder. The
   * datatype for the latter is created with the respective name. */
  SygusTypeConstructor(const std::string& name);
  ~SygusTypeConstructor() {}
  /** get name */
  std::string getName() const;
  /**
   * Add constructor that encodes an application of builtin operator op.
   * 
   * op: the builtin operator,
   * name: the name of the constructor,
   * spc: the print callback (for custom printing of this node),
   * weight: the weight of this constructor,
   * consTypes: the argument types of the constructor (typically other sygus
   * datatype types).
   */
  void addConstructor(Node op,
                                       const std::string& name,
                                       std::shared_ptr<SygusPrintCallback> spc,
                                       int weight,
                                       const std::vector<TypeNode>& consTypes);
  /**
   * This adds a constructor that corresponds to the any constant constructor
   * for the given (builtin) type tn.
   */
  void addAnyConstantConstructor(TypeNode tn);

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
  void buildDatatype(TypeNode sygusType,
                                         Node sygusVars,
                                         bool allowConst,
                                         bool allowAll);
  /** Get the sygus datatype built by this class */
  const Datatype& getDatatype() const;
private:
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
  std::vector<std::vector<TypeNode>> d_consArgs;
  /* Datatype to represent type's structure */
  Datatype d_dt;
}; /* class SygusTypeConstructor */

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
