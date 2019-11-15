/*********************                                                        */
/*! \file sygus_datatype.h
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

#ifndef CVC4__EXPR__SYGUS_DATATYPE_H
#define CVC4__EXPR__SYGUS_DATATYPE_H

#include <string>
#include <vector>

#include "expr/attribute.h"
#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

/** Attribute true for variables that represent any constant */
struct SygusAnyConstAttributeId
{
};
typedef expr::Attribute<SygusAnyConstAttributeId, bool> SygusAnyConstAttribute;

/**
 * Keeps the necessary information for bulding a sygus datatype, which includes
 * the operators, names, print callbacks and list of argument types for each
 * constructor.
 *
 * It also maintains a datatype to represent the structure of the type node.
 */
class SygusDatatype
{
 public:
  /** constructor */
  SygusDatatype(const std::string& name);
  ~SygusDatatype() {}
  /** get the name of this datatype */
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
   * 
   * The argument prepend is if we wish to add the constructor to the
   * beginning of the list of constructors.
   */
  void addConstructor(Node op,
                      const std::string& name,
                      std::shared_ptr<SygusPrintCallback> spc,
                      int weight,
                      const std::vector<TypeNode>& consTypes,
                      bool prepend = false);
  /**
   * This adds a constructor that corresponds to the any constant constructor
   * for the given (builtin) type tn.
   */
  void addAnyConstantConstructor(TypeNode tn,
                                bool prepend = false);

  /** builds a datatype with the information in the type object
   *
   * sygusType: the builtin type that this datatype encodes,
   * sygusVars: the formal argument list of the function-to-synthesize,
   * allowConst: whether the grammar corresponding to this datatype allows
   * any constant,
   * allowAll: whether the grammar corresponding to this datatype allows
   * any term.
   */
  void buildDatatype(TypeNode sygusType,
                     Node sygusVars,
                     bool allowConst,
                     bool allowAll);
  /** Get the sygus datatype built by this class */
  const Datatype& getDatatype() const;

 private:
  //---------- information to build normalized type node
  /** Operators for each constructor. */
  std::vector<Node> d_ops;
  /** Names for each constructor. */
  std::vector<std::string> d_cons_names;
  /** Print callbacks for each constructor */
  std::vector<std::shared_ptr<SygusPrintCallback>> d_pc;
  /** Weights for each constructor */
  std::vector<int> d_weight;
  /** List of argument types for each constructor */
  std::vector<std::vector<TypeNode>> d_consArgs;
  /** Datatype to represent type's structure */
  Datatype d_dt;
};

}  // namespace CVC4

#endif
