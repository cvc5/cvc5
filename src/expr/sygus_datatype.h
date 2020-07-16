/*********************                                                        */
/*! \file sygus_datatype.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
 * Information necessary to specify a sygus constructor. Further detail on these
 * fields can be found in SygusDatatype below.
 */
class SygusDatatypeConstructor
{
 public:
  /** The operator that the constructor encodes. */
  Node d_op;
  /** Name of the constructor. */
  std::string d_name;
  /** List of argument types. */
  std::vector<TypeNode> d_argTypes;
  /** Weight of the constructor. */
  int d_weight;
};

/**
 * Keeps the necessary information for initializing a sygus datatype, which
 * includes the operators, names, print callbacks and list of argument types
 * for each constructor.
 *
 * It also maintains a datatype to represent the structure of the type node.
 *
 * Notice that this class is only responsible for setting SyGuS-related
 * information regarding the datatype. It is still required that the user
 * of this class construct the datatype type corresponding to the datatype
 * e.g. via a call to ExprManager::mkMutualDatatypeTypes().
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
   * argTypes: the argument types of the constructor (typically other sygus
   * datatype types).
   * spc: the print callback (for custom printing of this node),
   * weight: the weight of this constructor.
   *
   * It should be the case that argTypes are sygus datatype types (possibly
   * unresolved) that encode the arguments of the builtin operator. That is,
   * if op is the builtin PLUS operator, then argTypes could contain 2+
   * sygus datatype types that encode integer.
   */
  void addConstructor(Node op,
                      const std::string& name,
                      const std::vector<TypeNode>& argTypes,
                      int weight = -1);
  /**
   * Add constructor that encodes an application of builtin kind k. Like above,
   * the arguments argTypes should correspond to sygus datatypes that encode
   * the types of the arguments of the kind.
   */
  void addConstructor(Kind k,
                      const std::vector<TypeNode>& argTypes,
                      int weight = -1);
  /**
   * This adds a constructor that corresponds to the any constant constructor
   * for the given (builtin) type tn.
   */
  void addAnyConstantConstructor(TypeNode tn);

  /** Get the number of constructors added to this class so far */
  size_t getNumConstructors() const;

  /** Get constructor at index i */
  const SygusDatatypeConstructor& getConstructor(unsigned i) const;

  /** builds a datatype with the information in the type object
   *
   * sygusType: the builtin type that this datatype encodes,
   * sygusVars: the formal argument list of the function-to-synthesize,
   * allowConst: whether the grammar corresponding to this datatype allows
   * any constant,
   * allowAll: whether the grammar corresponding to this datatype allows
   * any term.
   */
  void initializeDatatype(TypeNode sygusType,
                          Node sygusVars,
                          bool allowConst,
                          bool allowAll);
  /** Get the sygus datatype initialized by this class */
  const Datatype& getDatatype() const;

  /** is initialized */
  bool isInitialized() const;

 private:
  /** Information for each constructor. */
  std::vector<SygusDatatypeConstructor> d_cons;
  /** Datatype to represent type's structure */
  Datatype d_dt;
};

}  // namespace CVC4

#endif
