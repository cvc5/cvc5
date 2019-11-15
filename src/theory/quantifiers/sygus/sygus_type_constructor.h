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

#ifndef CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H
#define CVC4__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_NORM_H

#include <map>
#include <memory>
#include <string>
#include <vector>

#include "expr/datatype.h"
#include "expr/node.h"
#include "expr/node_manager_attributes.h"  // for VarNameAttr
#include "expr/type.h"
#include "expr/type_node.h"
#include "theory/quantifiers/term_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {


/** Keeps the necessary information for bulding a normalized type:
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

  /** adds information in "cons" (operator, name, print callback, argument
    * types) as it is into "to"
    *
    * A side effect of this procedure is to expand the definitions in the sygus
    * operator of "cons"
    *
    * The types of the arguments of "cons" are recursively normalized
    */
  void addConsInfo(SygusGrammarNorm* sygus_norm,
                    const DatatypeConstructor& cons);
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

  /** builds a datatype with the information in the type object
    *
    * "dt" is the datatype of the original typenode. It is necessary for
    * retrieving ancillary information during the datatype building, such as
    * its sygus type (e.g. Int)
    *
    * The built datatype and its unresolved type are saved in the global
    * accumulators of "sygus_norm"
    */
  void buildDatatype(SygusGrammarNorm* sygus_norm, const Datatype& dt);

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
  std::vector<std::vector<Type>> d_cons_args_t;
  /* Unresolved type node placeholder */
  TypeNode d_unres_tn;
  /* Datatype to represent type's structure */
  Datatype d_dt;
}; /* class SygusTypeConstructor */


}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif
