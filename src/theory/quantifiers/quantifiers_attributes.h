/*********************                                                        */
/*! \file quantifiers_attributes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Attributes for the theory quantifiers
 **
 ** Attributes for the theory quantifiers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H

#include "expr/attribute.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** Attribute true for function definition quantifiers */
struct FunDefAttributeId {};
typedef expr::Attribute< FunDefAttributeId, bool > FunDefAttribute;

/** Attribute true for quantifiers that we are doing quantifier elimination on */
struct QuantElimAttributeId {};
typedef expr::Attribute< QuantElimAttributeId, bool > QuantElimAttribute;

/** Attribute true for quantifiers that we are doing partial quantifier elimination on */
struct QuantElimPartialAttributeId {};
typedef expr::Attribute< QuantElimPartialAttributeId, bool > QuantElimPartialAttribute;

/** Attribute true for quantifiers that are SyGus conjectures */
struct SygusAttributeId {};
typedef expr::Attribute< SygusAttributeId, bool > SygusAttribute;

/**Attribute to give names to quantified formulas */
struct QuantNameAttributeId
{
};
typedef expr::Attribute<QuantNameAttributeId, bool> QuantNameAttribute;

struct InstLevelAttributeId
{
};
typedef expr::Attribute<InstLevelAttributeId, uint64_t> InstLevelAttribute;

/** Attribute for setting printing information for sygus variables
 *
 * For variable d of sygus datatype type, if
 * d.getAttribute(SygusPrintProxyAttribute) = t, then printing d will print t.
 */
struct SygusPrintProxyAttributeId
{
};
typedef expr::Attribute<SygusPrintProxyAttributeId, Node>
    SygusPrintProxyAttribute;

/** Attribute for specifying a "side condition" for a sygus conjecture
 *
 * A sygus conjecture of the form exists f. forall x. P[f,x] whose side
 * condition is C[f] has the semantics exists f. C[f] ^ forall x. P[f,x].
 */
struct SygusSideConditionAttributeId
{
};
typedef expr::Attribute<SygusSideConditionAttributeId, Node>
    SygusSideConditionAttribute;

/** Attribute for indicating that a sygus variable encodes a term
 *
 * This is used, e.g., for abduction where the formal argument list of the
 * abduct-to-synthesize corresponds to the free variables of the sygus
 * problem.
 */
struct SygusVarToTermAttributeId
{
};
typedef expr::Attribute<SygusVarToTermAttributeId, Node>
    SygusVarToTermAttribute;

/**
 * Attribute marked true for types that are used as abstraction types in
 * the finite model finding for function definitions algorithm.
 */
struct AbsTypeFunDefAttributeId
{
};
typedef expr::Attribute<AbsTypeFunDefAttributeId, bool> AbsTypeFunDefAttribute;

/**
 * Attribute true for quantifiers that have been internally generated, e.g.
 * for reductions of string operators.
 *
 * Currently, this attribute is used for indicating that E-matching should
 * not be applied, as E-matching should not be applied to quantifiers
 * generated for strings reductions.
 *
 * This attribute can potentially be generalized to an identifier indicating
 * the internal source of the quantified formula (of which strings reduction
 * is one possibility).
 */
struct InternalQuantAttributeId
{
};
typedef expr::Attribute<InternalQuantAttributeId, bool> InternalQuantAttribute;

namespace quantifiers {

/** This struct stores attributes for a single quantified formula */
struct QAttributes
{
 public:
  QAttributes()
      : d_hasPattern(false),
        d_sygus(false),
        d_qinstLevel(-1),
        d_quant_elim(false),
        d_quant_elim_partial(false),
        d_isInternal(false)
  {
  }
  ~QAttributes(){}
  /** does the quantified formula have a pattern? */
  bool d_hasPattern;
  /** if non-null, this quantified formula is a function definition for function
   * d_fundef_f */
  Node d_fundef_f;
  /** is this formula marked as a sygus conjecture? */
  bool d_sygus;
  /** side condition for sygus conjectures */
  Node d_sygusSideCondition;
  /** stores the maximum instantiation level allowed for this quantified formula
   * (-1 means allow any) */
  int d_qinstLevel;
  /** is this formula marked for quantifier elimination? */
  bool d_quant_elim;
  /** is this formula marked for partial quantifier elimination? */
  bool d_quant_elim_partial;
  /** Is this formula internally generated? */
  bool d_isInternal;
  /** the instantiation pattern list for this quantified formula (its 3rd child)
   */
  Node d_ipl;
  /** The name of this quantified formula, used for :qid */
  Node d_name;
  /** The (internal) quantifier id associated with this formula */
  Node d_qid_num;
  /** is this quantified formula a function definition? */
  bool isFunDef() const { return !d_fundef_f.isNull(); }
  /**
   * Is this a standard quantifier? A standard quantifier is one that we can
   * perform destructive updates (variable elimination, miniscoping, etc).
   *
   * A quantified formula is not standard if it is sygus, one for which
   * we are performing quantifier elimination, is a function definition, or
   * has a name.
   */
  bool isStandard() const;
};

/** This class caches information about attributes of quantified formulas
*
* It also has static utility functions used for determining attributes and
* information about
* quantified formulas.
*/
class QuantAttributes
{
public:
  QuantAttributes( QuantifiersEngine * qe );
  ~QuantAttributes(){}
  /** set user attribute
  * This function applies an attribute
  * This can be called when we mark expressions with attributes, e.g. (! q
  * :attribute attr [node_values, str_value...]),
  * It can also be called internally in various ways (for SyGus, quantifier
  * elimination, etc.)
  */
  static void setUserAttribute(const std::string& attr,
                               Node q,
                               std::vector<Node>& node_values,
                               std::string str_value);

  /** compute quantifier attributes */
  static void computeQuantAttributes(Node q, QAttributes& qa);
  /** compute the attributes for q */
  void computeAttributes(Node q);

  /** is fun def */
  static bool checkFunDef( Node q );
  /** is fun def */
  static bool checkFunDefAnnotation( Node ipl );
  /** is sygus conjecture */
  static bool checkSygusConjecture( Node q );
  /** is sygus conjecture */
  static bool checkSygusConjectureAnnotation( Node ipl );
  /** get fun def body */
  static Node getFunDefHead( Node q );
  /** get fun def body */
  static Node getFunDefBody( Node q );
  /** is quant elim annotation */
  static bool checkQuantElimAnnotation( Node ipl );

  /** is function definition */
  bool isFunDef( Node q );
  /** is sygus conjecture */
  bool isSygus( Node q );
  /** get instantiation level */
  int getQuantInstLevel( Node q );
  /** is quant elim */
  bool isQuantElim( Node q );
  /** is quant elim partial */
  bool isQuantElimPartial( Node q );
  /** is internal quantifier */
  bool isInternal(Node q) const;
  /** get quant name, which is used for :qid */
  Node getQuantName(Node q) const;
  /** get (internal) quant id num */
  int getQuantIdNum( Node q );
  /** get (internal)quant id num */
  Node getQuantIdNumNode( Node q );

  /** set instantiation level attr */
  static void setInstantiationLevelAttr(Node n, uint64_t level);
  /** set instantiation level attr */
  static void setInstantiationLevelAttr(Node n, Node qn, uint64_t level);

 private:
  /** pointer to quantifiers engine */
  QuantifiersEngine * d_quantEngine;
  /** cache of attributes */
  std::map< Node, QAttributes > d_qattr;
  /** function definitions */
  std::map< Node, bool > d_fun_defs;
};

}
}
}

#endif
