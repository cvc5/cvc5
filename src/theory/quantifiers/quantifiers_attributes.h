/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Attributes for the theory quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H

#include "expr/attribute.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {

/** Attribute true for function definition quantifiers */
struct FunDefAttributeId {};
typedef expr::Attribute< FunDefAttributeId, bool > FunDefAttribute;

/** Attribute true for quantifiers that we are doing partial quantifier elimination on */
struct QuantElimPartialAttributeId {};
typedef expr::Attribute< QuantElimPartialAttributeId, bool > QuantElimPartialAttribute;

/** Attribute true for quantifiers that are SyGus conjectures */
struct SygusAttributeId {};
typedef expr::Attribute< SygusAttributeId, bool > SygusAttribute;

/**
 * Attribute set to the name of the binary for quantifiers that are oracle
 * interfaces. In detail, an oracle interface is a quantified formula of the
 * form:
 *   (FORALL
 *     (BOUND_VAR_LIST i1 ... in o1 ... om)
 *     (ORACLE_FORMULA_GEN A C)
 *     (INST_PATTERN_LIST k))
 * where i1 ... in are the inputs to the interface, o1 ... om are the outputs
 * of the interface, A is the "assumption" formula, C is the "constraint"
 * formula, and k is a dummy skolem that has been marked with this attribute.
 * The string value of this attribute specifies a binary whose I/O behavior
 * should match the types of inputs and outputs specified by i1 ... in and
 * o1 ... om respectively.
 */
struct OracleInterfaceAttributeId
{
};
typedef expr::Attribute<OracleInterfaceAttributeId, Node>
    OracleInterfaceAttribute;

/**Attribute to give names to quantified formulas */
struct QuantNameAttributeId
{
};
typedef expr::Attribute<QuantNameAttributeId, bool> QuantNameAttribute;

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

namespace quantifiers {

/** This struct stores attributes for a single quantified formula */
struct QAttributes
{
 public:
  QAttributes()
      : d_hasPattern(false),
        d_hasPool(false),
        d_sygus(false),
        d_qinstLevel(-1),
        d_preserveStructure(false),
        d_quant_elim(false),
        d_quant_elim_partial(false),
        d_isQuantBounded(false)
  {
  }
  ~QAttributes(){}
  /** does the quantified formula have a pattern? */
  bool d_hasPattern;
  /** does the quantified formula have a pool? */
  bool d_hasPool;
  /** if non-null, this quantified formula is a function definition for function
   * d_fundef_f */
  Node d_fundef_f;
  /** is this formula marked as a sygus conjecture? */
  bool d_sygus;
  /** the oracle, which stores an implementation */
  Node d_oracle;
  /** side condition for sygus conjectures */
  Node d_sygusSideCondition;
  /** stores the maximum instantiation level allowed for this quantified formula
   * (-1 means allow any) */
  int64_t d_qinstLevel;
  /**
   * Is this formula marked as preserving structure?
   * For example, this attribute is marked when computing (partial) quantifier
   * elimination on a quantified formula, but does not impact the solving method
   * for it.
   */
  bool d_preserveStructure;
  /**
   * Is this formula marked for quantifier elimination? This impacts the
   * strategy used for instantiating it, e.g. we always use CEGQI.
   */
  bool d_quant_elim;
  /**
   * Is this formula marked for partial quantifier elimination? This impacts the
   * strategy used for instantiating it, e.g. we only invoke a single
   * instantiation for it.
   */
  bool d_quant_elim_partial;
  /** Is this formula internally generated and belonging to bounded integers? */
  bool d_isQuantBounded;
  /** the instantiation pattern list for this quantified formula (its 3rd child)
   */
  Node d_ipl;
  /** The name of this quantified formula, used for :qid */
  Node d_name;
  /** The (internal) quantifier id associated with this formula */
  Node d_qid_num;
  /** is this quantified formula a function definition? */
  bool isFunDef() const { return !d_fundef_f.isNull(); }
  /** is this quantified formula an oracle interface quantifier? */
  bool isOracleInterface() const { return !d_oracle.isNull(); }
  /**
   * Is this a standard quantifier? A standard quantifier is one that we can
   * perform destructive updates (variable elimination, miniscoping, etc).
   *
   * A quantified formula is not standard if it is sygus, one for which
   * we are performing quantifier elimination, or is a function definition.
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
  QuantAttributes();
  ~QuantAttributes(){}
  /** set user attribute
   * This function applies an attribute
   * This can be called when we mark expressions with attributes, e.g. (! q
   * :attribute attr [nodeValues]),
   * It can also be called internally in various ways (for SyGus, quantifier
   * elimination, etc.)
   */
  static void setUserAttribute(const std::string& attr,
                               TNode q,
                               const std::vector<Node>& nodeValues);

  /** compute quantifier attributes */
  static void computeQuantAttributes(Node q, QAttributes& qa);
  /** compute the attributes for q */
  void computeAttributes(Node q);

  /** is sygus conjecture */
  static bool checkSygusConjecture( Node q );
  /** is sygus conjecture */
  static bool checkSygusConjectureAnnotation( Node ipl );
  /** get fun def body */
  static Node getFunDefHead( Node q );
  /** get fun def body */
  static Node getFunDefBody(Node q);
  /** does q have a user-provided pattern? */
  static bool hasPattern(Node q);

  /** is function definition */
  bool isFunDef( Node q );
  /** is sygus conjecture */
  bool isSygus( Node q );
  /** is oracle interface */
  bool isOracleInterface(Node q);
  /** get instantiation level */
  int64_t getQuantInstLevel(Node q);
  /**
   * Is q a quantified formula we are performing quantifier elimination for?
   * This also true if we are performing partial quantifier elimination on q.
   */
  bool isQuantElim(Node q) const;
  /** is quant elim partial */
  bool isQuantElimPartial(Node q) const;
  /** is internal quantifier */
  bool isQuantBounded(Node q) const;
  /** get quant name, which is used for :qid */
  Node getQuantName(Node q) const;
  /** Print quantified formula q, possibly using its name, if it has one */
  std::string quantToString(Node q) const;
  /** get (internal) quant id num */
  int getQuantIdNum( Node q );
  /** get (internal)quant id num */
  Node getQuantIdNumNode( Node q );

  /** Make the instantiation attribute that marks "quantifier elimination" */
  static Node mkAttrQuantifierElimination(NodeManager* nm);
  /** Make the instantiation attribute that marks to perserve its structure */
  static Node mkAttrPreserveStructure(NodeManager* nm);
  /**
   * Set instantiation level attribute for all subterms without an instantiation
   * level in n to level.
   */
  static void setInstantiationLevelAttr(Node n, uint64_t level);
  /**
   * Get "instantiation level" for term n, if applicable. If n has an
   * instantiation level, we return true and set level to its instantiation
   * level.
   *
   * The instantiation level is an approximate measure of how many
   * instantiations were required for generating term n. In particular,
   * all new terms generated by an instantiation { x1 -> t1 ... xn -> tn } are
   * assigned an instantiation level that is 1 + max(level(t1)...level(tn)),
   * where all terms in the input formula have level 0.
   */
  static bool getInstantiationLevel(const Node& n, uint64_t& level);

 private:
  /** An identifier for the method below */
  enum class AttrType
  {
    ATTR_PRESERVE_STRUCTURE,
    ATTR_QUANT_ELIM
  };
  /** Make attribute internal, helper for mkAttrX methods above. */
  static Node mkAttrInternal(NodeManager* nm, AttrType at);
  /** cache of attributes */
  std::map< Node, QAttributes > d_qattr;
  /** function definitions */
  std::map< Node, bool > d_fun_defs;
};

/**
 * Make a named quantified formula. This is a quantified formula that will
 * print like:
 *   (<k> <bvl> (! <body> :qid name))
 */
Node mkNamedQuant(Kind k, Node bvl, Node body, const std::string& name);
}
}
}  // namespace cvc5::internal

#endif
