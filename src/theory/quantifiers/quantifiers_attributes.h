/*********************                                                        */
/*! \file quantifiers_attributes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Paul Meng, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Attributes for the theory quantifiers
 **
 ** Attributes for the theory quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H
#define __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_ATTRIBUTES_H

#include "expr/attribute.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** Attribute true for quantifiers that are axioms */
struct AxiomAttributeId {};
typedef expr::Attribute< AxiomAttributeId, bool > AxiomAttribute;

/** Attribute true for quantifiers that are conjecture */
struct ConjectureAttributeId {};
typedef expr::Attribute< ConjectureAttributeId, bool > ConjectureAttribute;

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

/** Attribute true for quantifiers that are synthesis conjectures */
struct SynthesisAttributeId {};
typedef expr::Attribute< SynthesisAttributeId, bool > SynthesisAttribute;

namespace quantifiers {

/** Attribute priority for rewrite rules */
//struct RrPriorityAttributeId {};
//typedef expr::Attribute< RrPriorityAttributeId, uint64_t > RrPriorityAttribute;


/** This class stores attributes for quantified formulas 
* TODO : document (as part of #1171)
*/
class QAttributes{
public:
  QAttributes() : d_hasPattern(false), d_conjecture(false), d_axiom(false), d_sygus(false),
                  d_synthesis(false), d_rr_priority(-1), d_qinstLevel(-1), d_quant_elim(false), d_quant_elim_partial(false){}
  ~QAttributes(){}
  bool d_hasPattern;
  Node d_rr;
  bool d_conjecture;
  bool d_axiom;
  Node d_fundef_f;
  bool d_sygus;
  bool d_synthesis;
  int d_rr_priority;
  int d_qinstLevel;
  bool d_quant_elim;
  bool d_quant_elim_partial;
  Node d_ipl;
  Node d_qid_num;
  bool isRewriteRule() { return !d_rr.isNull(); }
  bool isFunDef() { return !d_fundef_f.isNull(); }
};

/** This class caches information about attributes of quantified formulas 
* It also has static utility functions used for determining attributes and information about 
* quantified formulas.
*/
class QuantAttributes
{
public:
  QuantAttributes( QuantifiersEngine * qe );
  ~QuantAttributes(){}
  
  /** set user attribute
    *   This function will apply a custom set of attributes to all top-level universal
    *   quantifiers contained in n
    */
  static void setUserAttribute( const std::string& attr, Node n, std::vector< Node >& node_values, std::string str_value );
  
  //general queries concerning quantified formulas wrt modules
  /** is quantifier treated as a rewrite rule? */
  static bool checkRewriteRule( Node q );
  /** get the rewrite rule associated with the quanfied formula */
  static Node getRewriteRule( Node q );
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

  /** is conjecture */
  bool isConjecture( Node q );
  /** is axiom */
  bool isAxiom( Node q );
  /** is function definition */
  bool isFunDef( Node q );
  /** is sygus conjecture */
  bool isSygus( Node q );
  /** is synthesis conjecture */
  bool isSynthesis( Node q );
  /** get instantiation level */
  int getQuantInstLevel( Node q );
  /** get rewrite rule priority */
  int getRewriteRulePriority( Node q );
  /** is quant elim */
  bool isQuantElim( Node q );
  /** is quant elim partial */
  bool isQuantElimPartial( Node q );
  /** get quant id num */
  int getQuantIdNum( Node q );
  /** get quant id num */
  Node getQuantIdNumNode( Node q );
  /** compute quantifier attributes */
  static void computeQuantAttributes( Node q, QAttributes& qa );
  /** compute the attributes for q */
  void computeAttributes( Node q );
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
