/*********************                                                        */
/*! \file first_order_model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model extended classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__FIRST_ORDER_MODEL_H
#define __CVC4__FIRST_ORDER_MODEL_H

#include "theory/model.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/arrays/theory_arrays_model.h"

namespace CVC4 {
namespace theory {

struct ModelBasisAttributeId {};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
//for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                    0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId {};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t> ModelBasisArgAttribute;

class QuantifiersEngine;

namespace quantifiers{

class TermDb;

class FirstOrderModel : public DefaultModel
{
private:
  //pointer to term database
  TermDb* d_term_db;
  //add term function
  void addTerm( Node n );
  //for initialize model
  void initializeModelForTerm( Node n );
  /** to stream functions */
  void toStreamFunction( Node n, std::ostream& out );
  void toStreamType( TypeNode tn, std::ostream& out );
public: //for Theory UF:
  //models for each UF operator
  std::map< Node, uf::UfModelTree > d_uf_model_tree;
  //model generators
  std::map< Node, uf::UfModelTreeGenerator > d_uf_model_gen;
public: //for Theory Arrays:
  //default value for each non-store array
  std::map< Node, arrays::ArrayModel > d_array_model;
public: //for Theory Quantifiers:
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** get number of asserted quantifiers */
  int getNumAssertedQuantifiers() { return (int)d_forall_asserts.size(); }
  /** get asserted quantifier */
  Node getAssertedQuantifier( int i ) { return d_forall_asserts[i]; }
public:
  FirstOrderModel( QuantifiersEngine* qe, context::Context* c, std::string name );
  virtual ~FirstOrderModel(){}
  // reset the model
  void reset();
  /** get interpreted value */
  Node getInterpretedValue( TNode n );
public:
  // initialize the model
  void initialize();
  /** get term database */
  TermDb* getTermDatabase();
  /** to stream function */
  void toStream( std::ostream& out );
};

}
}
}

#endif
