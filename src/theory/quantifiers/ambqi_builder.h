/*********************                                                        */
/*! \file ambqi_builder.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Abstract MBQI model builder class
 **/

#include "cvc4_private.h"

#ifndef ABSTRACT_MBQI_BUILDER
#define ABSTRACT_MBQI_BUILDER

#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/first_order_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class FirstOrderModelAbs;

//representiation of function and term interpretations
class AbsDef
{
private:
  int addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, Node q, std::vector< Node >& terms, unsigned depth );
  void construct_compose( FirstOrderModelAbs * m, Node q, Node n, AbsDef * f,
                          std::map< unsigned, AbsDef * >& children,
                          std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                          std::vector< unsigned >& entry, std::vector< bool >& entry_def,
                          bool incomplete );
  void construct_entry( std::vector< unsigned >& entry, std::vector< bool >& entry_def, int v, unsigned depth = 0 );
  void construct_def_entry( FirstOrderModelAbs * m, Node q, int v, unsigned depth = 0 );
  void apply_ucompose( std::vector< unsigned >& entry, std::vector< bool >& entry_def, std::vector< int >& terms,
                       std::map< unsigned, int >& vchildren, AbsDef * a, unsigned depth = 0 );
  void construct_var_eq( FirstOrderModelAbs * m, Node q, unsigned v1, unsigned v2, int curr, int currv, unsigned depth = 0 );
  void construct_var( FirstOrderModelAbs * m, Node q, unsigned v, int currv, unsigned depth = 0 );
public:
  AbsDef() : d_value( -1 ){}
  std::map< unsigned, AbsDef > d_def;
  unsigned d_default;
  int d_value;

  AbsDef * getDefault() { return &d_def[d_default]; }
  void construct_func( FirstOrderModelAbs * m, std::vector< TNode >& fapps, unsigned depth = 0 );
  void debugPrintUInt( const char * c, unsigned dSize, unsigned u );
  void debugPrint( const char * c, FirstOrderModelAbs * m, Node f, unsigned depth = 0 );
  void simplify( FirstOrderModelAbs * m, Node q, unsigned depth = 0 );
  int addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, Node q ){
    std::vector< Node > terms;
    return addInstantiations( m, qe, q, terms, 0 );
  }
  bool construct( FirstOrderModelAbs * m, Node q, Node n, AbsDef * f,
                  std::map< unsigned, AbsDef * >& children,
                  std::map< unsigned, int >& bchildren,
                  std::map< unsigned, int >& vchildren,
                  int varChCount, bool incomplete );
  Node getFunctionValue( FirstOrderModelAbs * m, TNode op, std::vector< Node >& vars, unsigned depth = 0 );
  static unsigned getId( unsigned n );
  Node evaluate( FirstOrderModelAbs * m, TypeNode retType, std::vector< Node >& args );
  Node evaluate( FirstOrderModelAbs * m, TypeNode retType, std::vector< unsigned >& iargs, unsigned depth = 0 );
};

class AbsMbqiBuilder : public QModelBuilder
{
  friend class AbsDef;
private:
  Node d_true;
  Node d_false;
  bool doCheck( FirstOrderModelAbs * m, TNode q, AbsDef & ad, TNode n );
public:
  AbsMbqiBuilder( context::Context* c, QuantifiersEngine* qe );
  //process build model
  void processBuildModel(TheoryModel* m, bool fullModel);
  //do exhaustive instantiation
  bool doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort );
};

}
}
}

#endif
