/*********************                                                        */
/*! \file ambqi_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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
  bool addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, TNode q, std::vector< Node >& terms, int& inst, unsigned depth );
  void construct_compose( FirstOrderModelAbs * m, TNode q, TNode n, AbsDef * f,
                          std::map< unsigned, AbsDef * >& children,
                          std::map< unsigned, int >& bchildren, std::map< unsigned, int >& vchildren,
                          std::vector< unsigned >& entry, std::vector< bool >& entry_def );
  void construct_entry( std::vector< unsigned >& entry, std::vector< bool >& entry_def, int v, unsigned depth = 0 );
  void construct_def_entry( FirstOrderModelAbs * m, TNode q, TNode n, int v, unsigned depth = 0 );
  void apply_ucompose( FirstOrderModelAbs * m, TNode q,
                       std::vector< unsigned >& entry, std::vector< bool >& entry_def, std::vector< int >& terms,
                       std::map< unsigned, int >& vchildren, AbsDef * a, unsigned depth = 0 );
  void construct_var_eq( FirstOrderModelAbs * m, TNode q, unsigned v1, unsigned v2, int curr, int currv, unsigned depth = 0 );
  void construct_var( FirstOrderModelAbs * m, TNode q, unsigned v, int currv, unsigned depth = 0 );
  void get_defs( unsigned u, std::vector< AbsDef * >& defs );
  void construct_normalize( FirstOrderModelAbs * m, TNode q, std::vector< AbsDef * >& defs, unsigned depth = 0 );
public:
  enum {
    val_none = -1,
    val_unk = -2,
  };
  AbsDef() : d_default( 0 ), d_value( -1 ){}
  std::map< unsigned, AbsDef > d_def;
  unsigned d_default;
  int d_value;

  void clear() { d_def.clear(); d_default = 0; d_value = -1; }
  AbsDef * getDefault() { return &d_def[d_default]; }
  void construct_func( FirstOrderModelAbs * m, std::vector< TNode >& fapps, unsigned depth = 0 );
  void debugPrintUInt( const char * c, unsigned dSize, unsigned u ) const;
  void debugPrint( const char * c, FirstOrderModelAbs * m, TNode f, unsigned depth = 0 ) const;
  void simplify( FirstOrderModelAbs * m, TNode q, TNode n, unsigned depth = 0 );
  int addInstantiations( FirstOrderModelAbs * m, QuantifiersEngine * qe, Node q, int& inst ){
    std::vector< Node > terms;
    terms.resize( q[0].getNumChildren() );
    return addInstantiations( m, qe, q, terms, inst, 0 );
  }
  bool construct( FirstOrderModelAbs * m, TNode q, TNode n, AbsDef * f,
                  std::map< unsigned, AbsDef * >& children,
                  std::map< unsigned, int >& bchildren,
                  std::map< unsigned, int >& vchildren,
                  int varChCount );
  void negate();
  Node getFunctionValue( FirstOrderModelAbs * m, TNode op, std::vector< Node >& vars, unsigned depth = 0 );
  static bool isSimple( unsigned n );
  static unsigned getId( unsigned n, unsigned start=0, unsigned end=32 );
  Node evaluate( FirstOrderModelAbs * m, TypeNode retType, std::vector< Node >& args );
  Node evaluate( FirstOrderModelAbs * m, TypeNode retType, std::vector< unsigned >& iargs, unsigned depth = 0 );
  //for debugging
  bool is_normalized();
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
  ~AbsMbqiBuilder() throw() {}
  //process build model
  void processBuildModel(TheoryModel* m, bool fullModel);
  //do exhaustive instantiation
  int doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort );
};

}
}
}

#endif
