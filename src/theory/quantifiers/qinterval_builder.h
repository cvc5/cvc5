/*********************                                                        */
/*! \file qinterval_builder.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief qinterval model class
 **/

#include "cvc4_private.h"

#ifndef QINTERVAL_BUILDER
#define QINTERVAL_BUILDER

#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/first_order_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class FirstOrderModelQInt;

class QIntVarNumIndex
{
public:
  std::map< int, int > d_var_num;
  std::map< int, QIntVarNumIndex > d_var_index;
};

class QIntDef
{
private:
  Node evaluate_r( FirstOrderModelQInt * m, std::vector< Node >& reps, unsigned depth );
  Node evaluate_n_r( FirstOrderModelQInt * m, Node n, unsigned depth );
  void construct_compose_r( FirstOrderModelQInt * m, Node q,
                            std::vector< Node >& l, std::vector< Node >& u, Node n, QIntDef * f,
                            std::vector< Node >& args,
                            std::map< unsigned, QIntDef >& children,
                            std::map< unsigned, Node >& bchildren,
                            QIntVarNumIndex& vindex,
                            unsigned depth );

  void construct_enum_r( FirstOrderModelQInt * m, Node q, unsigned vn, unsigned depth, Node v );
  int getEvIndex( FirstOrderModelQInt * m, Node n, bool exc = false );
  void addEntry( FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u,
                 Node v, unsigned depth = 0 );
  Node simplify_r( FirstOrderModelQInt * m, Node q, std::vector< Node >& il, std::vector< Node >& iu,
                   unsigned depth );
  bool isTotal_r( FirstOrderModelQInt * m, Node q, std::vector< Node >& il, std::vector< Node >& iu,
                  unsigned depth );
public:
  QIntDef(){}
  std::map< Node, QIntDef > d_def;
  std::vector< Node > d_def_order;

  void construct( FirstOrderModelQInt * m, std::vector< Node >& fapps, unsigned depth = 0 );
  bool construct_compose( FirstOrderModelQInt * m, Node q, Node n, QIntDef * f,
                          std::map< unsigned, QIntDef >& children,
                          std::map< unsigned, Node >& bchildren, int varChCount,
                          QIntVarNumIndex& vindex );
  bool construct_enum( FirstOrderModelQInt * m, Node q, unsigned vn );

  Node evaluate( FirstOrderModelQInt * m, std::vector< Node >& reps ) { return evaluate_r( m, reps, 0 ); }
  Node evaluate_n( FirstOrderModelQInt * m, Node n ) { return evaluate_n_r( m, n, 0 ); }

  void debugPrint( const char * c, FirstOrderModelQInt * m, Node q, int t = 0 );
  QIntDef * getChild( unsigned i );
  Node getValue() { return d_def_order[0]; }
  Node getLower( unsigned i ) { return i==0 ? Node::null() : d_def_order[i-1]; }
  Node getUpper( unsigned i ) { return d_def_order[i]; }
  Node getMaximum() { return d_def_order.empty() ? Node::null() : getUpper( d_def_order.size()-1 ); }
  int getNumChildren() { return d_def_order.size(); }
  bool isTotal( FirstOrderModelQInt * m, Node q );

  Node simplify( FirstOrderModelQInt * m, Node q );
  Node getFunctionValue( FirstOrderModelQInt * m, std::vector< Node >& vars, unsigned depth = 0 );

  static void init_vec( FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u );
  static void debugPrint( const char * c, FirstOrderModelQInt * m, Node q, std::vector< Node >& l, std::vector< Node >& u );
};

class QIntDefIter {
private:
  FirstOrderModelQInt * d_fm;
  Node d_q;
  void resetIndex( QIntDef * qid );
public:
  QIntDefIter( FirstOrderModelQInt * m, Node q, QIntDef * qid );
  void debugPrint( const char * c, int t = 0 );
  std::vector< QIntDef * > d_index_visited;
  std::vector< int > d_index;
  bool isFinished() { return d_index.empty(); }
  bool increment( int index = -1 );
  unsigned getSize() { return d_index.size(); }
  Node getLower( int index );
  Node getUpper( int index );
  void getLowers( std::vector< Node >& reps );
  void getUppers( std::vector< Node >& reps );
  Node getValue();
};


class QuantVarOrder
{
private:
  int initialize( Node n, int minVarIndex, QIntVarNumIndex& vindex );
  int d_var_count;
  Node d_q;
  void debugPrint( const char * c, Node n, QIntVarNumIndex& vindex );
public:
  QuantVarOrder( Node q );
  std::map< int, Node > d_num_to_var;
  std::map< int, int > d_num_to_prev_num;
  std::map< int, int > d_num_to_next_num;
  std::map< Node, std::vector< int > > d_var_to_num;
  std::map< int, int > d_var_num_index;
  //std::map< Node, std::map< int, int > > d_var_occur;
  //int getVarNum( Node n, int arg ) { return d_var_occur[n][arg]; }
  unsigned getNumVars() { return d_var_count; }
  Node getVar( int i ) { return d_num_to_var[i]; }
  int getPrevNum( int i ) { return d_num_to_prev_num.find( i )!=d_num_to_prev_num.end() ? d_num_to_prev_num[i] : -1; }
  int getNextNum( int i ) { return d_num_to_next_num.find( i )!=d_num_to_next_num.end() ? d_num_to_next_num[i] : -1; }
  int getVarNumIndex( int i ) { return d_var_num_index[i]; }
  bool getInstantiation( FirstOrderModelQInt * m, std::vector< Node >& l, std::vector< Node >& u,
                         std::vector< Node >& inst );
  void debugPrint( const char * c );
  QIntVarNumIndex d_var_occur;
};

class QIntervalBuilder : public QModelBuilder
{
private:
  Node d_true;
  bool doCheck( FirstOrderModelQInt * m, Node q, QIntDef & qid, Node n,
                QIntVarNumIndex& vindex );
public:
  QIntervalBuilder( context::Context* c, QuantifiersEngine* qe );
  //process build model
  void processBuildModel(TheoryModel* m, bool fullModel);
  //do exhaustive instantiation
  bool doExhaustiveInstantiation( FirstOrderModel * fm, Node q, int effort );
};


}
}
}

#endif