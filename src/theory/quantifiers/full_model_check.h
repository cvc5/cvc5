/*********************                                                        */
/*! \file full_model_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Full model check class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H
#define __CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H

#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/first_order_model.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
namespace fmcheck {


class FirstOrderModelFmc;
class FullModelChecker;

class EntryTrie
{
private:
  int d_complete;
public:
  EntryTrie() : d_complete(-1), d_data(-1){}
  std::map<Node,EntryTrie> d_child;
  int d_data;
  void reset() { d_data = -1; d_child.clear(); d_complete = -1; }
  void addEntry( FirstOrderModelFmc * m, Node c, Node v, int data, int index = 0 );
  bool hasGeneralization( FirstOrderModelFmc * m, Node c, int index = 0 );
  int getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node> & inst, int index = 0 );
  void getEntries( FirstOrderModelFmc * m, Node c, std::vector<int> & compat, std::vector<int> & gen, int index = 0, bool is_gen = true );

  void collectIndices(Node c, int index, std::vector< int >& indices );
  bool isComplete(FirstOrderModelFmc * m, Node c, int index);
};/* class EntryTrie */


class Def
{
public:
  EntryTrie d_et;
  //cond is APPLY_UF whose arguments are returned by FullModelChecker::getRepresentative
  std::vector< Node > d_cond;
  //value is returned by FullModelChecker::getRepresentative
  std::vector< Node > d_value;
  void basic_simplify( FirstOrderModelFmc * m );
private:
  enum {
    status_unk,
    status_redundant,
    status_non_redundant
  };
  std::vector< int > d_status;
  bool d_has_simplified;
public:
  Def() : d_has_simplified(false){}
  void reset() {
    d_et.reset();
    d_cond.clear();
    d_value.clear();
    d_status.clear();
    d_has_simplified = false;
  }
  bool addEntry( FirstOrderModelFmc * m, Node c, Node v);
  Node evaluate( FirstOrderModelFmc * m, std::vector<Node>& inst );
  int getGeneralizationIndex( FirstOrderModelFmc * m, std::vector<Node>& inst );
  void simplify( FullModelChecker * mc, FirstOrderModelFmc * m );
  void debugPrint(const char * tr, Node op, FullModelChecker * m);
};/* class Def */


class FullModelChecker : public QModelBuilder
{
protected:
  Node d_true;
  Node d_false;
  std::map<TypeNode, std::map< Node, int > > d_rep_ids;
  std::map<Node, Def > d_quant_models;
  std::map<Node, Node > d_quant_cond;
  std::map< TypeNode, Node > d_array_cond;
  std::map< Node, Node > d_array_term_cond;
  std::map< Node, std::vector< int > > d_star_insts;
  std::map< TypeNode, bool > d_preinitialized_types;
  void preInitializeType( FirstOrderModelFmc * fm, TypeNode tn );
  Node normalizeArgReps(FirstOrderModelFmc * fm, Node op, Node n);
  bool exhaustiveInstantiate(FirstOrderModelFmc * fm, Node f, Node c, int c_index);
protected:
  void makeIntervalModel2( FirstOrderModelFmc * fm, Node op, std::vector< int > & indices, int index,
                          std::map< int, std::map< int, Node > >& changed_vals );
  void makeIntervalModel( FirstOrderModelFmc * fm, Node op, std::vector< int > & indices, int index,
                          std::map< int, std::map< int, Node > >& changed_vals );
  void convertIntervalModel( FirstOrderModelFmc * fm, Node op );
private:
  void doCheck(FirstOrderModelFmc * fm, Node f, Def & d, Node n );

  void doNegate( Def & dc );
  void doVariableEquality( FirstOrderModelFmc * fm, Node f, Def & d, Node eq );
  void doVariableRelation( FirstOrderModelFmc * fm, Node f, Def & d, Def & dc, Node v);
  void doUninterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d, Node n, std::vector< Def > & dc );

  void doUninterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d,
                               Def & df, std::vector< Def > & dc, int index,
                               std::vector< Node > & cond, std::vector<Node> & val );
  void doUninterpretedCompose2( FirstOrderModelFmc * fm, Node f,
                                std::map< int, Node > & entries, int index,
                                std::vector< Node > & cond, std::vector< Node > & val,
                                EntryTrie & curr);

  void doInterpretedCompose( FirstOrderModelFmc * fm, Node f, Def & d, Node n,
                             std::vector< Def > & dc, int index,
                             std::vector< Node > & cond, std::vector<Node> & val );
  int isCompat( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c );
  Node doIntervalMeet( FirstOrderModelFmc * fm, Node i1, Node i2, bool mk = true );
  bool doMeet( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c );
  Node mkCond( std::vector< Node > & cond );
  Node mkCondDefault( FirstOrderModelFmc * fm, Node f );
  void mkCondDefaultVec( FirstOrderModelFmc * fm, Node f, std::vector< Node > & cond );
  void mkCondVec( Node n, std::vector< Node > & cond );
  Node mkArrayCond( Node a );
  Node evaluateInterpreted( Node n, std::vector< Node > & vals );
  Node getSomeDomainElement( FirstOrderModelFmc * fm, TypeNode tn );
public:
  FullModelChecker( context::Context* c, QuantifiersEngine* qe );
  ~FullModelChecker() throw() {}

  void debugPrintCond(const char * tr, Node n, bool dispStar = false);
  void debugPrint(const char * tr, Node n, bool dispStar = false);

  int doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort );

  Node getFunctionValue(FirstOrderModelFmc * fm, Node op, const char* argPrefix );

  /** process build model */  
  void preProcessBuildModel(TheoryModel* m, bool fullModel); 
  void processBuildModel(TheoryModel* m, bool fullModel);
  /** get current model value */
  Node getCurrentUfModelValue( FirstOrderModelFmc* fm, Node n, std::vector< Node > & args, bool partial );

  bool useSimpleModels();
};/* class FullModelChecker */

}/* CVC4::theory::quantifiers::fmcheck namespace */
}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H */
