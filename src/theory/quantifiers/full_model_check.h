/*********************                                                        */
/*! \file full_model_check.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Full model check class
 **/

#ifndef FULL_MODEL_CHECK
#define FULL_MODEL_CHECK

#include "theory/quantifiers/model_builder.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {
namespace fmcheck {


class FullModelChecker;

class EntryTrie
{
public:
  EntryTrie() : d_data(-1){}
  std::map<Node,EntryTrie> d_child;
  int d_data;
  void reset() { d_data = -1; d_child.clear(); }
  void addEntry( FullModelChecker * m, Node c, Node v, int data, int index = 0 );
  bool hasGeneralization( FullModelChecker * m, Node c, int index = 0 );
  int getGeneralizationIndex( FullModelChecker * m, std::vector<Node> & inst, int index = 0 );
  void getEntries( FullModelChecker * m, Node c, std::vector<int> & compat, std::vector<int> & gen, int index = 0, bool is_gen = true );
  //if possible, get ground instance of c that evaluates to the entry
  bool getWitness( FullModelChecker * m, FirstOrderModel * fm, Node c, std::vector<Node> & inst, int index = 0 );
};


class Def
{
public:
  EntryTrie d_et;
  //cond is APPLY_UF whose arguments are returned by FullModelChecker::getRepresentative
  std::vector< Node > d_cond;
  //value is returned by FullModelChecker::getRepresentative
  std::vector< Node > d_value;
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
  bool addEntry( FullModelChecker * m, Node c, Node v);
  Node evaluate( FullModelChecker * m, std::vector<Node> inst );
  int getGeneralizationIndex( FullModelChecker * m, std::vector<Node> inst );
  void simplify( FullModelChecker * m );
  void debugPrint(const char * tr, Node op, FullModelChecker * m);
};


class FullModelChecker
{
private:
  Node d_true;
  Node d_false;
  QuantifiersEngine* d_qe;
  std::map<TypeNode, std::map< Node, int > > d_rep_ids;
  std::map<TypeNode, Node > d_model_basis_rep;
  std::map<Node, Def * > d_models;
  std::map<Node, Def > d_quant_models;
  std::map<Node, bool > d_models_init;
  std::map<Node, Node > d_quant_cond;
  std::map<TypeNode, Node > d_type_star;
  std::map<Node, std::map< Node, int > > d_quant_var_id;
  std::map<Node, std::vector< int > > d_star_insts;
  Node getRepresentative(FirstOrderModel * fm, Node n);
  Node normalizeArgReps(FirstOrderModel * fm, Node op, Node n);
  void addEntry( FirstOrderModel * fm, Node op, Node c, Node v,
                 std::vector< Node > & conds,
                 std::vector< Node > & values,
                 std::vector< Node > & entry_conds );
  int exhaustiveInstantiate(FirstOrderModel * fm, Node f, Node c, int c_index);
private:
  void doCheck(FirstOrderModel * fm, Node f, Def & d, Node n );

  void doNegate( Def & dc );
  void doVariableEquality( FirstOrderModel * fm, Node f, Def & d, Node eq );
  void doVariableRelation( FirstOrderModel * fm, Node f, Def & d, Def & dc, Node v);
  void doUninterpretedCompose( FirstOrderModel * fm, Node f, Def & d, Node n, std::vector< Def > & dc );

  void doUninterpretedCompose( FirstOrderModel * fm, Node f, Node op, Def & d,
                               std::vector< Def > & dc, int index,
                               std::vector< Node > & cond, std::vector<Node> & val );
  void doUninterpretedCompose2( FirstOrderModel * fm, Node f,
                                std::map< int, Node > & entries, int index,
                                std::vector< Node > & cond, std::vector< Node > & val,
                                EntryTrie & curr);

  void doInterpretedCompose( FirstOrderModel * fm, Node f, Def & d, Node n,
                             std::vector< Def > & dc, int index,
                             std::vector< Node > & cond, std::vector<Node> & val );
  int isCompat( std::vector< Node > & cond, Node c );
  bool doMeet( std::vector< Node > & cond, Node c );
  Node mkCond( std::vector< Node > & cond );
  Node mkCondDefault( Node f );
  void mkCondDefaultVec( Node f, std::vector< Node > & cond );
  void mkCondVec( Node n, std::vector< Node > & cond );
  Node evaluateInterpreted( Node n, std::vector< Node > & vals );
public:
  FullModelChecker( QuantifiersEngine* qe );
  ~FullModelChecker(){}

  int getVariableId(Node f, Node n) { return d_quant_var_id[f][n]; }
  bool isStar(Node n);
  Node getStar(TypeNode tn) { return d_type_star[tn]; }
  bool isModelBasisTerm(Node n);
  Node getModelBasisTerm(TypeNode tn);
  void reset(FirstOrderModel * fm);
  Def * getModel(FirstOrderModel * fm, Node op);

  void debugPrintCond(const char * tr, Node n, bool dispStar = false);
  void debugPrint(const char * tr, Node n, bool dispStar = false);

  int exhaustiveInstantiate(FirstOrderModel * fm, Node f, int effort);
  bool hasStarExceptions( Node f ) { return !d_star_insts[f].empty(); }

  bool isActive();
  bool useSimpleModels();
  Node getFunctionValue(FirstOrderModel * fm, Node op, const char* argPrefix );
};

}
}
}
}

#endif
