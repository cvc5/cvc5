/*********************                                                        */
/*! \file full_model_check.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Full model check class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H
#define CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H

#include "theory/quantifiers/fmf/model_builder.h"
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
  /**
   * The predicate for the quantified formula. This is used to express
   * conditions under which the quantified formula is false in the model.
   * For example, for quantified formula (forall x:Int, y:U. P), this is
   * a predicate of type (Int x U) -> Bool.
   */
  std::map<Node, Node > d_quant_cond;
  /** A set of quantified formulas that cannot be handled by model-based
   * quantifier instantiation */
  std::unordered_set<Node, NodeHashFunction> d_unhandledQuant;
  std::map< TypeNode, Node > d_array_cond;
  std::map< Node, Node > d_array_term_cond;
  std::map< Node, std::vector< int > > d_star_insts;
  //--------------------for preinitialization
  /** preInitializeType
   *
   * This function ensures that the model fm is properly initialized with
   * respect to type tn.
   *
   * In particular, this class relies on the use of "model basis" terms, which
   * are distinguished terms that are used to specify default values for
   * uninterpreted functions. This method enforces that the model basis term
   * occurs in the model for each relevant type T, where a type T is relevant
   * if a bound variable is of type T, or an uninterpreted function has an
   * argument or a return value of type T.
   */
  void preInitializeType( FirstOrderModelFmc * fm, TypeNode tn );
  /** for each type, an equivalence class of that type from the model */
  std::map<TypeNode, Node> d_preinitialized_eqc;
  /** map from types to whether we have called the method above */
  std::map<TypeNode, bool> d_preinitialized_types;
  //--------------------end for preinitialization
  Node normalizeArgReps(FirstOrderModelFmc * fm, Node op, Node n);
  bool exhaustiveInstantiate(FirstOrderModelFmc * fm, Node f, Node c, int c_index);
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
  bool doMeet( FirstOrderModelFmc * fm, std::vector< Node > & cond, Node c );
  Node mkCond( std::vector< Node > & cond );
  Node mkCondDefault( FirstOrderModelFmc * fm, Node f );
  void mkCondDefaultVec( FirstOrderModelFmc * fm, Node f, std::vector< Node > & cond );
  void mkCondVec( Node n, std::vector< Node > & cond );
  Node evaluateInterpreted( Node n, std::vector< Node > & vals );
  Node getSomeDomainElement( FirstOrderModelFmc * fm, TypeNode tn );
public:
  FullModelChecker( context::Context* c, QuantifiersEngine* qe );

  void debugPrintCond(const char * tr, Node n, bool dispStar = false);
  void debugPrint(const char * tr, Node n, bool dispStar = false);

  int doExhaustiveInstantiation(FirstOrderModel* fm,
                                Node f,
                                int effort) override;

  Node getFunctionValue(FirstOrderModelFmc * fm, Node op, const char* argPrefix );

  /** process build model */
  bool preProcessBuildModel(TheoryModel* m) override;
  bool processBuildModel(TheoryModel* m) override;

  bool useSimpleModels();

 private:
  /**
   * Register quantified formula.
   * This checks whether q can be handled by model-based instantiation and
   * initializes the necessary information if so.
   */
  void registerQuantifiedFormula(Node q);
  /** Is quantified formula q handled by model-based instantiation? */
  bool isHandled(Node q) const;
};/* class FullModelChecker */

}/* CVC4::theory::quantifiers::fmcheck namespace */
}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__FULL_MODEL_CHECK_H */
