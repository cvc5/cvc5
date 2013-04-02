/*********************                                                        */
/*! \file first_order_model.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of model engine model class
 **/

#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"

#define USE_INDEX_ORDERING

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

FirstOrderModel::FirstOrderModel( context::Context* c, std::string name ) : TheoryModel( c, name, true ),
d_axiom_asserted( c, false ), d_forall_asserts( c ), d_isModelSet( c, false ){

}

void FirstOrderModel::assertQuantifier( Node n ){
  d_forall_asserts.push_back( n );
  if( n.getAttribute(AxiomAttribute()) ){
    d_axiom_asserted = true;
  }
}

void FirstOrderModel::reset(){
  TheoryModel::reset();
}

void FirstOrderModel::initialize( bool considerAxioms ){
  //rebuild models
  d_uf_model_tree.clear();
  d_uf_model_gen.clear();
  d_array_model.clear();
  //this is called after representatives have been chosen and the equality engine has been built
  //for each quantifier, collect all operators we care about
  for( int i=0; i<getNumAssertedQuantifiers(); i++ ){
    Node f = getAssertedQuantifier( i );
    if( considerAxioms || !f.hasAttribute(AxiomAttribute()) ){
      //initialize relevant models within bodies of all quantifiers
      initializeModelForTerm( f[1] );
    }
  }
}

void FirstOrderModel::initializeModelForTerm( Node n ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( d_uf_model_tree.find( op )==d_uf_model_tree.end() ){
      TypeNode tn = op.getType();
      tn = tn[ (int)tn.getNumChildren()-1 ];
      //only generate models for predicates and functions with uninterpreted range types
      if( tn==NodeManager::currentNM()->booleanType() || tn.isSort() ){
        d_uf_model_tree[ op ] = uf::UfModelTree( op );
        d_uf_model_gen[ op ].clear();
      }
    }
  }
  /*
  if( n.getType().isArray() ){
    while( n.getKind()==STORE ){
      n = n[0];
    }
    Node nn = getRepresentative( n );
    if( d_array_model.find( nn )==d_array_model.end() ){
      d_array_model[nn] = arrays::ArrayModel( nn, this );
    }
  }
  */
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    initializeModelForTerm( n[i] );
  }
}

//for evaluation of quantifier bodies

void FirstOrderModel::resetEvaluate(){
  d_eval_uf_use_default.clear();
  d_eval_uf_model.clear();
  d_eval_term_index_order.clear();
  d_eval_failed.clear();
  d_eval_failed_lits.clear();
  d_eval_formulas = 0;
  d_eval_uf_terms = 0;
  d_eval_lits = 0;
  d_eval_lits_unknown = 0;
}

//if evaluate( n ) = eVal,
// let n' = ri * n be the formula n instantiated with the current values in r_iter
// if eVal = 1, then n' is true, if eVal = -1, then n' is false,
// if eVal = 0, then n' cannot be proven to be equal to phaseReq
// if eVal is not 0, then
//   each n{ri->d_index[0]/x_0...ri->d_index[depIndex]/x_depIndex, */x_(depIndex+1) ... */x_n } is equivalent in the current model
int FirstOrderModel::evaluate( Node n, int& depIndex, RepSetIterator* ri ){
  ++d_eval_formulas;
  //Debug("fmf-eval-debug") << "Evaluate " << n << " " << phaseReq << std::endl;
  //Notice() << "Eval " << n << std::endl;
  if( n.getKind()==NOT ){
    int val = evaluate( n[0], depIndex, ri );
    return val==1 ? -1 : ( val==-1 ? 1 : 0 );
  }else if( n.getKind()==OR || n.getKind()==AND || n.getKind()==IMPLIES ){
    int baseVal = n.getKind()==AND ? 1 : -1;
    int eVal = baseVal;
    int posDepIndex = ri->getNumTerms();
    int negDepIndex = -1;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //evaluate subterm
      int childDepIndex;
      Node nn = ( i==0 && n.getKind()==IMPLIES ) ? n[i].notNode() : n[i];
      int eValT = evaluate( nn, childDepIndex, ri );
      if( eValT==baseVal ){
        if( eVal==baseVal ){
          if( childDepIndex>negDepIndex ){
            negDepIndex = childDepIndex;
          }
        }
      }else if( eValT==-baseVal ){
        eVal = -baseVal;
        if( childDepIndex<posDepIndex ){
          posDepIndex = childDepIndex;
          if( posDepIndex==-1 ){
            break;
          }
        }
      }else if( eValT==0 ){
        if( eVal==baseVal ){
          eVal = 0;
        }
      }
    }
    if( eVal!=0 ){
      depIndex = eVal==-baseVal ? posDepIndex : negDepIndex;
      return eVal;
    }else{
      return 0;
    }
  }else if( n.getKind()==IFF || n.getKind()==XOR ){
    int depIndex1;
    int eVal = evaluate( n[0], depIndex1, ri );
    if( eVal!=0 ){
      int depIndex2;
      int eVal2 = evaluate( n.getKind()==XOR ? n[1].notNode() : n[1], depIndex2, ri );
      if( eVal2!=0 ){
        depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
        return eVal==eVal2 ? 1 : -1;
      }
    }
    return 0;
  }else if( n.getKind()==ITE ){
    int depIndex1, depIndex2;
    int eVal = evaluate( n[0], depIndex1, ri );
    if( eVal==0 ){
      //evaluate children to see if they are the same value
      int eval1 = evaluate( n[1], depIndex1, ri );
      if( eval1!=0 ){
        int eval2 = evaluate( n[1], depIndex2, ri );
        if( eval1==eval2 ){
          depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
          return eval1;
        }
      }
    }else{
      int eValT = evaluate( n[eVal==1 ? 1 : 2], depIndex2, ri );
      depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
      return eValT;
    }
    return 0;
  }else if( n.getKind()==FORALL ){
    return 0;
  }else{
    ++d_eval_lits;
    ////if we know we will fail again, immediately return
    //if( d_eval_failed.find( n )!=d_eval_failed.end() ){
    //  if( d_eval_failed[n] ){
    //    return -1;
    //  }
    //}
    //Debug("fmf-eval-debug") << "Evaluate literal " << n << std::endl;
    int retVal = 0;
    depIndex = ri->getNumTerms()-1;
    Node val = evaluateTerm( n, depIndex, ri );
    if( !val.isNull() ){
      if( areEqual( val, d_true ) ){
        retVal = 1;
      }else if( areEqual( val, d_false ) ){
        retVal = -1;
      }else{
        if( val.getKind()==EQUAL ){
          if( areEqual( val[0], val[1] ) ){
            retVal = 1;
          }else if( areDisequal( val[0], val[1] ) ){
            retVal = -1;
          }
        }
      }
    }
    if( retVal!=0 ){
      Debug("fmf-eval-debug") << "Evaluate literal: return " << retVal << ", depIndex = " << depIndex << std::endl;
    }else{
      ++d_eval_lits_unknown;
      Trace("fmf-eval-amb") << "Neither true nor false : " << n << std::endl;
      Trace("fmf-eval-amb") << "   value : " << val << std::endl;
      //std::cout << "Neither true nor false : " << n << std::endl;
      //std::cout << "  Value : " << val << std::endl;
      //for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //  std::cout << "   " << i << " : " << n[i].getType() << std::endl;
      //}
    }
    return retVal;
  }
}

Node FirstOrderModel::evaluateTerm( Node n, int& depIndex, RepSetIterator* ri ){
  //Message() << "Eval term " << n << std::endl;
  Node val;
  depIndex = ri->getNumTerms()-1;
  //check the type of n
  if( n.getKind()==INST_CONSTANT ){
    int v = n.getAttribute(InstVarNumAttribute());
    depIndex = ri->d_var_order[ v ];
    val = ri->getTerm( v );
  }else if( n.getKind()==ITE ){
    int depIndex1, depIndex2;
    int eval = evaluate( n[0], depIndex1, ri );
    if( eval==0 ){
      //evaluate children to see if they are the same
      Node val1 = evaluateTerm( n[ 1 ], depIndex1, ri );
      Node val2 = evaluateTerm( n[ 2 ], depIndex2, ri );
      if( val1==val2 ){
        val = val1;
        depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
      }else{
        return Node::null();
      }
    }else{
      val = evaluateTerm( n[ eval==1 ? 1 : 2 ], depIndex2, ri );
      depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
    }
  }else{
    std::vector< int > children_depIndex;
    //for select, pre-process read over writes
    if( n.getKind()==SELECT ){
#if 0
      //std::cout << "Evaluate " << n << std::endl;
      Node sel = evaluateTerm( n[1], depIndex, ri );
      if( sel.isNull() ){
        depIndex = ri->getNumTerms()-1;
        return Node::null();
      }
      Node arr = getRepresentative( n[0] );
      //if( n[0]!=getRepresentative( n[0] ) ){
      //  std::cout << n[0] << " is " << getRepresentative( n[0] ) << std::endl;
      //}
      int tempIndex;
      int eval = 1;
      while( arr.getKind()==STORE && eval!=0 ){
        eval = evaluate( sel.eqNode( arr[1] ), tempIndex, ri );
        depIndex = tempIndex > depIndex ? tempIndex : depIndex;
        if( eval==1 ){
          val = evaluateTerm( arr[2], tempIndex, ri );
          depIndex = tempIndex > depIndex ? tempIndex : depIndex;
          return val;
        }else if( eval==-1 ){
          arr = arr[0];
        }
      }
      arr = evaluateTerm( arr, tempIndex, ri );
      depIndex = tempIndex > depIndex ? tempIndex : depIndex;
      val = NodeManager::currentNM()->mkNode( SELECT, arr, sel );
#else
      val = evaluateTermDefault( n, depIndex, children_depIndex, ri );
#endif
    }else{
      //default term evaluate : evaluate all children, recreate the value
      val = evaluateTermDefault( n, depIndex, children_depIndex, ri );
    }
    if( !val.isNull() ){
      bool setVal = false;
      //custom ways of evaluating terms
      if( n.getKind()==APPLY_UF ){
        Node op = n.getOperator();
        //Debug("fmf-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
        //if it is a defined UF, then consult the interpretation
        if( d_uf_model_tree.find( op )!=d_uf_model_tree.end() ){
          ++d_eval_uf_terms;
          int argDepIndex = 0;
          //make the term model specifically for n
          makeEvalUfModel( n );
          //now, consult the model
          if( d_eval_uf_use_default[n] ){
            val = d_uf_model_tree[ op ].getValue( this, val, argDepIndex );
          }else{
            val = d_eval_uf_model[ n ].getValue( this, val, argDepIndex );
          }
          //Debug("fmf-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
          //d_eval_uf_model[ n ].debugPrint("fmf-eval-debug", d_qe );
          Assert( !val.isNull() );
          //recalculate the depIndex
          depIndex = -1;
          for( int i=0; i<argDepIndex; i++ ){
            int index = d_eval_uf_use_default[n] ? i : d_eval_term_index_order[n][i];
            Debug("fmf-eval-debug") << "Add variables from " << index << "..." << std::endl;
            if( children_depIndex[index]>depIndex ){
              depIndex = children_depIndex[index];
            }
          }
          setVal = true;
        }
      }else if( n.getKind()==SELECT ){
        //we are free to interpret this term however we want
      }
      //if not set already, rewrite and consult model for interpretation
      if( !setVal ){
        val = Rewriter::rewrite( val );
        if( val.getMetaKind()!=kind::metakind::CONSTANT ){
          //FIXME: we cannot do this until we trust all theories collectModelInfo!
          //val = getInterpretedValue( val );
          //val = getRepresentative( val );
        }
      }
      Trace("fmf-eval-debug") << "Evaluate term " << n << " = ";
      printRepresentativeDebug( "fmf-eval-debug", val );
      Trace("fmf-eval-debug") << ", depIndex = " << depIndex << std::endl;
    }
  }
  return val;
}

Node FirstOrderModel::evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex, RepSetIterator* ri ){
  depIndex = -1;
  if( n.getNumChildren()==0 ){
    return n;
  }else{
    //first we must evaluate the arguments
    std::vector< Node > children;
    if( n.getMetaKind()==kind::metakind::PARAMETERIZED ){
      children.push_back( n.getOperator() );
    }
    //for each argument, calculate its value, and the variables its value depends upon
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      childDepIndex.push_back( -1 );
      Node nn = evaluateTerm( n[i], childDepIndex[i], ri );
      if( nn.isNull() ){
        depIndex = ri->getNumTerms()-1;
        return nn;
      }else{
        children.push_back( nn );
        if( childDepIndex[i]>depIndex ){
          depIndex = childDepIndex[i];
        }
      }
    }
    //recreate the value
    Node val = NodeManager::currentNM()->mkNode( n.getKind(), children );
    return val;
  }
}

void FirstOrderModel::clearEvalFailed( int index ){
  for( int i=0; i<(int)d_eval_failed_lits[index].size(); i++ ){
    d_eval_failed[ d_eval_failed_lits[index][i] ] = false;
  }
  d_eval_failed_lits[index].clear();
}

void FirstOrderModel::makeEvalUfModel( Node n ){
  if( d_eval_uf_model.find( n )==d_eval_uf_model.end() ){
    makeEvalUfIndexOrder( n );
    if( !d_eval_uf_use_default[n] ){
      Node op = n.getOperator();
      d_eval_uf_model[n] = uf::UfModelTree( op, d_eval_term_index_order[n] );
      d_uf_model_gen[op].makeModel( this, d_eval_uf_model[n] );
      //Debug("fmf-index-order") << "Make model for " << n << " : " << std::endl;
      //d_eval_uf_model[n].debugPrint( "fmf-index-order", d_qe, 2 );
    }
  }
}

struct sortGetMaxVariableNum {
  std::map< Node, int > d_max_var_num;
  int computeMaxVariableNum( Node n ){
    if( n.getKind()==INST_CONSTANT ){
      return n.getAttribute(InstVarNumAttribute());
    }else if( n.hasAttribute(InstConstantAttribute()) ){
      int maxVal = -1;
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        int val = getMaxVariableNum( n[i] );
        if( val>maxVal ){
          maxVal = val;
        }
      }
      return maxVal;
    }else{
      return -1;
    }
  }
  int getMaxVariableNum( Node n ){
    std::map< Node, int >::iterator it = d_max_var_num.find( n );
    if( it==d_max_var_num.end() ){
      int num = computeMaxVariableNum( n );
      d_max_var_num[n] = num;
      return num;
    }else{
      return it->second;
    }
  }
  bool operator() (Node i,Node j) { return (getMaxVariableNum(i)<getMaxVariableNum(j));}
};

void FirstOrderModel::makeEvalUfIndexOrder( Node n ){
  if( d_eval_term_index_order.find( n )==d_eval_term_index_order.end() ){
#ifdef USE_INDEX_ORDERING
    //sort arguments in order of least significant vs. most significant variable in default ordering
    std::map< Node, std::vector< int > > argIndex;
    std::vector< Node > args;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( argIndex.find( n[i] )==argIndex.end() ){
        args.push_back( n[i] );
      }
      argIndex[n[i]].push_back( i );
    }
    sortGetMaxVariableNum sgmvn;
    std::sort( args.begin(), args.end(), sgmvn );
    for( int i=0; i<(int)args.size(); i++ ){
      for( int j=0; j<(int)argIndex[ args[i] ].size(); j++ ){
        d_eval_term_index_order[n].push_back( argIndex[ args[i] ][j] );
      }
    }
    bool useDefault = true;
    for( int i=0; i<(int)d_eval_term_index_order[n].size(); i++ ){
      if( i!=d_eval_term_index_order[n][i] ){
        useDefault = false;
        break;
      }
    }
    d_eval_uf_use_default[n] = useDefault;
    Debug("fmf-index-order") << "Will consider the following index ordering for " << n << " : ";
    for( int i=0; i<(int)d_eval_term_index_order[n].size(); i++ ){
      Debug("fmf-index-order") << d_eval_term_index_order[n][i] << " ";
    }
    Debug("fmf-index-order") << std::endl;
#else
    d_eval_uf_use_default[n] = true;
#endif
  }
}
