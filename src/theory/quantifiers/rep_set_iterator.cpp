/*********************                                                        */
/*! \file rep_set_iterator.cpp
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
 ** \brief Implementation of relevant domain class
 **/

#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/term_database.h"

#define USE_INDEX_ORDERING

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

RepSetIterator::RepSetIterator( Node f, FirstOrderModel* model ) : d_f( f ), d_model( model ){
  //store instantiation constants
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    d_index.push_back( 0 );
  }
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    //store default index order
    d_index_order.push_back( i );
    d_var_order[i] = i;
    //store default domain
    d_domain.push_back( RepDomain() );
    for( int j=0; j<(int)d_model->d_ra.d_type_reps[d_f[0][i].getType()].size(); j++ ){
      d_domain[i].push_back( j );
    }
  }
}

void RepSetIterator::setIndexOrder( std::vector< int >& indexOrder ){
  d_index_order.clear();
  d_index_order.insert( d_index_order.begin(), indexOrder.begin(), indexOrder.end() );
  //make the d_var_order mapping
  for( int i=0; i<(int)d_index_order.size(); i++ ){
    d_var_order[d_index_order[i]] = i;
  }
}

void RepSetIterator::setDomain( std::vector< RepDomain >& domain ){
  d_domain.clear();
  d_domain.insert( d_domain.begin(), domain.begin(), domain.end() );
  //we are done if a domain is empty
  for( int i=0; i<(int)d_domain.size(); i++ ){
    if( d_domain[i].empty() ){
      d_index.clear();
    }
  }
}

void RepSetIterator::increment2( int counter ){
  Assert( !isFinished() );
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
  counter = (int)d_index.size()-1;
#endif
  //increment d_index
  while( counter>=0 && d_index[counter]==(int)(d_domain[counter].size()-1) ){
    counter--;
  }
  if( counter==-1 ){
    d_index.clear();
  }else{
    for( int i=(int)d_index.size()-1; i>counter; i-- ){
      d_index[i] = 0;
      //d_model->clearEvalFailed( i );
    }
    d_index[counter]++;
    //d_model->clearEvalFailed( counter );
  }
}

void RepSetIterator::increment(){
  if( !isFinished() ){
    increment2( (int)d_index.size()-1 );
  }
}

bool RepSetIterator::isFinished(){
  return d_index.empty();
}

void RepSetIterator::getMatch( QuantifiersEngine* qe, InstMatch& m ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    m.d_map[ qe->getTermDatabase()->getInstantiationConstant( d_f, d_index_order[i] ) ] = getTerm( i );
  }
}

Node RepSetIterator::getTerm( int i ){
  TypeNode tn = d_f[0][d_index_order[i]].getType();
  Assert( d_model->d_ra.d_type_reps.find( tn )!=d_model->d_ra.d_type_reps.end() );
  int index = d_index_order[i];
  return d_model->d_ra.d_type_reps[tn][d_domain[index][d_index[index]]];
}

void RepSetIterator::debugPrint( const char* c ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << i << " : " << d_index[i] << " : " << getTerm( i ) << std::endl;
  }
}

void RepSetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << d_index[i] << ": " << getTerm( i ) << " ";
  }
  Debug( c ) << std::endl;
}

RepSetEvaluator::RepSetEvaluator( FirstOrderModel* m, RepSetIterator* ri ) : d_model( m ), d_riter( ri ){

}

//if evaluate( n, phaseReq ) = eVal,
// if eVal = d_riter->d_index.size()
//   then the formula n instantiated with d_riter cannot be proven to be equal to phaseReq
// otherwise,
//   each n{d_riter->d_index[0]/x_0...d_riter->d_index[eVal]/x_eVal, */x_(eVal+1) ... */x_n } is equal to phaseReq in the current model
int RepSetEvaluator::evaluate( Node n, int& depIndex ){
  ++d_eval_formulas;
  //Debug("fmf-eval-debug") << "Evaluate " << n << " " << phaseReq << std::endl;
  //Notice() << "Eval " << n << std::endl;
  if( n.getKind()==NOT ){
    int val = evaluate( n[0], depIndex );
    return val==1 ? -1 : ( val==-1 ? 1 : 0 );
  }else if( n.getKind()==OR || n.getKind()==AND || n.getKind()==IMPLIES ){
    int baseVal = n.getKind()==AND ? 1 : -1;
    int eVal = baseVal;
    int posDepIndex = d_riter->getNumTerms();
    int negDepIndex = -1;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //evaluate subterm
      int childDepIndex;
      Node nn = ( i==0 && n.getKind()==IMPLIES ) ? n[i].notNode() : n[i];
      int eValT = evaluate( nn, childDepIndex );
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
    int eVal = evaluate( n[0], depIndex1 );
    if( eVal!=0 ){
      int depIndex2;
      int eVal2 = evaluate( n.getKind()==XOR ? n[1].notNode() : n[1], depIndex2 );
      if( eVal2!=0 ){
        depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
        return eVal==eVal2 ? 1 : -1;
      }
    }
    return 0;
  }else if( n.getKind()==ITE ){
    int depIndex1, depIndex2;
    int eVal = evaluate( n[0], depIndex1 );
    if( eVal==0 ){
      //evaluate children to see if they are the same value
      int eval1 = evaluate( n[1], depIndex1 );
      if( eval1!=0 ){
        int eval2 = evaluate( n[1], depIndex2 );
        if( eval1==eval2 ){
          depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
          return eval1;
        }
      }
    }else{
      int eValT = evaluate( n[eVal==1 ? 1 : 2], depIndex2 );
      depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
      return eValT;
    }
    return 0;
  }else if( n.getKind()==FORALL ){
    return 0;
  }else{
    ////if we know we will fail again, immediately return
    //if( d_eval_failed.find( n )!=d_eval_failed.end() ){
    //  if( d_eval_failed[n] ){
    //    return -1;
    //  }
    //}
    //Debug("fmf-eval-debug") << "Evaluate literal " << n << std::endl;
    //this should be a literal
    //Node gn = n.substitute( d_riter->d_ic.begin(), d_riter->d_ic.end(), d_riter->d_terms.begin(), d_riter->d_terms.end() );
    //Debug("fmf-eval-debug") << "  Ground version = " << gn << std::endl;
    int retVal = 0;
    depIndex = d_riter->getNumTerms()-1;
    if( n.getKind()==APPLY_UF ){
      //case for boolean predicates
      Node val = evaluateTerm( n, depIndex );
      if( d_model->hasTerm( val ) ){
        if( d_model->areEqual( val, d_model->d_true ) ){
          retVal = 1;
        }else{
          retVal = -1;
        }
      }
    }else if( n.getKind()==EQUAL ){
      //case for equality
      retVal = evaluateEquality( n[0], n[1], depIndex );
    }else{
      std::vector< int > cdi;
      Node val = evaluateTermDefault( n, depIndex, cdi );
      if( !val.isNull() ){
        val = Rewriter::rewrite( val );
        if( val==d_model->d_true ){
          retVal = 1;
        }else if( val==d_model->d_false ){
          retVal = -1;
        }
      }
    }
    if( retVal!=0 ){
      Debug("fmf-eval-debug") << "Evaluate literal: return " << retVal << ", depends = " << depIndex << std::endl;
    }else{
      Debug("fmf-eval-amb") << "Neither true nor false : " << n << std::endl;
      //std::cout << "Neither true nor false : " << n << std::endl;
    }
    return retVal;
  }
}

int RepSetEvaluator::evaluateEquality( Node n1, Node n2, int& depIndex ){
  ++d_eval_eqs;
  //Notice() << "Eval eq " << n1 << " " << n2 << std::endl;
  Debug("fmf-eval-debug") << "Evaluate equality: " << std::endl;
  Debug("fmf-eval-debug") << "   " << n1 << " = " << n2 << std::endl;
  int depIndex1, depIndex2;
  Node val1 = evaluateTerm( n1, depIndex1 );
  Node val2 = evaluateTerm( n2, depIndex2 );
  Debug("fmf-eval-debug") << "   Values :  ";
  d_model->printRepresentativeDebug( "fmf-eval-debug", val1 );
  Debug("fmf-eval-debug") <<  " = ";
  d_model->printRepresentativeDebug( "fmf-eval-debug", val2 );
  Debug("fmf-eval-debug") << std::endl;
  int retVal = 0;
  if( !val1.isNull() && !val2.isNull() ){
    if( d_model->areEqual( val1, val2 ) ){
      retVal = 1;
    }else if( d_model->areDisequal( val1, val2 ) ){
      retVal = -1;
    }else{
      Node eq = val1.eqNode( val2 );
      eq = Rewriter::rewrite( eq );
      if( eq==d_model->d_true ){
        retVal = 1;
      }else if( eq==d_model->d_false ){
        retVal = -1;
      }
    }
  }
  if( retVal!=0 ){
    depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
    Debug("fmf-eval-debug") << "   value = " << (retVal==1) << ", depIndex = " << depIndex << std::endl;
  }else{
    depIndex = d_riter->getNumTerms()-1;
    Debug("fmf-eval-amb") << "Neither equal nor disequal : " << n1 << " , " << n2 << std::endl;
    //std::cout << "Neither equal nor disequal : " << n1 << " , " << n2 << std::endl;
  }
  return retVal;
}

Node RepSetEvaluator::evaluateTerm( Node n, int& depIndex ){
  //Notice() << "Eval term " << n << std::endl;
  if( n.hasAttribute(InstConstantAttribute()) ){
    Node val;
    depIndex = d_riter->getNumTerms()-1;
    //check the type of n
    if( n.getKind()==INST_CONSTANT ){
      int v = n.getAttribute(InstVarNumAttribute());
      depIndex = d_riter->d_var_order[ v ];
      val = d_riter->getTerm( v );
    }else if( n.getKind()==ITE ){
      int depIndex1, depIndex2;
      int eval = evaluate( n[0], depIndex1 );
      if( eval==0 ){
        //evaluate children to see if they are the same
        Node val1 = evaluateTerm( n[ 1 ], depIndex1 );
        Node val2 = evaluateTerm( n[ 1 ], depIndex1 );
        if( val1==val2 ){
          val = val1;
          depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
        }else{
          return Node::null();
        }
      }else{
        val = evaluateTerm( n[ eval==1 ? 1 : 2 ], depIndex2 );
        depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
      }
    }else{
#if 0
      //for select, pre-process read over writes
      if( n.getKind()==SELECT ){
        Node selIndex = evaluateTerm( n[1], depIndex );
        if( selIndex.isNull() ){
          depIndex = d_riter->getNumTerms()-1;
          return Node::null();
        }
        Node arr = n[0];
        int eval = 1;
        while( arr.getKind()==STORE && eval!=0 ){
          int tempIndex;
          eval = evaluateEquality( selIndex, arr[1], tempIndex );
          depIndex = tempIndex > depIndex ? tempIndex : depIndex;
          if( eval==1 ){
            val = evaluateTerm( arr[2], tempIndex );
            depIndex = tempIndex > depIndex ? tempIndex : depIndex;
            return val;
          }else if( eval==-1 ){
            arr = arr[0];
          }
        }
        n = NodeManager::currentNM()->mkNode( SELECT, arr, selIndex );
      }
#endif
      //default term evaluate : evaluate all children, recreate the value
      std::vector< int > children_depIndex;
      val = evaluateTermDefault( n, depIndex, children_depIndex );
      //case split on the type of term
      if( n.getKind()==APPLY_UF ){
        Node op = n.getOperator();
        //Debug("fmf-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
        //if it is a defined UF, then consult the interpretation
        ++d_eval_uf_terms;
        int argDepIndex = 0;
        if( d_model->d_uf_model.find( op )!=d_model->d_uf_model.end() ){
          //make the term model specifically for n
          makeEvalUfModel( n );
          //now, consult the model
          if( d_eval_uf_use_default[n] ){
            val = d_model->d_uf_model[op].d_tree.getValue( d_model, val, argDepIndex );
          }else{
            val = d_eval_uf_model[ n ].getValue( d_model, val, argDepIndex );
          }
          //Debug("fmf-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
          //d_eval_uf_model[ n ].debugPrint("fmf-eval-debug", d_qe );
          Assert( !val.isNull() );
        }else{
          d_eval_uf_use_default[n] = true;
          argDepIndex = (int)n.getNumChildren();
        }
        //recalculate the depIndex
        depIndex = -1;
        for( int i=0; i<argDepIndex; i++ ){
          int index = d_eval_uf_use_default[n] ? i : d_eval_term_index_order[n][i];
          Debug("fmf-eval-debug") << "Add variables from " << index << "..." << std::endl;
          if( children_depIndex[index]>depIndex ){
            depIndex = children_depIndex[index];
          }
        }
        Debug("fmf-eval-debug") << "Evaluate term " << n << " = ";
        d_model->printRepresentativeDebug( "fmf-eval-debug", val );
        Debug("fmf-eval-debug") << ", depIndex = " << depIndex << std::endl;
      }else if( n.getKind()==SELECT ){
        if( d_model->d_array_model.find( n[0] )!=d_model->d_array_model.end() ){
          //consult the default value for the array DO_THIS
          //val = Rewriter::rewrite( val );
          //val = d_model->d_array_model[ n[0] ];
          val = Rewriter::rewrite( val );
        }else{
          val = Rewriter::rewrite( val );
        }
      }else{
        val = Rewriter::rewrite( val );
      }
    }
    return val;
  }else{
    depIndex = -1;
    return n;
  }
}

Node RepSetEvaluator::evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex ){
  //first we must evaluate the arguments
  std::vector< Node > children;
  if( n.getMetaKind()==kind::metakind::PARAMETERIZED ){
    children.push_back( n.getOperator() );
  }
  depIndex = -1;
  //for each argument, calculate its value, and the variables its value depends upon
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    childDepIndex.push_back( -1 );
    Node nn = evaluateTerm( n[i], childDepIndex[i] );
    if( nn.isNull() ){
      depIndex = d_riter->getNumTerms()-1;
      return nn;
    }else{
      children.push_back( nn );
      if( childDepIndex[i]>depIndex ){
        depIndex = childDepIndex[i];
      }
    }
  }
  //recreate the value
  return NodeManager::currentNM()->mkNode( n.getKind(), children );
}

void RepSetEvaluator::clearEvalFailed( int index ){
  for( int i=0; i<(int)d_eval_failed_lits[index].size(); i++ ){
    d_eval_failed[ d_eval_failed_lits[index][i] ] = false;
  }
  d_eval_failed_lits[index].clear();
}

void RepSetEvaluator::makeEvalUfModel( Node n ){
  if( d_eval_uf_model.find( n )==d_eval_uf_model.end() ){
    makeEvalUfIndexOrder( n );
    if( !d_eval_uf_use_default[n] ){
      Node op = n.getOperator();
      d_eval_uf_model[n] = uf::UfModelTreeOrdered( op, d_eval_term_index_order[n] );
      d_model->d_uf_model[op].makeModel( d_eval_uf_model[n] );
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

void RepSetEvaluator::makeEvalUfIndexOrder( Node n ){
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


