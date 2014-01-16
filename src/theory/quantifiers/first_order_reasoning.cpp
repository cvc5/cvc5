/*********************                                                        */
/*! \file first_order_reasoning.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief first order reasoning module
 **
 **/

#include <vector>

#include "theory/quantifiers/first_order_reasoning.h"
#include "theory/rewriter.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace std;

namespace CVC4 {


void FirstOrderPropagation::collectLits( Node n, std::vector<Node> & lits ){
  if( n.getKind()==FORALL ){
    collectLits( n[1], lits );
  }else if( n.getKind()==OR ){
    for(unsigned j=0; j<n.getNumChildren(); j++) {
      collectLits(n[j], lits );
    }
  }else{
    lits.push_back( n );
  }
}

void FirstOrderPropagation::simplify( std::vector< Node >& assertions ){
  for( unsigned i=0; i<assertions.size(); i++) {
    Trace("fo-rsn") << "Assert : " << assertions[i] << std::endl;
  }

  //process all assertions
  int num_processed;
  int num_true = 0;
  int num_rounds = 0;
  do {
    num_processed = 0;
    for( unsigned i=0; i<assertions.size(); i++ ){
      if( d_assertion_true.find(assertions[i])==d_assertion_true.end() ){
        std::vector< Node > fo_lits;
        collectLits( assertions[i], fo_lits );
        Node unitLit = process( assertions[i], fo_lits );
        if( !unitLit.isNull() ){
          Trace("fo-rsn-debug") << "...possible unit literal : " << unitLit << " from " << assertions[i] << std::endl;
          bool pol = unitLit.getKind()!=NOT;
          unitLit = unitLit.getKind()==NOT ? unitLit[0] : unitLit;
          if( unitLit.getKind()==EQUAL ){

          }else if( unitLit.getKind()==APPLY_UF ){
            //make sure all are unique vars;
            bool success = true;
            std::vector< Node > unique_vars;
            for( unsigned j=0; j<unitLit.getNumChildren(); j++) {
              if( unitLit[j].getKind()==BOUND_VARIABLE ){
                if( std::find(unique_vars.begin(), unique_vars.end(), unitLit[j])==unique_vars.end() ){
                  unique_vars.push_back( unitLit[j] );
                }else{
                  success = false;
                  break;
                }
              }else{
                success = false;
                break;
              }
            }
            if( success ){
              d_const_def[unitLit.getOperator()] = NodeManager::currentNM()->mkConst(pol);
              Trace("fo-rsn") << "Propagate : " << unitLit.getOperator() << " == " << pol << std::endl;
              Trace("fo-rsn") << "    from : " << assertions[i] << std::endl;
              d_assertion_true[assertions[i]] = true;
              num_processed++;
            }
          }else if( unitLit.getKind()==VARIABLE ){
            d_const_def[unitLit] = NodeManager::currentNM()->mkConst(pol);
            Trace("fo-rsn") << "Propagate variable : " << unitLit << " == " << pol << std::endl;
            Trace("fo-rsn") << "    from : " << assertions[i] << std::endl;
            d_assertion_true[assertions[i]] = true;
            num_processed++;
          }
        }
        if( d_assertion_true.find(assertions[i])!=d_assertion_true.end() ){
          num_true++;
        }
      }
    }
    num_rounds++;
  }while( num_processed>0 );
  Trace("fo-rsn-sum") << "Simplified " << num_true << " / " << assertions.size() << " in " << num_rounds << " rounds." << std::endl;
  for( unsigned i=0; i<assertions.size(); i++ ){
    assertions[i] = theory::Rewriter::rewrite( simplify( assertions[i] ) );
  }
}

Node FirstOrderPropagation::process(Node a, std::vector< Node > & lits) {
  int index = -1;
  for( unsigned i=0; i<lits.size(); i++) {
    bool pol = lits[i].getKind()!=NOT;
    Node n = lits[i].getKind()==NOT ? lits[i][0] : lits[i];
    Node litDef;
    if( n.getKind()==APPLY_UF ){
      if( d_const_def.find(n.getOperator())!=d_const_def.end() ){
        litDef = d_const_def[n.getOperator()];
      }
    }else if( n.getKind()==VARIABLE ){
      if( d_const_def.find(n)!=d_const_def.end() ){
        litDef = d_const_def[n];
      }
    }
    if( !litDef.isNull() ){
      Node poln = NodeManager::currentNM()->mkConst( pol );
      if( litDef==poln ){
        Trace("fo-rsn-debug") << "Assertion " << a << " is true because of " << lits[i] << std::endl;
        d_assertion_true[a] = true;
        return Node::null();
      }
    }
    if( litDef.isNull() ){
      if( index==-1 ){
        //store undefined index
        index = i;
      }else{
        //two undefined, return null
        return Node::null();
      }
    }
  }
  if( index!=-1 ){
    return lits[index];
  }else{
    return Node::null();
  }
}

Node FirstOrderPropagation::simplify( Node n ) {
  if( n.getKind()==VARIABLE ){
    if( d_const_def.find(n)!=d_const_def.end() ){
      return d_const_def[n];
    }
  }else if( n.getKind()==APPLY_UF ){
    if( d_const_def.find(n.getOperator())!=d_const_def.end() ){
      return d_const_def[n.getOperator()];
    }
  }
  if( n.getNumChildren()==0 ){
    return n;
  }else{
    std::vector< Node > children;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      children.push_back( n.getOperator() );
    }
    for(unsigned i=0; i<n.getNumChildren(); i++) {
      children.push_back( simplify(n[i]) );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }
}

}
