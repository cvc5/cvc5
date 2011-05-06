#include "theory/datatypes/explanation_manager.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::datatypes;

void ProofManager::setExplanation( Node n, Node jn, unsigned r ) 
{ 
  Assert( n!=jn );
  d_exp[n] = std::pair< Node, unsigned >( jn, r ); 
}

//std::ostream& operator<<(std::ostream& os, Reason::Rule r)
//{
//  switch( r ){
//    
//  }
//}

void ExplanationManager::process( Node n, NodeBuilder<>& nb, ProofManager* pm )
{
  if( n.getKind()==kind::AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ) {
      process( n[i], nb, pm );
    }
  }else{
    if( !pm->hasExplained( n ) ){
      context::CDMap< Node, Reason, NodeHashFunction >::iterator it = d_drv_map.find( n );
      Reason r;
      Node exp;
      if( it!=d_drv_map.end() ){
        r = (*it).second;
        if( !r.d_isInput ){
          if( r.d_e ){

            Debug("emanager") << "Em::process: Consult externally for " << n << std::endl;
            exp = r.d_e->explain( n, pm );
            //trivial case, explainer says that n is an input
            if( exp==n ){
              r.d_isInput = true;
            }
          }else{
            exp = r.d_node;
            pm->setExplanation( n, exp, r.d_reason );
            if( exp.isNull() ) Debug("emanager") << "Em::process: " << n << " is an axiom, reason = " << r.d_reason << endl;
          }
        }
      }

      if( r.d_isInput ){
        Debug("emanager") << "Em::process: " << n << " is an input " << endl;
        nb << n;
        pm->setExplanation( n, Node::null(), Reason::input );
      }else if( !exp.isNull() ){
        Debug("emanager") << "Em::process: " << exp << " is the explanation for " << n << " " 
                          << ", reason = " << pm->getReason( n ) << endl;
        if( exp.getKind()==kind::AND ){
          for( int i=0; i<(int)exp.getNumChildren(); i++ ) {
            process( exp[i], nb, pm );
          }
        }else{
          process( exp, nb, pm );
        }
      }
    }else{
      Debug("emanager") << "Em::process: proof manager has already explained " << n << endl;
    }
  }
}

Node ExplanationManager::explain( Node n, ProofManager* pm )
{
  NodeBuilder<> nb(kind::AND);
  if( pm ){
    pm->clear();
    process( n, nb, pm );
  }else{
    ProofManager pm;
    process( n, nb, &pm );
  }
  return ( nb.getNumChildren() == 1 ) ? nb.getChild( 0 ) : nb;
}
