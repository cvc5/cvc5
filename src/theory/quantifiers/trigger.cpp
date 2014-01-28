/*********************                                                        */
/*! \file trigger.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of trigger class
 **/

#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/inst_match_generator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

/** trigger class constructor */
Trigger::Trigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption, bool smartTriggers ) :
d_quantEngine( qe ), d_f( f ){
  d_nodes.insert( d_nodes.begin(), nodes.begin(), nodes.end() );
  Trace("trigger") << "Trigger for " << f << ": " << std::endl;
  for( int i=0; i<(int)d_nodes.size(); i++ ){
    Trace("trigger") << "   " << d_nodes[i] << std::endl;
  }
  Trace("trigger-debug") << ", smart triggers = " << smartTriggers;
  Trace("trigger") << std::endl;
  if( smartTriggers ){
    if( d_nodes.size()==1 ){
      if( isSimpleTrigger( d_nodes[0] ) ){
        d_mg = new InstMatchGeneratorSimple( f, d_nodes[0] );
      }else{
        d_mg = InstMatchGenerator::mkInstMatchGenerator( d_nodes[0], qe );
        d_mg->setActiveAdd(true);
      }
    }else{
      d_mg = new InstMatchGeneratorMulti( f, d_nodes, qe, matchOption );
      //d_mg = InstMatchGenerator::mkInstMatchGenerator( d_nodes, qe );
      //d_mg->setActiveAdd();
    }
  }else{
    d_mg = InstMatchGenerator::mkInstMatchGenerator( d_nodes, qe );
    d_mg->setActiveAdd(true);
  }
  if( d_nodes.size()==1 ){
    if( isSimpleTrigger( d_nodes[0] ) ){
      ++(qe->d_statistics.d_triggers);
    }else{
      ++(qe->d_statistics.d_simple_triggers);
    }
  }else{
    Trace("multi-trigger") << "Multi-trigger " << (*this) << " for " << f << std::endl;
    //Notice() << "Multi-trigger for " << f << " : " << std::endl;
    //Notice() << "   " << (*this) << std::endl;
    ++(qe->d_statistics.d_multi_triggers);
  }
  //Notice() << "Trigger : " << (*this) << "  for " << f << std::endl;
  if( options::eagerInstQuant() ){
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      Node op = qe->getTermDatabase()->getOperator( d_nodes[i] );
      qe->getTermDatabase()->registerTrigger( this, op );
    }
  }
  Trace("trigger-debug") << "Finished making trigger." << std::endl;
}

void Trigger::resetInstantiationRound(){
  d_mg->resetInstantiationRound( d_quantEngine );
}

void Trigger::reset( Node eqc ){
  d_mg->reset( eqc, d_quantEngine );
}

bool Trigger::getNextMatch( Node f, InstMatch& m ){
  bool retVal = d_mg->getNextMatch( f, m, d_quantEngine );
  return retVal;
}

bool Trigger::getMatch( Node f, Node t, InstMatch& m ){
  //FIXME: this assumes d_mg is an inst match generator
  return ((InstMatchGenerator*)d_mg)->getMatch( f, t, m, d_quantEngine );
}

int Trigger::addTerm( Node t ){
  return d_mg->addTerm( d_f, t, d_quantEngine );
}

int Trigger::addInstantiations( InstMatch& baseMatch ){
  int addedLemmas = d_mg->addInstantiations( d_f, baseMatch, d_quantEngine );
  if( addedLemmas>0 ){
    Debug("inst-trigger") << "Added " << addedLemmas << " lemmas, trigger was ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      Debug("inst-trigger") << d_nodes[i] << " ";
    }
    Debug("inst-trigger") << std::endl;
  }
  return addedLemmas;
}

Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, std::vector< Node >& nodes, int matchOption, bool keepAll, int trOption,
                             bool smartTriggers ){
  std::vector< Node > trNodes;
  if( !keepAll ){
    //only take nodes that contribute variables to the trigger when added
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::map< Node, bool > vars;
    std::map< Node, std::vector< Node > > patterns;
    size_t varCount = 0;
    for( int i=0; i<(int)temp.size(); i++ ){
      bool foundVar = false;
      qe->getTermDatabase()->computeVarContains( temp[i] );
      for( int j=0; j<(int)qe->getTermDatabase()->d_var_contains[ temp[i] ].size(); j++ ){
        Node v = qe->getTermDatabase()->d_var_contains[ temp[i] ][j];
        if( quantifiers::TermDb::getInstConstAttr(v)==f ){
          if( vars.find( v )==vars.end() ){
            varCount++;
            vars[ v ] = true;
            foundVar = true;
          }
        }
      }
      if( foundVar ){
        trNodes.push_back( temp[i] );
        for( int j=0; j<(int)qe->getTermDatabase()->d_var_contains[ temp[i] ].size(); j++ ){
          Node v = qe->getTermDatabase()->d_var_contains[ temp[i] ][j];
          patterns[ v ].push_back( temp[i] );
        }
      }
      if( varCount==f[0].getNumChildren() ){
        break;
      }
    }
    if( varCount<f[0].getNumChildren() ){
      Trace("trigger-debug") << "Don't consider trigger since it does not contain all variables in " << f << std::endl;
      for( unsigned i=0; i<nodes.size(); i++) {
        Trace("trigger-debug") << nodes[i] << " ";
      }
      Trace("trigger-debug") << std::endl;

      //do not generate multi-trigger if it does not contain all variables
      return NULL;
    }else{
      //now, minimize the trigger
      for( int i=0; i<(int)trNodes.size(); i++ ){
        bool keepPattern = false;
        Node n = trNodes[i];
        for( int j=0; j<(int)qe->getTermDatabase()->d_var_contains[ n ].size(); j++ ){
          Node v = qe->getTermDatabase()->d_var_contains[ n ][j];
          if( patterns[v].size()==1 ){
            keepPattern = true;
            break;
          }
        }
        if( !keepPattern ){
          //remove from pattern vector
          for( int j=0; j<(int)qe->getTermDatabase()->d_var_contains[ n ].size(); j++ ){
            Node v = qe->getTermDatabase()->d_var_contains[ n ][j];
            for( int k=0; k<(int)patterns[v].size(); k++ ){
              if( patterns[v][k]==n ){
                patterns[v].erase( patterns[v].begin() + k, patterns[v].begin() + k + 1 );
                break;
              }
            }
          }
          //remove from trigger nodes
          trNodes.erase( trNodes.begin() + i, trNodes.begin() + i + 1 );
          i--;
        }
      }
    }
  }else{
    trNodes.insert( trNodes.begin(), nodes.begin(), nodes.end() );
  }

  //check for duplicate?
  if( trOption==TR_MAKE_NEW ){
    //static int trNew = 0;
    //static int trOld = 0;
    //Trigger* t = qe->getTermDatabase()->getTrigger( trNodes );
    //if( t ){
    //  trOld++;
    //}else{
    //  trNew++;
    //}
    //if( (trNew+trOld)%100==0 ){
    //  Notice() << "Trigger new old = " << trNew << " " << trOld << std::endl;
    //}
  }else{
    Trigger* t = qe->getTriggerDatabase()->getTrigger( trNodes );
    if( t ){
      if( trOption==TR_GET_OLD ){
        //just return old trigger
        return t;
      }else{
        return NULL;
      }
    }
  }
  Trigger* t = new Trigger( qe, f, trNodes, matchOption, smartTriggers );
  qe->getTriggerDatabase()->addTrigger( trNodes, t );
  return t;
}
Trigger* Trigger::mkTrigger( QuantifiersEngine* qe, Node f, Node n, int matchOption, bool keepAll, int trOption, bool smartTriggers ){
  std::vector< Node > nodes;
  nodes.push_back( n );
  return mkTrigger( qe, f, nodes, matchOption, keepAll, trOption, smartTriggers );
}

bool Trigger::isUsableTrigger( std::vector< Node >& nodes, Node f ){
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( !isUsableTrigger( nodes[i], f ) ){
      return false;
    }
  }
  return true;
}

bool Trigger::isUsable( Node n, Node f ){
  if( quantifiers::TermDb::getInstConstAttr(n)==f ){
    if( isAtomicTrigger( n ) ){
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        if( !isUsable( n[i], f ) ){
          return false;
        }
      }
      return true;
    }else if( n.getKind()==INST_CONSTANT ){
      return true;
    }else{
      std::map< Node, Node > coeffs;
      if( isArithmeticTrigger( f, n, coeffs ) ){
        return true;
      }else if( isBooleanTermTrigger( n ) ){
        return true;
      }
    }
    return false;
  }else{
    return true;
  }
}

bool nodeContainsVar( Node n, Node v ){
  if( n==v) {
    return true;
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++) {
      if( nodeContainsVar(n[i], v) ){
        return true;
      }
    }
    return false;
  }
}

Node Trigger::getIsUsableTrigger( Node n, Node f, bool pol, bool hasPol ) {
  if( options::relationalTriggers() ){
    if( n.getKind()==EQUAL || n.getKind()==IFF || n.getKind()==GEQ ){
      Node rtr;
      for( unsigned i=0; i<2; i++) {
        unsigned j = (i==0) ? 1 : 0;
        if( n[j].getKind()==INST_CONSTANT && isUsableTrigger(n[i], f) && !nodeContainsVar( n[i], n[j] ) ) {
          rtr = n;
          break;
        }
      }
      if( n[0].getType().isInteger() ){
        //try to rearrange?
        std::map< Node, Node > m;
        if (QuantArith::getMonomialSumLit(n, m) ){
          for( std::map< Node, Node >::iterator it = m.begin(); it!=m.end(); ++it ){
            if( !it->first.isNull() && it->first.getKind()==INST_CONSTANT ){
              Node veq;
              if( QuantArith::isolate( it->first, m, veq, n.getKind() ) ){
                int vti = veq[0]==it->first ? 1 : 0;
                if( isUsableTrigger(veq[vti], f) && !nodeContainsVar( veq[vti], veq[vti==0 ? 1 : 0]) ){
                  rtr = veq;
                }
              }
            }
          }
        }
      }
      if( !rtr.isNull() ){
        Trace("relational-trigger") << "Relational trigger : " << std::endl;
        Trace("relational-trigger") << "    " << rtr << " (from " << n << ")" << std::endl;
        Trace("relational-trigger") << "    in quantifier " << f << std::endl;
        if( hasPol ){
          Trace("relational-trigger") << "    polarity : " << pol << std::endl;
        }
        Node rtr2 = (hasPol && pol) ? rtr.negate() : rtr;
        return rtr2;
      }
    }
  }
  bool usable = quantifiers::TermDb::getInstConstAttr(n)==f && isAtomicTrigger( n ) && isUsable( n, f );
  Trace("usable") << n << " usable : " << (quantifiers::TermDb::getInstConstAttr(n)==f) << " " << isAtomicTrigger( n ) << " " << isUsable( n, f ) << std::endl;
  if( usable ){
    return n;
  }else{
    return Node::null();
  }
}

bool Trigger::isUsableTrigger( Node n, Node f ){
  Node nu = getIsUsableTrigger(n,f);
  return !nu.isNull();
}

bool Trigger::isAtomicTrigger( Node n ){
  return ( n.getKind()==APPLY_UF && !n.getOperator().getAttribute(NoMatchAttribute()) ) || n.getKind()==SELECT || n.getKind()==STORE ||
         n.getKind()==APPLY_CONSTRUCTOR || n.getKind()==APPLY_SELECTOR || n.getKind()==APPLY_TESTER;
}
bool Trigger::isSimpleTrigger( Node n ){
  if( isAtomicTrigger( n ) ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n[i].getKind()!=INST_CONSTANT && quantifiers::TermDb::hasInstConstAttr(n[i]) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}


bool Trigger::collectPatTerms2( QuantifiersEngine* qe, Node f, Node n, std::map< Node, bool >& patMap, int tstrt, bool pol, bool hasPol ){
  if( patMap.find( n )==patMap.end() ){
    patMap[ n ] = false;
    bool newHasPol = n.getKind()==IFF ? false : hasPol;
    bool newPol = n.getKind()==NOT ? !pol : pol;
    if( tstrt==TS_MIN_TRIGGER ){
      if( n.getKind()==FORALL ){
        return false;
      }else{
        bool retVal = false;
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          bool newHasPol2 = (n.getKind()==ITE && i==0) ? false : newHasPol;
          if( collectPatTerms2( qe, f, n[i], patMap, tstrt, newPol, newHasPol2 ) ){
            retVal = true;
          }
        }
        if( retVal ){
          return true;
        }else{
          Node nu = getIsUsableTrigger( n, f, pol, hasPol );
          if( !nu.isNull() ){
            patMap[ nu ] = true;
            return true;
          }else{
            return false;
          }
        }
      }
    }else{
      bool retVal = false;
      Node nu = getIsUsableTrigger( n, f, pol, hasPol );
      if( !nu.isNull() ){
        patMap[ nu ] = true;
        if( tstrt==TS_MAX_TRIGGER ){
          return true;
        }else{
          retVal = true;
        }
      }
      if( n.getKind()!=FORALL ){
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          bool newHasPol2 = (n.getKind()==ITE && i==0) ? false : newHasPol;
          if( collectPatTerms2( qe, f, n[i], patMap, tstrt, newPol, newHasPol2 ) ){
            retVal = true;
          }
        }
      }
      return retVal;
    }
  }else{
    return patMap[ n ];
  }
}

void Trigger::collectPatTerms( QuantifiersEngine* qe, Node f, Node n, std::vector< Node >& patTerms, int tstrt, bool filterInst ){
  std::map< Node, bool > patMap;
  if( filterInst ){
    //immediately do not consider any term t for which another term is an instance of t
    std::vector< Node > patTerms2;
    collectPatTerms( qe, f, n, patTerms2, TS_ALL, false );
    std::vector< Node > temp;
    temp.insert( temp.begin(), patTerms2.begin(), patTerms2.end() );
    qe->getTermDatabase()->filterInstances( temp );
    if( temp.size()!=patTerms2.size() ){
      Trace("trigger-filter-instance") << "Filtered an instance: " << std::endl;
      Trace("trigger-filter-instance") << "Old: ";
      for( int i=0; i<(int)patTerms2.size(); i++ ){
        Trace("trigger-filter-instance") << patTerms2[i] << " ";
      }
      Trace("trigger-filter-instance") << std::endl << "New: ";
      for( int i=0; i<(int)temp.size(); i++ ){
        Trace("trigger-filter-instance") << temp[i] << " ";
      }
      Trace("trigger-filter-instance") << std::endl;
    }
    if( tstrt==TS_ALL ){
      patTerms.insert( patTerms.begin(), temp.begin(), temp.end() );
      return;
    }else{
      //do not consider terms that have instances
      for( int i=0; i<(int)patTerms2.size(); i++ ){
        if( std::find( temp.begin(), temp.end(), patTerms2[i] )==temp.end() ){
          patMap[ patTerms2[i] ] = false;
        }
      }
    }
  }
  collectPatTerms2( qe, f, n, patMap, tstrt, true, true );
  for( std::map< Node, bool >::iterator it = patMap.begin(); it != patMap.end(); ++it ){
    if( it->second ){
      patTerms.push_back( it->first );
    }
  }
}

bool Trigger::isArithmeticTrigger( Node f, Node n, std::map< Node, Node >& coeffs ){
  if( n.getKind()==PLUS ){
    Assert( coeffs.empty() );
    NodeBuilder<> t(kind::PLUS);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( quantifiers::TermDb::hasInstConstAttr(n[i]) ){
        if( n[i].getKind()==INST_CONSTANT ){
          if( quantifiers::TermDb::getInstConstAttr(n[i])==f ){
            coeffs[ n[i] ] = Node::null();
          }else{
            coeffs.clear();
            return false;
          }
        }else if( !isArithmeticTrigger( f, n[i], coeffs ) ){
          coeffs.clear();
          return false;
        }
      }else{
        t << n[i];
      }
    }
    if( t.getNumChildren()==0 ){
      coeffs[ Node::null() ] = NodeManager::currentNM()->mkConst( Rational(0) );
    }else if( t.getNumChildren()==1 ){
      coeffs[ Node::null() ]  = t.getChild( 0 );
    }else{
      coeffs[ Node::null() ]  = t;
    }
    return true;
  }else if( n.getKind()==MULT ){
    if( n[0].getKind()==INST_CONSTANT && quantifiers::TermDb::getInstConstAttr(n[0])==f ){
      if( !quantifiers::TermDb::hasInstConstAttr(n[1]) ){
        coeffs[ n[0] ] = n[1];
        return true;
      }
    }else if( n[1].getKind()==INST_CONSTANT && quantifiers::TermDb::getInstConstAttr(n[1])==f ){
      if( !quantifiers::TermDb::hasInstConstAttr(n[0]) ){
        coeffs[ n[1] ] = n[0];
        return true;
      }
    }
  }
  return false;
}

bool Trigger::isBooleanTermTrigger( Node n ) {
  if( n.getKind()==ITE ){
    //check for boolean term converted to ITE
    if( n[0].getKind()==INST_CONSTANT &&
        n[1].getKind()==CONST_BITVECTOR &&
        n[2].getKind()==CONST_BITVECTOR ){
      if( ((BitVectorType)n[1].getType().toType()).getSize()==1 &&
          n[1].getConst<BitVector>().toInteger()==1 &&
          n[2].getConst<BitVector>().toInteger()==0 ){
        return true;
      }
    }
  }
  return false;
}

Trigger* TriggerTrie::getTrigger2( std::vector< Node >& nodes ){
  if( nodes.empty() ){
    return d_tr;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )!=d_children.end() ){
      return d_children[n]->getTrigger2( nodes );
    }else{
      return NULL;
    }
  }
}

void TriggerTrie::addTrigger2( std::vector< Node >& nodes, Trigger* t ){
  if( nodes.empty() ){
    d_tr = t;
  }else{
    Node n = nodes.back();
    nodes.pop_back();
    if( d_children.find( n )==d_children.end() ){
      d_children[n] = new TriggerTrie;
    }
    d_children[n]->addTrigger2( nodes, t );
  }
}
