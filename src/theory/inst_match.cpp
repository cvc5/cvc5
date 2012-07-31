/*********************                                                        */
/*! \file inst_match.cpp
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
 ** \brief Implementation of inst match class
 **/

#include "theory/inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/candidate_generator.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;


InstMatch::InstMatch() {
}

InstMatch::InstMatch( InstMatch* m ) {
  d_map = m->d_map;
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m, bool & set ){
  std::map< Node, Node >::iterator vn = d_map.find( v );
  if( vn==d_map.end() ){
    set = true;
    this->set(v,m);
    Debug("matching-debug") << "Add partial " << v << "->" << m << std::endl;
    return true;
  }else{
    set = false;
    return q->areEqual( vn->second, m );
  }
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m ){
  bool set;
  return setMatch(q,v,m,set);
}

bool InstMatch::add( InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      d_map[it->first] = it->second;
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( d_map.find( it->first )==d_map.end() ){
      d_map[ it->first ] = it->second;
    }else{
      if( it->second!=d_map[it->first] ){
        if( !q->areEqual( it->second, d_map[it->first] ) ){
          d_map.clear();
          return false;
        }
      }
    }
  }
  return true;
}

void InstMatch::debugPrint( const char* c ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    Debug( c ) << "   " << it->first << " -> " << it->second << std::endl;
  }
  //if( !d_splits.empty() ){
  //  Debug( c ) << "   Conditions: ";
  //  for( std::map< Node, Node >::iterator it = d_splits.begin(); it !=d_splits.end(); ++it ){
  //    Debug( c ) << it->first << " = " << it->second << " ";
  //  }
  //  Debug( c ) << std::endl;
  //}
}

void InstMatch::makeComplete( Node f, QuantifiersEngine* qe ){
  for( int i=0; i<(int)qe->getTermDatabase()->d_inst_constants[f].size(); i++ ){
    Node ic = qe->getTermDatabase()->d_inst_constants[f][i];
    if( d_map.find( ic )==d_map.end() ){
      d_map[ ic ] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
}

void InstMatch::makeInternal( QuantifiersEngine* qe ){
  if( options::cbqi() ){
    for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
      if( it->second.hasAttribute(InstConstantAttribute()) ){
        d_map[ it->first ] = qe->getEqualityQuery()->getInternalRepresentative( it->second );
        if( it->second.hasAttribute(InstConstantAttribute()) ){
          d_map[ it->first ] = qe->getTermDatabase()->getFreeVariableForInstConstant( it->first );
        }
      }
    }
  }
}

void InstMatch::makeRepresentative( QuantifiersEngine* qe ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    d_map[ it->first ] = qe->getEqualityQuery()->getInternalRepresentative( it->second );
    if( options::cbqi() && it->second.hasAttribute(InstConstantAttribute()) ){
      d_map[ it->first ] = qe->getTermDatabase()->getFreeVariableForInstConstant( it->first );
    }
  }
}

void InstMatch::applyRewrite(){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    it->second = Rewriter::rewrite(it->second);
  }
}

void InstMatch::computeTermVec( QuantifiersEngine* qe, const std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    std::map< Node, Node >::iterator it = d_map.find( vars[i] );
    if( it!=d_map.end() && !it->second.isNull() ){
      match.push_back( it->second );
    }else{
      match.push_back( qe->getTermDatabase()->getFreeVariableForInstConstant( vars[i] ) );
    }
  }
}
void InstMatch::computeTermVec( const std::vector< Node >& vars, std::vector< Node >& match ){
  for( int i=0; i<(int)vars.size(); i++ ){
    match.push_back( d_map[ vars[i] ] );
  }
}


/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
void InstMatchTrie::addInstMatch2( QuantifiersEngine* qe, Node f, InstMatch& m, int index, ImtIndexOrder* imtio ){
  if( long(index)<long(f[0].getNumChildren()) && ( !imtio || long(index)<long(imtio->d_order.size()) ) ){
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.get( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    d_data[n].addInstMatch2( qe, f, m, index+1, imtio );
  }
}

/** exists match */
bool InstMatchTrie::existsInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, int index, ImtIndexOrder* imtio ){
  if( long(index)==long(f[0].getNumChildren()) || ( imtio && long(index)==long(imtio->d_order.size()) ) ){
    return true;
  }else{
    int i_index = imtio ? imtio->d_order[index] : index;
    Node n = m.get( qe->getTermDatabase()->getInstantiationConstant( f, i_index ) );
    std::map< Node, InstMatchTrie >::iterator it = d_data.find( n );
    if( it!=d_data.end() ){
      if( it->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
        return true;
      }
    }
    if( modEq ){
      //check modulo equality if any other instantiation match exists
      if( qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
        eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                 qe->getEqualityQuery()->getEngine() );
        while( !eqc.isFinished() ){
          Node en = (*eqc);
          if( en!=n ){
            std::map< Node, InstMatchTrie >::iterator itc = d_data.find( en );
            if( itc!=d_data.end() ){
              if( itc->second.existsInstMatch( qe, f, m, modEq, index+1, imtio ) ){
                return true;
              }
            }
          }
          ++eqc;
        }
      }
      //for( std::map< Node, InstMatchTrie >::iterator itc = d_data.begin(); itc != d_data.end(); ++itc ){
      //  if( itc->first!=n && qe->getEqualityQuery()->areEqual( n, itc->first ) ){
      //    if( itc->second.existsInstMatch( qe, f, m, modEq, index+1 ) ){
      //      return true;
      //    }
      //  }
      //}
    }
    return false;
  }
}

bool InstMatchTrie::addInstMatch( QuantifiersEngine* qe, Node f, InstMatch& m, bool modEq, ImtIndexOrder* imtio ){
  if( !existsInstMatch( qe, f, m, modEq, 0, imtio ) ){
    addInstMatch2( qe, f, m, 0, imtio );
    return true;
  }else{
    return false;
  }
}

InstMatchGenerator::InstMatchGenerator( Node pat, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
  initializePattern( pat, qe );
}

InstMatchGenerator::InstMatchGenerator( std::vector< Node >& pats, QuantifiersEngine* qe, int matchPolicy ) : d_matchPolicy( matchPolicy ){
  if( pats.size()==1 ){
    initializePattern( pats[0], qe );
  }else{
    initializePatterns( pats, qe );
  }
}

void InstMatchGenerator::initializePatterns( std::vector< Node >& pats, QuantifiersEngine* qe ){
  int childMatchPolicy = d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ? 0 : d_matchPolicy;
  for( int i=0; i<(int)pats.size(); i++ ){
    d_children.push_back( new InstMatchGenerator( pats[i], qe, childMatchPolicy ) );
  }
  d_pattern = Node::null();
  d_match_pattern = Node::null();
  d_cg = NULL;
}

void InstMatchGenerator::initializePattern( Node pat, QuantifiersEngine* qe ){
  Debug("inst-match-gen") << "Pattern term is " << pat << std::endl;
  Assert( pat.hasAttribute(InstConstantAttribute()) );
  d_pattern = pat;
  d_match_pattern = pat;
  if( d_match_pattern.getKind()==NOT ){
    //we want to add the children of the NOT
    d_match_pattern = d_pattern[0];
  }
  if( d_match_pattern.getKind()==IFF || d_match_pattern.getKind()==EQUAL ){
    if( !d_match_pattern[0].hasAttribute(InstConstantAttribute()) ){
      Assert( d_match_pattern[1].hasAttribute(InstConstantAttribute()) );
      //swap sides
      d_pattern = NodeManager::currentNM()->mkNode( d_match_pattern.getKind(), d_match_pattern[1], d_match_pattern[0] );
      d_pattern = pat.getKind()==NOT ? d_pattern.notNode() : d_pattern;
      if( pat.getKind()!=NOT ){   //TEMPORARY until we do better implementation of disequality matching
        d_match_pattern = d_match_pattern[1];
      }else{
        d_match_pattern = d_pattern[0][0];
      }
    }else if( !d_match_pattern[1].hasAttribute(InstConstantAttribute()) ){
      Assert( d_match_pattern[0].hasAttribute(InstConstantAttribute()) );
      if( pat.getKind()!=NOT ){   //TEMPORARY until we do better implementation of disequality matching
        d_match_pattern = d_match_pattern[0];
      }
    }
  }
  int childMatchPolicy = MATCH_GEN_DEFAULT;
  for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
    if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
      if( d_match_pattern[i].getKind()!=INST_CONSTANT ){
        d_children.push_back( new InstMatchGenerator( d_match_pattern[i], qe, childMatchPolicy ) );
        d_children_index.push_back( i );
      }
    }
  }

  Debug("inst-match-gen") << "Pattern is " << d_pattern << ", match pattern is " << d_match_pattern << std::endl;

  //create candidate generator
  if( d_match_pattern.getKind()==EQUAL || d_match_pattern.getKind()==IFF ){
    Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
    //we will be producing candidates via literal matching heuristics
    if( d_pattern.getKind()!=NOT ){
      //candidates will be all equalities
      d_cg = new inst::CandidateGeneratorQELitEq( qe, d_match_pattern );
    }else{
      //candidates will be all disequalities
      d_cg = new inst::CandidateGeneratorQELitDeq( qe, d_match_pattern );
    }
  }else if( d_pattern.getKind()==EQUAL || d_pattern.getKind()==IFF || d_pattern.getKind()==NOT ){
    Assert( d_matchPolicy==MATCH_GEN_DEFAULT );
    if( d_pattern.getKind()==NOT ){
      Unimplemented("Disequal generator unimplemented");
    }else{
      Assert( Trigger::isAtomicTrigger( d_match_pattern ) );
      //we are matching only in a particular equivalence class
      d_cg = new inst::CandidateGeneratorQE( qe, d_match_pattern.getOperator() );
      //store the equivalence class that we will call d_cg->reset( ... ) on
      d_eq_class = d_pattern[1];
    }
  }else if( Trigger::isAtomicTrigger( d_match_pattern ) ){
    //if( d_matchPolicy==MATCH_GEN_EFFICIENT_E_MATCH ){
      //Warning() << "Currently efficient e matching is not taken into account for quantifiers: " << d_pattern << std::endl;
    //}
    //we will be scanning lists trying to find d_match_pattern.getOperator()
    d_cg = new inst::CandidateGeneratorQE( qe, d_match_pattern.getOperator() );
  }else{
    d_cg = new CandidateGeneratorQueue;
    if( !Trigger::getPatternArithmetic( d_match_pattern.getAttribute(InstConstantAttribute()), d_match_pattern, d_arith_coeffs ) ){
      Debug("inst-match-gen") << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
      Warning() << "(?) Unknown matching pattern is " << d_match_pattern << std::endl;
      d_matchPolicy = MATCH_GEN_INTERNAL_ERROR;
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << d_match_pattern << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
      //we will treat this as match gen internal arithmetic
      d_matchPolicy = MATCH_GEN_INTERNAL_ARITHMETIC;
    }
  }
}

/** get match (not modulo equality) */
bool InstMatchGenerator::getMatch( Node t, InstMatch& m, QuantifiersEngine* qe ){
  Debug("matching") << "Matching " << t << " against pattern " << d_match_pattern << " ("
                    << m.size() << ")" << ", " << d_children.size() << std::endl;
  Assert( !d_match_pattern.isNull() );
  if( qe->d_optMatchIgnoreModelBasis && t.getAttribute(ModelBasisAttribute()) ){
    return true;
  }else if( d_matchPolicy==MATCH_GEN_INTERNAL_ARITHMETIC ){
    return getMatchArithmetic( t, m, qe );
  }else if( d_matchPolicy==MATCH_GEN_INTERNAL_ERROR ){
    return false;
  }else{
    EqualityQuery* q = qe->getEqualityQuery();
    //add m to partial match vector
    std::vector< InstMatch > partial;
    partial.push_back( InstMatch( &m ) );
    //if t is null
    Assert( !t.isNull() );
    Assert( !t.hasAttribute(InstConstantAttribute()) );
    Assert( t.getKind()==d_match_pattern.getKind() );
    Assert( !Trigger::isAtomicTrigger( d_match_pattern ) || t.getOperator()==d_match_pattern.getOperator() );
    //first, check if ground arguments are not equal, or a match is in conflict
    for( int i=0; i<(int)d_match_pattern.getNumChildren(); i++ ){
      if( d_match_pattern[i].hasAttribute(InstConstantAttribute()) ){
        if( d_match_pattern[i].getKind()==INST_CONSTANT ){
          if( !partial[0].setMatch( q, d_match_pattern[i], t[i] ) ){
            //match is in conflict
            Debug("matching-debug") << "Match in conflict " << t[i] << " and "
                                    << d_match_pattern[i] << " because "
                                    << partial[0].get(d_match_pattern[i])
                                    << std::endl;
            Debug("matching-fail") << "Match fail: " << partial[0].get(d_match_pattern[i]) << " and " << t[i] << std::endl;
            return false;
          }
        }
      }else{
        if( !q->areEqual( d_match_pattern[i], t[i] ) ){
          Debug("matching-fail") << "Match fail arg: " << d_match_pattern[i] << " and " << t[i] << std::endl;
          //ground arguments are not equal
          return false;
        }
      }
    }
    //now, fit children into match
    //we will be requesting candidates for matching terms for each child
    std::vector< Node > reps;
    for( int i=0; i<(int)d_children.size(); i++ ){
      Node rep = q->getRepresentative( t[ d_children_index[i] ] );
      reps.push_back( rep );
      d_children[i]->d_cg->reset( rep );
    }

    //combine child matches
    int index = 0;
    while( index>=0 && index<(int)d_children.size() ){
      partial.push_back( InstMatch( &partial[index] ) );
      if( d_children[index]->getNextMatch2( partial[index+1], qe ) ){
        index++;
      }else{
        d_children[index]->d_cg->reset( reps[index] );
        partial.pop_back();
        if( !partial.empty() ){
          partial.pop_back();
        }
        index--;
      }
    }
    if( index>=0 ){
      m = partial.back();
      return true;
    }else{
      return false;
    }
  }
}

bool InstMatchGenerator::getNextMatch2( InstMatch& m, QuantifiersEngine* qe, bool saveMatched ){
  bool success = false;
  Node t;
  do{
    //get the next candidate term t
    t = d_cg->getNextCandidate();
    //if t not null, try to fit it into match m
    if( !t.isNull() && t.getType()==d_match_pattern.getType() ){
      success = getMatch( t, m, qe );
    }
  }while( !success && !t.isNull() );
  if (saveMatched) m.d_matched = t;
  return success;
}

bool InstMatchGenerator::getMatchArithmetic( Node t, InstMatch& m, QuantifiersEngine* qe ){
  Debug("matching-arith") << "Matching " << t << " " << d_match_pattern << std::endl;
  if( !d_arith_coeffs.empty() ){
    NodeBuilder<> tb(kind::PLUS);
    Node ic = Node::null();
    for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
      Debug("matching-arith") << it->first << " -> " << it->second << std::endl;
      if( !it->first.isNull() ){
        if( m.find( it->first )==m.end() ){
          //see if we can choose this to set
          if( ic.isNull() && ( it->second.isNull() || !it->first.getType().isInteger() ) ){
            ic = it->first;
          }
        }else{
          Debug("matching-arith") << "already set " << m.get( it->first ) << std::endl;
          Node tm = m.get( it->first );
          if( !it->second.isNull() ){
            tm = NodeManager::currentNM()->mkNode( MULT, it->second, tm );
          }
          tb << tm;
        }
      }else{
        tb << it->second;
      }
    }
    if( !ic.isNull() ){
      Node tm;
      if( tb.getNumChildren()==0 ){
        tm = t;
      }else{
        tm = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
        tm = NodeManager::currentNM()->mkNode( MINUS, t, tm );
      }
      if( !d_arith_coeffs[ ic ].isNull() ){
        Assert( !ic.getType().isInteger() );
        Node coeff = NodeManager::currentNM()->mkConst( Rational(1) / d_arith_coeffs[ ic ].getConst<Rational>() );
        tm = NodeManager::currentNM()->mkNode( MULT, coeff, tm );
      }
      m.set( ic, Rewriter::rewrite( tm ));
      //set the rest to zeros
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        if( !it->first.isNull() ){
          if( m.find( it->first )==m.end() ){
            m.set( it->first, NodeManager::currentNM()->mkConst( Rational(0) ) );
          }
        }
      }
      Debug("matching-arith") << "Setting " << ic << " to " << tm << std::endl;
      return true;
    }else{
      return false;
    }
  }else{
    return false;
  }
}


/** reset instantiation round */
void InstMatchGenerator::resetInstantiationRound( QuantifiersEngine* qe ){
  if( d_match_pattern.isNull() ){
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->resetInstantiationRound( qe );
    }
  }else{
    if( d_cg ){
      d_cg->resetInstantiationRound();
    }
  }
}

void InstMatchGenerator::reset( Node eqc, QuantifiersEngine* qe ){
  if( d_match_pattern.isNull() ){
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->reset( eqc, qe );
    }
    d_partial.clear();
  }else{
    if( !d_eq_class.isNull() ){
      //we have a specific equivalence class in mind
      //we are producing matches for f(E) ~ t, where E is a non-ground vector of terms, and t is a ground term
      //just look in equivalence class of the RHS
      d_cg->reset( d_eq_class );
    }else{
      d_cg->reset( eqc );
    }
  }
}

bool InstMatchGenerator::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
  m.d_matched = Node::null();
  if( d_match_pattern.isNull() ){
    int index = (int)d_partial.size();
    while( index>=0 && index<(int)d_children.size() ){
      if( index>0 ){
        d_partial.push_back( InstMatch( &d_partial[index-1] ) );
      }else{
        d_partial.push_back( InstMatch() );
      }
      if( d_children[index]->getNextMatch( d_partial[index], qe ) ){
        index++;
      }else{
        d_children[index]->reset( Node::null(), qe );
        d_partial.pop_back();
        if( !d_partial.empty() ){
          d_partial.pop_back();
        }
        index--;
      }
    }
    if( index>=0 ){
      m = d_partial.back();
      d_partial.pop_back();
      return true;
    }else{
      return false;
    }
  }else{
    bool res = getNextMatch2( m, qe, true );
    Assert(!res || !m.d_matched.isNull());
    return res;
  }
}



// Currently the implementation doesn't take into account that
// variable should have the same value given.
// TODO use the d_children way perhaps
// TODO replace by a real dictionnary
// We should create a real substitution? slower more precise
// We don't do that often
bool InstMatchGenerator::nonunifiable( TNode t0, const std::vector<Node> & vars){
  if(d_match_pattern.isNull()) return true;

  typedef std::vector<std::pair<TNode,TNode> > tstack;
  tstack stack(1,std::make_pair(t0,d_match_pattern)); // t * pat

  while(!stack.empty()){
    const std::pair<TNode,TNode> p = stack.back(); stack.pop_back();
    const TNode & t = p.first;
    const TNode & pat = p.second;

    // t or pat is a variable currently we consider that can match anything
    if( find(vars.begin(),vars.end(),t) != vars.end() ) continue;
    if( pat.getKind() == INST_CONSTANT ) continue;

    // t and pat are nonunifiable
    if( !Trigger::isAtomicTrigger( t ) || !Trigger::isAtomicTrigger( pat ) ) {
      if(t == pat) continue;
      else return true;
    };
    if( t.getOperator() != pat.getOperator() ) return true;

    //put the children on the stack
    for( size_t i=0; i < pat.getNumChildren(); i++ ){
      stack.push_back(std::make_pair(t[i],pat[i]));
    };
  }
  // The heuristic can't find non-unifiability
  return false;
}

int InstMatchGenerator::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  //now, try to add instantiation for each match produced
  int addedLemmas = 0;
  InstMatch m;
  while( getNextMatch( m, qe ) ){
    //m.makeInternal( d_quantEngine->getEqualityQuery() );
    m.add( baseMatch );
    if( qe->addInstantiation( f, m ) ){
      addedLemmas++;
      if( qe->d_optInstLimitActive && qe->d_optInstLimit<=0 ){
        return addedLemmas;
      }
    }
    m.clear();
  }
  //return number of lemmas added
  return addedLemmas;
}

int InstMatchGenerator::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  if( !d_match_pattern.isNull() ){
    InstMatch m;
    if( getMatch( t, m, qe ) ){
      if( qe->addInstantiation( f, m ) ){
        return 1;
      }
    }
  }else{
    for( int i=0; i<(int)d_children.size(); i++ ){
      d_children[i]->addTerm( f, t, qe );
    }
  }
  return 0;
}

/** constructors */
InstMatchGeneratorMulti::InstMatchGeneratorMulti( Node f, std::vector< Node >& pats, QuantifiersEngine* qe, int matchOption ) :
d_f( f ){
  Debug("smart-multi-trigger") << "Making smart multi-trigger for " << f << std::endl;
  std::map< Node, std::vector< Node > > var_contains;
  Trigger::getVarContains( f, pats, var_contains );
  //convert to indicies
  for( std::map< Node, std::vector< Node > >::iterator it = var_contains.begin(); it != var_contains.end(); ++it ){
    Debug("smart-multi-trigger") << "Pattern " << it->first << " contains: ";
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug("smart-multi-trigger") << it->second[i] << " ";
      int index = it->second[i].getAttribute(InstVarNumAttribute());
      d_var_contains[ it->first ].push_back( index );
      d_var_to_node[ index ].push_back( it->first );
    }
    Debug("smart-multi-trigger") << std::endl;
  }
  for( int i=0; i<(int)pats.size(); i++ ){
    Node n = pats[i];
    //make the match generator
    d_children.push_back( new InstMatchGenerator( n, qe, matchOption ) );
    //compute unique/shared variables
    std::vector< int > unique_vars;
    std::map< int, bool > shared_vars;
    int numSharedVars = 0;
    for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
      if( d_var_to_node[ d_var_contains[n][j] ].size()==1 ){
        Debug("smart-multi-trigger") << "Var " << d_var_contains[n][j] << " is unique to " << pats[i] << std::endl;
        unique_vars.push_back( d_var_contains[n][j] );
      }else{
        shared_vars[ d_var_contains[n][j] ] = true;
        numSharedVars++;
      }
    }
    //we use the latest shared variables, then unique variables
    std::vector< int > vars;
    int index = i==0 ? (int)(pats.size()-1) : (i-1);
    while( numSharedVars>0 && index!=i ){
      for( std::map< int, bool >::iterator it = shared_vars.begin(); it != shared_vars.end(); ++it ){
        if( it->second ){
          if( std::find( d_var_contains[ pats[index] ].begin(), d_var_contains[ pats[index] ].end(), it->first )!=
              d_var_contains[ pats[index] ].end() ){
            vars.push_back( it->first );
            shared_vars[ it->first ] = false;
            numSharedVars--;
          }
        }
      }
      index = index==0 ? (int)(pats.size()-1) : (index-1);
    }
    vars.insert( vars.end(), unique_vars.begin(), unique_vars.end() );
    Debug("smart-multi-trigger") << "   Index[" << i << "]: ";
    for( int i=0; i<(int)vars.size(); i++ ){
      Debug("smart-multi-trigger") << vars[i] << " ";
    }
    Debug("smart-multi-trigger") << std::endl;
    //make ordered inst match trie
    InstMatchTrie::ImtIndexOrder* imtio = new InstMatchTrie::ImtIndexOrder;
    imtio->d_order.insert( imtio->d_order.begin(), vars.begin(), vars.end() );
    d_children_trie.push_back( InstMatchTrieOrdered( imtio ) );
  }

}

/** reset instantiation round (call this whenever equivalence classes have changed) */
void InstMatchGeneratorMulti::resetInstantiationRound( QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->resetInstantiationRound( qe );
  }
}

/** reset, eqc is the equivalence class to search in (any if eqc=null) */
void InstMatchGeneratorMulti::reset( Node eqc, QuantifiersEngine* qe ){
  for( int i=0; i<(int)d_children.size(); i++ ){
    d_children[i]->reset( eqc, qe );
  }
}

int InstMatchGeneratorMulti::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  int addedLemmas = 0;
  Debug("smart-multi-trigger") << "Process smart multi trigger" << std::endl;
  for( int i=0; i<(int)d_children.size(); i++ ){
    Debug("smart-multi-trigger") << "Calculate matches " << i << std::endl;
    std::vector< InstMatch > newMatches;
    InstMatch m;
    while( d_children[i]->getNextMatch( m, qe ) ){
      m.makeRepresentative( qe );
      newMatches.push_back( InstMatch( &m ) );
      m.clear();
    }
    for( int j=0; j<(int)newMatches.size(); j++ ){
      processNewMatch( qe, newMatches[j], i, addedLemmas );
    }
  }
  return addedLemmas;
}

void InstMatchGeneratorMulti::processNewMatch( QuantifiersEngine* qe, InstMatch& m, int fromChildIndex, int& addedLemmas ){
  //see if these produce new matches
  d_children_trie[fromChildIndex].addInstMatch( qe, d_f, m, true );
  //possibly only do the following if we know that new matches will be produced?
  //the issue is that instantiations are filtered in quantifiers engine, and so there is no guarentee that
  // we can safely skip the following lines, even when we have already produced this match.
  Debug("smart-multi-trigger") << "Child " << fromChildIndex << " produced match " << m << std::endl;
  //process new instantiations
  int childIndex = (fromChildIndex+1)%(int)d_children.size();
  std::vector< IndexedTrie > unique_var_tries;
  processNewInstantiations( qe, m, addedLemmas, d_children_trie[childIndex].getTrie(),
                            unique_var_tries, 0, childIndex, fromChildIndex, true );
}

void InstMatchGeneratorMulti::processNewInstantiations( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
                                                        std::vector< IndexedTrie >& unique_var_tries,
                                                        int trieIndex, int childIndex, int endChildIndex, bool modEq ){
  if( childIndex==endChildIndex ){
    //now, process unique variables
    processNewInstantiations2( qe, m, addedLemmas, unique_var_tries, 0 );
  }else if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
    int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
    Node curr_ic = qe->getTermDatabase()->getInstantiationConstant( d_f, curr_index );
    if( m.find( curr_ic )==m.end() ){
      //if( d_var_to_node[ curr_index ].size()==1 ){    //FIXME
      //  //unique variable(s), defer calculation
      //  unique_var_tries.push_back( IndexedTrie( std::pair< int, int >( childIndex, trieIndex ), tr ) );
      //  int newChildIndex = (childIndex+1)%(int)d_children.size();
      //  processNewInstantiations( qe, m, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
      //                            0, newChildIndex, endChildIndex, modEq );
      //}else{
        //shared and non-set variable, add to InstMatch
        for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
          InstMatch mn( &m );
          mn.set( curr_ic, it->first);
          processNewInstantiations( qe, mn, addedLemmas, &(it->second), unique_var_tries,
                                    trieIndex+1, childIndex, endChildIndex, modEq );
        }
      //}
    }else{
      //shared and set variable, try to merge
      Node n = m.get( curr_ic );
      std::map< Node, InstMatchTrie >::iterator it = tr->d_data.find( n );
      if( it!=tr->d_data.end() ){
        processNewInstantiations( qe, m, addedLemmas, &(it->second), unique_var_tries,
                                  trieIndex+1, childIndex, endChildIndex, modEq );
      }
      if( modEq ){
        //check modulo equality for other possible instantiations
        if( qe->getEqualityQuery()->getEngine()->hasTerm( n ) ){
          eq::EqClassIterator eqc( qe->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                   qe->getEqualityQuery()->getEngine() );
          while( !eqc.isFinished() ){
            Node en = (*eqc);
            if( en!=n ){
              std::map< Node, InstMatchTrie >::iterator itc = tr->d_data.find( en );
              if( itc!=tr->d_data.end() ){
                processNewInstantiations( qe, m, addedLemmas, &(itc->second), unique_var_tries,
                                          trieIndex+1, childIndex, endChildIndex, modEq );
              }
            }
            ++eqc;
          }
        }
      }
    }
  }else{
    int newChildIndex = (childIndex+1)%(int)d_children.size();
    processNewInstantiations( qe, m, addedLemmas, d_children_trie[newChildIndex].getTrie(), unique_var_tries,
                              0, newChildIndex, endChildIndex, modEq );
  }
}

void InstMatchGeneratorMulti::processNewInstantiations2( QuantifiersEngine* qe, InstMatch& m, int& addedLemmas,
                                                         std::vector< IndexedTrie >& unique_var_tries,
                                                         int uvtIndex, InstMatchTrie* tr, int trieIndex ){
  if( uvtIndex<(int)unique_var_tries.size() ){
    int childIndex = unique_var_tries[uvtIndex].first.first;
    if( !tr ){
      tr = unique_var_tries[uvtIndex].second;
      trieIndex = unique_var_tries[uvtIndex].first.second;
    }
    if( trieIndex<(int)d_children_trie[childIndex].getOrdering()->d_order.size() ){
      int curr_index = d_children_trie[childIndex].getOrdering()->d_order[trieIndex];
      Node curr_ic = qe->getTermDatabase()->getInstantiationConstant( d_f, curr_index );
      //unique non-set variable, add to InstMatch
      for( std::map< Node, InstMatchTrie >::iterator it = tr->d_data.begin(); it != tr->d_data.end(); ++it ){
        InstMatch mn( &m );
        mn.set( curr_ic, it->first);
        processNewInstantiations2( qe, mn, addedLemmas, unique_var_tries, uvtIndex, &(it->second), trieIndex+1 );
      }
    }else{
      processNewInstantiations2( qe, m, addedLemmas, unique_var_tries, uvtIndex+1 );
    }
  }else{
    //m is an instantiation
    if( qe->addInstantiation( d_f, m ) ){
      addedLemmas++;
      Debug("smart-multi-trigger") << "-> Produced instantiation " << m << std::endl;
    }
  }
}

int InstMatchGeneratorMulti::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  int addedLemmas = 0;
  for( int i=0; i<(int)d_children.size(); i++ ){
    if( ((InstMatchGenerator*)d_children[i])->d_match_pattern.getOperator()==t.getOperator() ){
      InstMatch m;
      //if it produces a match, then process it with the rest
      if( ((InstMatchGenerator*)d_children[i])->getMatch( t, m, qe ) ){
        processNewMatch( qe, m, i, addedLemmas );
      }
    }
  }
  return addedLemmas;
}

int InstMatchGeneratorSimple::addInstantiations( Node f, InstMatch& baseMatch, QuantifiersEngine* qe ){
  InstMatch m;
  m.add( baseMatch );
  int addedLemmas = 0;
  if( d_match_pattern.getType()==NodeManager::currentNM()->booleanType() ){
    for( int i=0; i<2; i++ ){
      addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_pred_map_trie[i][ d_match_pattern.getOperator() ]) );
    }
  }else{
    addInstantiations( m, qe, addedLemmas, 0, &(qe->getTermDatabase()->d_func_map_trie[ d_match_pattern.getOperator() ]) );
  }
  return addedLemmas;
}

void InstMatchGeneratorSimple::addInstantiations( InstMatch& m, QuantifiersEngine* qe, int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat ){
  if( argIndex==(int)d_match_pattern.getNumChildren() ){
    //m is an instantiation
    if( qe->addInstantiation( d_f, m ) ){
      addedLemmas++;
      Debug("simple-multi-trigger") << "-> Produced instantiation " << m << std::endl;
    }
  }else{
    if( d_match_pattern[argIndex].getKind()==INST_CONSTANT ){
      Node ic = d_match_pattern[argIndex];
      for( std::map< Node, quantifiers::TermArgTrie >::iterator it = tat->d_data.begin(); it != tat->d_data.end(); ++it ){
        Node t = it->first;
        if( m.get( ic ).isNull() || m.get( ic )==t ){
          Node prev = m.get( ic );
          m.set( ic, t);
          addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second) );
          m.set( ic, prev);
        }
      }
    }else{
      Node r = qe->getEqualityQuery()->getRepresentative( d_match_pattern[argIndex] );
      std::map< Node, quantifiers::TermArgTrie >::iterator it = tat->d_data.find( r );
      if( it!=tat->d_data.end() ){
        addInstantiations( m, qe, addedLemmas, argIndex+1, &(it->second) );
      }
    }
  }
}

int InstMatchGeneratorSimple::addTerm( Node f, Node t, QuantifiersEngine* qe ){
  Assert( options::eagerInstQuant() );
  InstMatch m;
  for( int i=0; i<(int)t.getNumChildren(); i++ ){
    if( d_match_pattern[i].getKind()==INST_CONSTANT ){
      m.set(d_match_pattern[i], t[i]);
    }else if( !qe->getEqualityQuery()->areEqual( d_match_pattern[i], t[i] ) ){
      return 0;
    }
  }
  return qe->addInstantiation( f, m ) ? 1 : 0;
}
