/*********************                                                        */
/*! \file term_database.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of term databse class
 **/

#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/options.h"
#include "theory/rewriterules/efficient_e_matching.h"
#include "theory/quantifiers/theory_quantifiers.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

using namespace CVC4::theory::inst;

bool TermArgTrie::addTerm2( QuantifiersEngine* qe, Node n, int argIndex ){
  if( argIndex<(int)n.getNumChildren() ){
    Node r = qe->getEqualityQuery()->getRepresentative( n[ argIndex ] );
    std::map< Node, TermArgTrie >::iterator it = d_data.find( r );
    if( it==d_data.end() ){
      d_data[r].addTerm2( qe, n, argIndex+1 );
      return true;
    }else{
      return it->second.addTerm2( qe, n, argIndex+1 );
    }
  }else{
    //store n in d_data (this should be interpretted as the "data" and not as a reference to a child)
    d_data[n].d_data.clear();
    return false;
  }
}

void TermDb::addTermEfficient( Node n, std::set< Node >& added){
  static AvailableInTermDb aitdi;
  if (inst::Trigger::isAtomicTrigger( n ) && !n.getAttribute(aitdi)){
    //Already processed but new in this branch
    n.setAttribute(aitdi,true);
    added.insert( n );
    for( size_t i=0; i< n.getNumChildren(); i++ ){
      addTermEfficient(n[i],added);
    }
  }

}


Node TermDb::getOperator( Node n ) {
  //return n.getOperator();

  if( n.getKind()==SELECT || n.getKind()==STORE ){
    //since it is parametric, use a particular one as op
    TypeNode tn1 = n[0].getType();
    TypeNode tn2 = n[1].getType();
    Node op = n.getOperator();
    std::map< Node, std::map< TypeNode, std::map< TypeNode, Node > > >::iterator ito = d_par_op_map.find( op );
    if( ito!=d_par_op_map.end() ){
      std::map< TypeNode, std::map< TypeNode, Node > >::iterator it = ito->second.find( tn1 );
      if( it!=ito->second.end() ){
        std::map< TypeNode, Node >::iterator it2 = it->second.find( tn2 );
        if( it2!=it->second.end() ){
          return it2->second;
        }
      }
    }
    d_par_op_map[op][tn1][tn2] = n;
    return n;
  }else if( n.getKind()==APPLY_UF ){
    return n.getOperator();
  }else{
    return Node::null();
  }
}

void TermDb::addTerm( Node n, std::set< Node >& added, bool withinQuant ){
  //don't add terms in quantifier bodies
  if( withinQuant && !options::registerQuantBodyTerms() ){
    return;
  }
  if( d_processed.find( n )==d_processed.end() ){
    ++(d_quantEngine->d_statistics.d_term_in_termdb);
    d_processed.insert(n);
    d_type_map[ n.getType() ].push_back( n );
    n.setAttribute(AvailableInTermDb(),true);
    //if this is an atomic trigger, consider adding it
    //Call the children?
    if( inst::Trigger::isAtomicTrigger( n ) ){
      if( !TermDb::hasInstConstAttr(n) ){
        Trace("term-db") << "register term in db " << n << std::endl;
        //std::cout << "register trigger term " << n << std::endl;
        Node op = getOperator( n );
        d_op_map[op].push_back( n );
        added.insert( n );

        for( size_t i=0; i<n.getNumChildren(); i++ ){
          addTerm( n[i], added, withinQuant );
          if( options::efficientEMatching() ){
            EfficientEMatcher* eem = d_quantEngine->getEfficientEMatcher();
            if( d_parents[n[i]][op].empty() ){
              //must add parent to equivalence class info
              Node nir = d_quantEngine->getEqualityQuery()->getRepresentative( n[i] );
              EqClassInfo* eci_nir = eem->getEquivalenceClassInfo( nir );
              if( eci_nir ){
                eci_nir->d_pfuns[ op ] = true;
              }
            }
            //add to parent structure
            if( std::find( d_parents[n[i]][op][i].begin(), d_parents[n[i]][op][i].end(), n )==d_parents[n[i]][op][i].end() ){
              d_parents[n[i]][op][i].push_back( n );
              Assert(!getParents(n[i],op,i).empty());
            }
          }
          if( options::eagerInstQuant() ){
            if( !n.hasAttribute(InstLevelAttribute()) && n.getAttribute(InstLevelAttribute())==0 ){
              int addedLemmas = 0;
              for( size_t i=0; i<d_op_triggers[op].size(); i++ ){
                addedLemmas += d_op_triggers[op][i]->addTerm( n );
              }
              //Message() << "Terms, added lemmas: " << addedLemmas << std::endl;
              d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
            }
          }
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        addTerm( n[i], added, withinQuant );
      }
    }
  }else{
    if( options::efficientEMatching() && !TermDb::hasInstConstAttr(n)){
      //Efficient e-matching must be notified
      //The term in triggers are not important here
      Debug("term-db") << "New in this branch term " << n << std::endl;
      addTermEfficient(n,added);
    }
  }
}

 void TermDb::reset( Theory::Effort effort ){
   int nonCongruentCount = 0;
   int congruentCount = 0;
   int alreadyCongruentCount = 0;
   //rebuild d_func/pred_map_trie for each operation, this will calculate all congruent terms
   for( std::map< Node, std::vector< Node > >::iterator it = d_op_map.begin(); it != d_op_map.end(); ++it ){
     d_op_count[ it->first ] = 0;
     if( !it->second.empty() ){
       if( it->second[0].getType().isBoolean() ){
         d_pred_map_trie[ 0 ][ it->first ].d_data.clear();
         d_pred_map_trie[ 1 ][ it->first ].d_data.clear();
       }else{
         d_func_map_trie[ it->first ].d_data.clear();
         for( int i=0; i<(int)it->second.size(); i++ ){
           Node n = it->second[i];
           computeModelBasisArgAttribute( n );
           if( !n.getAttribute(NoMatchAttribute()) ){
             if( !d_func_map_trie[ it->first ].addTerm( d_quantEngine, n ) ){
               NoMatchAttribute nma;
               n.setAttribute(nma,true);
               Debug("term-db-cong") << n << " is redundant." << std::endl;
               congruentCount++;
             }else{
               nonCongruentCount++;
               d_op_count[ it->first ]++;
             }
           }else{
             congruentCount++;
             alreadyCongruentCount++;
           }
         }
       }
     }
   }
   for( int i=0; i<2; i++ ){
     Node n = NodeManager::currentNM()->mkConst( i==1 );
     if( d_quantEngine->getEqualityQuery()->getEngine()->hasTerm( n ) ){
       eq::EqClassIterator eqc( d_quantEngine->getEqualityQuery()->getEngine()->getRepresentative( n ),
                                d_quantEngine->getEqualityQuery()->getEngine() );
       while( !eqc.isFinished() ){
         Node en = (*eqc);
         computeModelBasisArgAttribute( en );
         if( en.getKind()==APPLY_UF && !TermDb::hasInstConstAttr(en) ){
           if( !en.getAttribute(NoMatchAttribute()) ){
             Node op = getOperator( en );
             if( !d_pred_map_trie[i][op].addTerm( d_quantEngine, en ) ){
               NoMatchAttribute nma;
               en.setAttribute(nma,true);
               Debug("term-db-cong") << en << " is redundant." << std::endl;
               congruentCount++;
             }else{
               nonCongruentCount++;
               d_op_count[ op ]++;
             }
           }else{
             alreadyCongruentCount++;
           }
         }
         ++eqc;
       }
     }
   }
   Debug("term-db-cong") << "TermDb: Reset" << std::endl;
   Debug("term-db-cong") << "Congruent/Non-Congruent = ";
   Debug("term-db-cong") << congruentCount << "(" << alreadyCongruentCount << ") / " << nonCongruentCount << std::endl;
}

Node TermDb::getModelBasisTerm( TypeNode tn, int i ){
  if( d_model_basis_term.find( tn )==d_model_basis_term.end() ){
    Node mbt;
    if( tn.isInteger() || tn.isReal() ){
      mbt = NodeManager::currentNM()->mkConst( Rational( 0 ) );
    }else if( !tn.isSort() ){
      mbt = tn.mkGroundTerm();
    }else{
      if( options::fmfFreshDistConst() || d_type_map[ tn ].empty() ){
        std::stringstream ss;
        ss << Expr::setlanguage(options::outputLanguage());
        ss << "e_" << tn;
        mbt = NodeManager::currentNM()->mkSkolem( ss.str(), tn, "is a model basis term" );
        Trace("mkVar") << "ModelBasis:: Make variable " << mbt << " : " << tn << std::endl;
      }else{
        mbt = d_type_map[ tn ][ 0 ];
      }
    }
    ModelBasisAttribute mba;
    mbt.setAttribute(mba,true);
    d_model_basis_term[tn] = mbt;
    Trace("model-basis-term") << "Choose " << mbt << " as model basis term for " << tn << std::endl;
  }
  return d_model_basis_term[tn];
}

Node TermDb::getModelBasisOpTerm( Node op ){
  if( d_model_basis_op_term.find( op )==d_model_basis_op_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( int i=0; i<(int)(t.getNumChildren()-1); i++ ){
      children.push_back( getModelBasisTerm( t[i] ) );
    }
    if( children.size()==1 ){
      d_model_basis_op_term[op] = op;
    }else{
      d_model_basis_op_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
    }
  }
  return d_model_basis_op_term[op];
}

Node TermDb::getModelBasis( Node f, Node n ){
  //make model basis
  if( d_model_basis_terms.find( f )==d_model_basis_terms.end() ){
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      d_model_basis_terms[f].push_back( getModelBasisTerm( f[0][j].getType() ) );
    }
  }
  Node gn = n.substitute( d_inst_constants[f].begin(), d_inst_constants[f].end(),
                          d_model_basis_terms[f].begin(), d_model_basis_terms[f].end() );
  return gn;
}

Node TermDb::getModelBasisBody( Node f ){
  if( d_model_basis_body.find( f )==d_model_basis_body.end() ){
    Node n = getInstConstantBody( f );
    d_model_basis_body[f] = getModelBasis( f, n );
  }
  return d_model_basis_body[f];
}

void TermDb::computeModelBasisArgAttribute( Node n ){
  if( !n.hasAttribute(ModelBasisArgAttribute()) ){
    //ensure that the model basis terms have been defined
    if( n.getKind()==APPLY_UF ){
      getModelBasisOpTerm( n.getOperator() );
    }
    uint64_t val = 0;
    //determine if it has model basis attribute
    for( int j=0; j<(int)n.getNumChildren(); j++ ){
      if( n[j].getAttribute(ModelBasisAttribute()) ){
        val++;
      }
    }
    ModelBasisArgAttribute mbaa;
    n.setAttribute( mbaa, val );
  }
}

void TermDb::makeInstantiationConstantsFor( Node f ){
  if( d_inst_constants.find( f )==d_inst_constants.end() ){
    Debug("quantifiers-engine") << "Instantiation constants for " << f << " : " << std::endl;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      d_vars[f].push_back( f[0][i] );
      //make instantiation constants
      Node ic = NodeManager::currentNM()->mkInstConstant( f[0][i].getType() );
      d_inst_constants_map[ic] = f;
      d_inst_constants[ f ].push_back( ic );
      Debug("quantifiers-engine") << "  " << ic << std::endl;
      //set the var number attribute
      InstVarNumAttribute ivna;
      ic.setAttribute(ivna,i);
      InstConstantAttribute ica;
      ic.setAttribute(ica,f);
      //also set the no-match attribute
      NoMatchAttribute nma;
      ic.setAttribute(nma,true);
    }
  }
}


Node TermDb::getInstConstAttr( Node n ) {
  if (!n.hasAttribute(InstConstantAttribute()) ){
    Node f;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      f = getInstConstAttr(n[i]);
      if( !f.isNull() ){
        break;
      }
    }
    InstConstantAttribute ica;
    n.setAttribute(ica,f);
    if( !f.isNull() ){
      //also set the no-match attribute
      NoMatchAttribute nma;
      n.setAttribute(nma,true);
    }
  }
  return n.getAttribute(InstConstantAttribute());
}

bool TermDb::hasInstConstAttr( Node n ) {
  return !getInstConstAttr(n).isNull();
}

bool TermDb::hasBoundVarAttr( Node n ) {
  if( !n.getAttribute(HasBoundVarComputedAttribute()) ){
    bool hasBv = false;
    if( n.getKind()==BOUND_VARIABLE ){
      hasBv = true;
    }else{
      for (unsigned i=0; i<n.getNumChildren(); i++) {
        if( hasBoundVarAttr(n[i]) ){
          hasBv = true;
          break;
        }
      }
    }
    HasBoundVarAttribute hbva;
    n.setAttribute(hbva, hasBv);
    HasBoundVarComputedAttribute hbvca;
    n.setAttribute(hbvca, true);
    Trace("bva") << n << " has bva : " << n.getAttribute(HasBoundVarAttribute()) << std::endl;
  }
  return n.getAttribute(HasBoundVarAttribute());
}

void TermDb::getBoundVars( Node n, std::vector< Node >& bvs) {
  if (n.getKind()==BOUND_VARIABLE ){
    if ( std::find( bvs.begin(), bvs.end(), n)==bvs.end() ){
      bvs.push_back( n );
    }
  }else{
    for( unsigned i=0; i<n.getNumChildren(); i++) {
      getBoundVars(n[i], bvs);
    }
  }
}


/** get the i^th instantiation constant of f */
Node TermDb::getInstantiationConstant( Node f, int i ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( f );
  if( it!=d_inst_constants.end() ){
    return it->second[i];
  }else{
    return Node::null();
  }
}

/** get number of instantiation constants for f */
int TermDb::getNumInstantiationConstants( Node f ) const {
  std::map< Node, std::vector< Node > >::const_iterator it = d_inst_constants.find( f );
  if( it!=d_inst_constants.end() ){
    return (int)it->second.size();
  }else{
    return 0;
  }
}

Node TermDb::getInstConstantBody( Node f ){
  std::map< Node, Node >::iterator it = d_inst_const_body.find( f );
  if( it==d_inst_const_body.end() ){
    makeInstantiationConstantsFor( f );
    Node n = getInstConstantNode( f[1], f );
    d_inst_const_body[ f ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermDb::getCounterexampleLiteral( Node f ){
  if( d_ce_lit.find( f )==d_ce_lit.end() ){
    Node ceBody = getInstConstantBody( f );
    //check if any variable are of bad types, and fail if so
    for( size_t i=0; i<d_inst_constants[f].size(); i++ ){
      if( d_inst_constants[f][i].getType().isBoolean() ){
        d_ce_lit[ f ] = Node::null();
        return Node::null();
      }
    }
    //otherwise, ensure literal
    Node ceLit = d_quantEngine->getValuation().ensureLiteral( ceBody.notNode() );
    d_ce_lit[ f ] = ceLit;
  }
  return d_ce_lit[ f ];
}

Node TermDb::getInstConstantNode( Node n, Node f ){
  return convertNodeToPattern(n,f,d_vars[f],d_inst_constants[ f ]);
}

Node TermDb::convertNodeToPattern( Node n, Node f, const std::vector<Node> & vars,
                                              const std::vector<Node> & inst_constants){
  Node n2 = n.substitute( vars.begin(), vars.end(),
                          inst_constants.begin(),
                          inst_constants.end() );
  return n2;
}



Node TermDb::getSkolemizedBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_skolem_body.find( f )==d_skolem_body.end() ){
    std::vector< Node > vars;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      Node skv = NodeManager::currentNM()->mkSkolem( "skv_$$", f[0][i].getType(), "is a termdb-created skolemized body" );
      d_skolem_constants[ f ].push_back( skv );
      vars.push_back( f[0][i] );
      //carry information for sort inference
      if( options::sortInference() ){
        d_quantEngine->getTheoryEngine()->getSortInference()->setSkolemVar( f, f[0][i], skv );
      }
    }
    d_skolem_body[ f ] = f[ 1 ].substitute( vars.begin(), vars.end(),
                                            d_skolem_constants[ f ].begin(), d_skolem_constants[ f ].end() );
  }
  return d_skolem_body[ f ];
}

Node TermDb::getFreeVariableForInstConstant( Node n ){
  TypeNode tn = n.getType();
  if( d_free_vars.find( tn )==d_free_vars.end() ){
	for( unsigned i=0; i<d_type_map[ tn ].size(); i++ ){
	  if( !quantifiers::TermDb::hasInstConstAttr(d_type_map[ tn ][ i ]) ){
	    d_free_vars[tn] = d_type_map[ tn ][ i ];
	  }
	}
	if( d_free_vars.find( tn )==d_free_vars.end() ){
      //if integer or real, make zero
      if( tn.isInteger() || tn.isReal() ){
        Rational z(0);
        d_free_vars[tn] = NodeManager::currentNM()->mkConst( z );
      }else{
	    d_free_vars[tn] = NodeManager::currentNM()->mkSkolem( "freevar_$$", tn, "is a free variable created by termdb" );
	    Trace("mkVar") << "FreeVar:: Make variable " << d_free_vars[tn] << " : " << tn << std::endl;
      }
    }
  }
  return d_free_vars[tn];
}

const std::vector<Node> & TermDb::getParents(TNode n, TNode f, int arg){
  std::hash_map< Node, std::hash_map< Node, std::hash_map< int, std::vector< Node > >,NodeHashFunction  >,NodeHashFunction  >::const_iterator
    rn = d_parents.find( n );
  if( rn !=d_parents.end() ){
    std::hash_map< Node, std::hash_map< int, std::vector< Node > > , NodeHashFunction  > ::const_iterator
      rf = rn->second.find(f);
    if( rf != rn->second.end() ){
      std::hash_map< int, std::vector< Node > > ::const_iterator
        ra = rf->second.find(arg);
      if( ra != rf->second.end() ){
        return ra->second;
      }
    }
  }
  static std::vector<Node> empty;
  return empty;
}

void TermDb::computeVarContains( Node n ) {
  if( d_var_contains.find( n )==d_var_contains.end() ){
    d_var_contains[n].clear();
    computeVarContains2( n, n );
  }
}

void TermDb::computeVarContains2( Node n, Node parent ){
  if( n.getKind()==INST_CONSTANT ){
    if( std::find( d_var_contains[parent].begin(), d_var_contains[parent].end(), n )==d_var_contains[parent].end() ){
      d_var_contains[parent].push_back( n );
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeVarContains2( n[i], parent );
    }
  }
}

bool TermDb::isVariableSubsume( Node n1, Node n2 ){
  if( n1==n2 ){
    return true;
  }else{
    //Notice() << "is variable subsume ? " << n1 << " " << n2 << std::endl;
    computeVarContains( n1 );
    computeVarContains( n2 );
    for( int i=0; i<(int)d_var_contains[n2].size(); i++ ){
      if( std::find( d_var_contains[n1].begin(), d_var_contains[n1].end(), d_var_contains[n2][i] )==d_var_contains[n1].end() ){
        //Notice() << "no" << std::endl;
        return false;
      }
    }
    //Notice() << "yes" << std::endl;
    return true;
  }
}

void TermDb::getVarContains( Node f, std::vector< Node >& pats, std::map< Node, std::vector< Node > >& varContains ){
  for( int i=0; i<(int)pats.size(); i++ ){
    computeVarContains( pats[i] );
    varContains[ pats[i] ].clear();
    for( int j=0; j<(int)d_var_contains[pats[i]].size(); j++ ){
      if( d_var_contains[pats[i]][j].getAttribute(InstConstantAttribute())==f ){
        varContains[ pats[i] ].push_back( d_var_contains[pats[i]][j] );
      }
    }
  }
}

void TermDb::getVarContainsNode( Node f, Node n, std::vector< Node >& varContains ){
  computeVarContains( n );
  for( int j=0; j<(int)d_var_contains[n].size(); j++ ){
    if( d_var_contains[n][j].getAttribute(InstConstantAttribute())==f ){
      varContains.push_back( d_var_contains[n][j] );
    }
  }
}

/** is n1 an instance of n2 or vice versa? */
int TermDb::isInstanceOf( Node n1, Node n2 ){
  if( n1==n2 ){
    return 1;
  }else if( n1.getKind()==n2.getKind() ){
    if( n1.getKind()==APPLY_UF ){
      if( n1.getOperator()==n2.getOperator() ){
        int result = 0;
        for( int i=0; i<(int)n1.getNumChildren(); i++ ){
          if( n1[i]!=n2[i] ){
            int cResult = isInstanceOf( n1[i], n2[i] );
            if( cResult==0 ){
              return 0;
            }else if( cResult!=result ){
              if( result!=0 ){
                return 0;
              }else{
                result = cResult;
              }
            }
          }
        }
        return result;
      }
    }
    return 0;
  }else if( n2.getKind()==INST_CONSTANT ){
    computeVarContains( n1 );
    //if( std::find( d_var_contains[ n1 ].begin(), d_var_contains[ n1 ].end(), n2 )!=d_var_contains[ n1 ].end() ){
    //  return 1;
    //}
    if( d_var_contains[ n1 ].size()==1 && d_var_contains[ n1 ][ 0 ]==n2 ){
      return 1;
    }
  }else if( n1.getKind()==INST_CONSTANT ){
    computeVarContains( n2 );
    //if( std::find( d_var_contains[ n2 ].begin(), d_var_contains[ n2 ].end(), n1 )!=d_var_contains[ n2 ].end() ){
    //  return -1;
    //}
    if( d_var_contains[ n2 ].size()==1 && d_var_contains[ n2 ][ 0 ]==n1 ){
      return 1;
    }
  }
  return 0;
}

bool TermDb::isUnifiableInstanceOf( Node n1, Node n2, std::map< Node, Node >& subs ){
  if( n1==n2 ){
    return true;
  }else if( n2.getKind()==INST_CONSTANT ){
    //if( !node_contains( n1, n2 ) ){
    //  return false;
    //}
    if( subs.find( n2 )==subs.end() ){
      subs[n2] = n1;
    }else if( subs[n2]!=n1 ){
      return false;
    }
    return true;
  }else if( n1.getKind()==n2.getKind() && n1.getMetaKind()==kind::metakind::PARAMETERIZED ){
    if( n1.getOperator()!=n2.getOperator() ){
      return false;
    }
    for( int i=0; i<(int)n1.getNumChildren(); i++ ){
      if( !isUnifiableInstanceOf( n1[i], n2[i], subs ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void TermDb::filterInstances( std::vector< Node >& nodes ){
  std::vector< bool > active;
  active.resize( nodes.size(), true );
  for( int i=0; i<(int)nodes.size(); i++ ){
    for( int j=i+1; j<(int)nodes.size(); j++ ){
      if( active[i] && active[j] ){
        int result = isInstanceOf( nodes[i], nodes[j] );
        if( result==1 ){
          Trace("filter-instances") << nodes[j] << " is an instance of " << nodes[i] << std::endl;
          active[j] = false;
        }else if( result==-1 ){
          Trace("filter-instances") << nodes[i] << " is an instance of " << nodes[j] << std::endl;
          active[i] = false;
        }
      }
    }
  }
  std::vector< Node > temp;
  for( int i=0; i<(int)nodes.size(); i++ ){
    if( active[i] ){
      temp.push_back( nodes[i] );
    }
  }
  nodes.clear();
  nodes.insert( nodes.begin(), temp.begin(), temp.end() );
}

void TermDb::registerTrigger( theory::inst::Trigger* tr, Node op ){
  if( std::find( d_op_triggers[op].begin(), d_op_triggers[op].end(), tr )==d_op_triggers[op].end() ){
    d_op_triggers[op].push_back( tr );
  }
}
