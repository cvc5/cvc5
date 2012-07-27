/*********************                                                        */
/*! \file term_database.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): bobot
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of term databse class
 **/

 #include "theory/quantifiers/term_database.h"
 #include "theory/quantifiers_engine.h"
 #include "theory/uf/theory_uf_instantiator.h"
 #include "theory/theory_engine.h"
 #include "theory/quantifiers/first_order_model.h"

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
  if (Trigger::isAtomicTrigger( n ) && !n.getAttribute(aitdi)){
    //Already processed but new in this branch
    n.setAttribute(aitdi,true);
    added.insert( n );
    for( size_t i=0; i< n.getNumChildren(); i++ ){
      addTermEfficient(n[i],added);
    }
  }

}


void TermDb::addTerm( Node n, std::set< Node >& added, bool withinQuant ){
  //don't add terms in quantifier bodies
  if( withinQuant && !Options::current()->registerQuantBodyTerms ){
    return;
  }
  if( d_processed.find( n )==d_processed.end() ){
    ++(d_quantEngine->d_statistics.d_term_in_termdb);
    d_processed.insert(n);
    d_type_map[ n.getType() ].push_back( n );
    n.setAttribute(AvailableInTermDb(),true);
    //if this is an atomic trigger, consider adding it
    //Call the children?
    if( Trigger::isAtomicTrigger( n ) ){
      if( !n.hasAttribute(InstConstantAttribute()) ){
        Debug("term-db") << "register trigger term " << n << std::endl;
        //std::cout << "register trigger term " << n << std::endl;
        Node op = n.getOperator();
        d_op_map[op].push_back( n );
        added.insert( n );

        uf::InstantiatorTheoryUf* d_ith = (uf::InstantiatorTheoryUf*)d_quantEngine->getInstantiator( THEORY_UF );
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          addTerm( n[i], added, withinQuant );
          if( Options::current()->efficientEMatching ){
            if( d_parents[n[i]][op].empty() ){
              //must add parent to equivalence class info
              Node nir = d_ith->getRepresentative( n[i] );
              uf::EqClassInfo* eci_nir = d_ith->getEquivalenceClassInfo( nir );
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
          if( Options::current()->eagerInstQuant ){
            if( !n.hasAttribute(InstLevelAttribute()) && n.getAttribute(InstLevelAttribute())==0 ){
              int addedLemmas = 0;
              for( int i=0; i<(int)d_ith->d_op_triggers[op].size(); i++ ){
                addedLemmas += d_ith->d_op_triggers[op][i]->addTerm( n );
              }
              //Message() << "Terms, added lemmas: " << addedLemmas << std::endl;
              d_quantEngine->flushLemmas( &d_quantEngine->getTheoryEngine()->getTheory( THEORY_QUANTIFIERS )->getOutputChannel() );
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
    if( Options::current()->efficientEMatching && !n.hasAttribute(InstConstantAttribute())){
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
     if( !it->second.empty() ){
       if( it->second[0].getType()==NodeManager::currentNM()->booleanType() ){
         d_pred_map_trie[ 0 ][ it->first ].d_data.clear();
         d_pred_map_trie[ 1 ][ it->first ].d_data.clear();
       }else{
         d_func_map_trie[ it->first ].d_data.clear();
         for( int i=0; i<(int)it->second.size(); i++ ){
           Node n = it->second[i];
           if( !n.getAttribute(NoMatchAttribute()) ){
             if( !d_func_map_trie[ it->first ].addTerm( d_quantEngine, n ) ){
               NoMatchAttribute nma;
               n.setAttribute(nma,true);
               congruentCount++;
             }else{
               nonCongruentCount++;
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
     eq::EqClassIterator eqc( d_quantEngine->getEqualityQuery()->getRepresentative( n ),
                              d_quantEngine->getEqualityQuery()->getEngine() );
     while( !eqc.isFinished() ){
       Node en = (*eqc);
       if( en.getKind()==APPLY_UF && !en.hasAttribute(InstConstantAttribute()) ){
         if( !en.getAttribute(NoMatchAttribute()) ){
           Node op = en.getOperator();
           if( !d_pred_map_trie[i][op].addTerm( d_quantEngine, en ) ){
             NoMatchAttribute nma;
             en.setAttribute(nma,true);
             congruentCount++;
           }else{
             nonCongruentCount++;
           }
         }else{
           alreadyCongruentCount++;
         }
       }
       ++eqc;
     }
   }
   Debug("term-db-cong") << "TermDb: Reset" << std::endl;
   Debug("term-db-cong") << "Congruent/Non-Congruent = ";
   Debug("term-db-cong") << congruentCount << "(" << alreadyCongruentCount << ") / " << nonCongruentCount << std::endl;
}

void TermDb::registerModelBasis( Node n, Node gn ){
  if( d_model_basis.find( n )==d_model_basis.end() ){
    d_model_basis[n] = gn;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerModelBasis( n[i], gn[i] );
    }
  }
}

Node TermDb::getModelBasisTerm( TypeNode tn, int i ){
  if( d_model_basis_term.find( tn )==d_model_basis_term.end() ){
    Node mbt;
    if( d_type_map[ tn ].empty() ){
      std::stringstream ss;
      ss << Expr::setlanguage(Options::current()->outputLanguage);
      ss << "e_" << tn;
      mbt = NodeManager::currentNM()->mkVar( ss.str(), tn );
    }else{
      mbt = d_type_map[ tn ][ 0 ];
    }
    ModelBasisAttribute mba;
    mbt.setAttribute(mba,true);
    d_model_basis_term[tn] = mbt;
  }
  return d_model_basis_term[tn];
}

Node TermDb::getModelBasisOpTerm( Node op ){
  if( d_model_basis_op_term.find( op )==d_model_basis_op_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( size_t i=0; i<t.getNumChildren()-1; i++ ){
      children.push_back( getModelBasisTerm( t[i] ) );
    }
    d_model_basis_op_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
  }
  return d_model_basis_op_term[op];
}

void TermDb::computeModelBasisArgAttribute( Node n ){
  if( !n.hasAttribute(ModelBasisArgAttribute()) ){
    uint64_t val = 0;
    //determine if it has model basis attribute
    for( int j=0; j<(int)n.getNumChildren(); j++ ){
      if( n[j].getAttribute(ModelBasisAttribute()) ){
        val = 1;
        break;
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
    }
  }
}

void TermDb::setInstantiationLevelAttr( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevelAttr( n[i], level );
  }
}


void TermDb::setInstantiationConstantAttr( Node n, Node f ){
  if( !n.hasAttribute(InstConstantAttribute()) ){
    bool setAttr = false;
    if( n.getKind()==INST_CONSTANT ){
      setAttr = true;
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        setInstantiationConstantAttr( n[i], f );
        if( n[i].hasAttribute(InstConstantAttribute()) ){
          setAttr = true;
        }
      }
    }
    if( setAttr ){
      InstConstantAttribute ica;
      n.setAttribute(ica,f);
      //also set the no-match attribute
      NoMatchAttribute nma;
      n.setAttribute(nma,true);
    }
  }
}


Node TermDb::getCounterexampleBody( Node f ){
  std::map< Node, Node >::iterator it = d_counterexample_body.find( f );
  if( it==d_counterexample_body.end() ){
    makeInstantiationConstantsFor( f );
    Node n = getSubstitutedNode( f[1], f );
    d_counterexample_body[ f ] = n;
    return n;
  }else{
    return it->second;
  }
}

Node TermDb::getSkolemizedBody( Node f ){
  Assert( f.getKind()==FORALL );
  if( d_skolem_body.find( f )==d_skolem_body.end() ){
    std::vector< Node > vars;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      Node skv = NodeManager::currentNM()->mkSkolem( f[0][i].getType() );
      d_skolem_constants[ f ].push_back( skv );
      vars.push_back( f[0][i] );
    }
    d_skolem_body[ f ] = f[ 1 ].substitute( vars.begin(), vars.end(),
                                            d_skolem_constants[ f ].begin(), d_skolem_constants[ f ].end() );
    if( f.hasAttribute(InstLevelAttribute()) ){
      setInstantiationLevelAttr( d_skolem_body[ f ], f.getAttribute(InstLevelAttribute()) );
    }
  }
  return d_skolem_body[ f ];
}


Node TermDb::getSubstitutedNode( Node n, Node f ){
  return convertNodeToPattern(n,f,d_vars[f],d_inst_constants[ f ]);
}

Node TermDb::convertNodeToPattern( Node n, Node f, const std::vector<Node> & vars,
                                              const std::vector<Node> & inst_constants){
  Node n2 = n.substitute( vars.begin(), vars.end(),
                          inst_constants.begin(),
                          inst_constants.end() );
  setInstantiationConstantAttr( n2, f );
  return n2;
}

Node TermDb::getFreeVariableForInstConstant( Node n ){
  TypeNode tn = n.getType();
  if( d_free_vars.find( tn )==d_free_vars.end() ){
    //if integer or real, make zero
    if( tn==NodeManager::currentNM()->integerType() || tn==NodeManager::currentNM()->realType() ){
      Rational z(0);
      d_free_vars[tn] = NodeManager::currentNM()->mkConst( z );
    }else{
      if( d_type_map[ tn ].empty() ){
        d_free_vars[tn] = NodeManager::currentNM()->mkVar( tn );
      }else{
        d_free_vars[tn] = d_type_map[ tn ][ 0 ];
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
