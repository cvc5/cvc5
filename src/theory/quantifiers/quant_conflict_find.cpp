/*********************                                                        */
/*! \file quant_conflict_find.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief quant conflict find class
 **
 **/

#include <vector>

#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

Node QcfNodeIndex::existsTerm( TNode n, std::vector< TNode >& reps, int index ) {
  if( index==(int)reps.size() ){
    if( d_children.empty() ){
      return Node::null();
    }else{
      return d_children.begin()->first;
    }
  }else{
    std::map< TNode, QcfNodeIndex >::iterator it = d_children.find( reps[index] );
    if( it==d_children.end() ){
      return Node::null();
    }else{
      return it->second.existsTerm( n, reps, index+1 );
    }
  }
}

Node QcfNodeIndex::addTerm( TNode n, std::vector< TNode >& reps, int index ) {
  if( index==(int)reps.size() ){
    if( d_children.empty() ){
      d_children[ n ].clear();
      return n;
    }else{
      return d_children.begin()->first;
    }
  }else{
    return d_children[reps[index]].addTerm( n, reps, index+1 );
  }
}


void QcfNodeIndex::debugPrint( const char * c, int t ) {
  for( std::map< TNode, QcfNodeIndex >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
    if( !it->first.isNull() ){
      for( int j=0; j<t; j++ ){ Trace(c) << "  "; }
      Trace(c) << it->first << " : " << std::endl;
      it->second.debugPrint( c, t+1 );
    }
  }
}


void QuantInfo::initialize( Node q, Node qn ) {
  d_q = q;
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_match.push_back( TNode::null() );
    d_match_term.push_back( TNode::null() );
  }

  //register the variables
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_var_num[q[0][i]] = i;
    d_vars.push_back( q[0][i] );
  }

  registerNode( qn, true, true );


  Trace("qcf-qregister") << "- Make match gen structure..." << std::endl;
  d_mg = new MatchGen( this, qn );

  if( d_mg->isValid() ){
    for( unsigned j=q[0].getNumChildren(); j<d_vars.size(); j++ ){
      if( d_vars[j].getKind()!=BOUND_VARIABLE ){
        bool beneathQuant = d_nbeneathQuant.find( d_vars[j] )==d_nbeneathQuant.end();
        d_var_mg[j] = new MatchGen( this, d_vars[j], true, beneathQuant );
        if( !d_var_mg[j]->isValid() && options::qcfMode()<QCF_PARTIAL ){
          d_mg->setInvalid();
          break;
        }else{
          std::vector< int > bvars;
          d_var_mg[j]->determineVariableOrder( this, bvars );
        }
      }
    }

    if( d_mg->isValid() ){
      std::vector< int > bvars;
      d_mg->determineVariableOrder( this, bvars );
    }

    //must also contain all variables?
    if( d_isPartial ){
      for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
        if( d_has_var.find( q[0][i] )==d_has_var.end() ){
          d_isPartial = false;
          d_mg->setInvalid();
          break;
        }
      }
    }
  }
  Trace("qcf-qregister-summary") << "QCF register : " << ( d_mg->isValid() ? ( isPartial() ? "PARTIAL " : "VALID " ) : "INVALID" ) << " : " << q << std::endl;
}

void QuantInfo::registerNode( Node n, bool hasPol, bool pol, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Register : " << n << std::endl;
  if( n.getKind()==FORALL ){
    registerNode( n[1], hasPol, pol, true );
  }else{
    if( n.getKind()!=OR && n.getKind()!=AND && n.getKind()!=IFF && n.getKind()!=NOT ){
      if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
        //literals
        if( n.getKind()==EQUAL ){
          for( unsigned i=0; i<n.getNumChildren(); i++ ){
            flatten( n[i], beneathQuant );
          }
        }else if( MatchGen::isHandledUfTerm( n ) ){
          flatten( n, beneathQuant );
        }else if( n.getKind()==ITE ){
          if( !n[1].getType().isBoolean() ){
            for( unsigned i=1; i<=2; i++ ){
              flatten( n[i], beneathQuant );
            }
          }
        }
      }
    }
    if( isVar( n ) && !beneathQuant ){
      d_nbeneathQuant[n] = true;
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
      //QcfNode * qcfc = new QcfNode( d_c );
      //qcfc->d_parent = qcf;
      //qcf->d_child[i] = qcfc;
      registerNode( n[i], newHasPol, newPol, beneathQuant );
    }
  }
}

void QuantInfo::flatten( Node n, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Flatten : " << n << std::endl;
  if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
    if( d_var_num.find( n )==d_var_num.end() ){
      Trace("qcf-qregister-debug2") << "Add FLATTEN VAR : " << n << std::endl;
      d_var_num[n] = d_vars.size();
      d_vars.push_back( n );
      d_match.push_back( TNode::null() );
      d_match_term.push_back( TNode::null() );
      if( n.getKind()==ITE ){
        registerNode( n, false, false );
      }else{
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          flatten( n[i], beneathQuant );
        }
      }
      if( !beneathQuant ){
        d_nbeneathQuant[n] = true;
      }
    }else{
      Trace("qcf-qregister-debug2") << "...already processed" << std::endl;
    }
  }else{
    Trace("qcf-qregister-debug2") << "...is ground." << std::endl;
  }
}


void QuantInfo::reset_round( QuantConflictFind * p ) {
  for( unsigned i=0; i<d_match.size(); i++ ){
    d_match[i] = TNode::null();
    d_match_term[i] = TNode::null();
  }
  d_curr_var_deq.clear();
  //add built-in variable constraints
  for( unsigned r=0; r<2; r++ ){
    for( std::map< int, std::vector< Node > >::iterator it = d_var_constraint[r].begin();
         it != d_var_constraint[r].end(); ++it ){
      for( unsigned j=0; j<it->second.size(); j++ ){
        Node rr = it->second[j];
        if( !isVar( rr ) ){
          rr = p->getRepresentative( rr );
        }
        if( addConstraint( p, it->first, rr, r==0 )==-1 ){
          d_var_constraint[0].clear();
          d_var_constraint[1].clear();
          //quantified formula is actually equivalent to true
          Trace("qcf-qregister") << "Quantifier is equivalent to true!!!" << std::endl;
          d_mg->d_children.clear();
          d_mg->d_n = NodeManager::currentNM()->mkConst( true );
          d_mg->d_type = MatchGen::typ_ground;
          return;
        }
      }
    }
  }
  d_mg->reset_round( p );
  for( std::map< int, MatchGen * >::iterator it = d_var_mg.begin(); it != d_var_mg.end(); ++it ){
    it->second->reset_round( p );
  }
}

int QuantInfo::getCurrentRepVar( int v ) {
  if( v!=-1 && !d_match[v].isNull() ){
    int vn = getVarNum( d_match[v] );
    if( vn!=-1 ){
      //int vr = getCurrentRepVar( vn );
      //d_match[v] = d_vars[vr];
      //return vr;
      return getCurrentRepVar( vn );
    }
  }
  return v;
}

TNode QuantInfo::getCurrentValue( TNode n ) {
  int v = getVarNum( n );
  if( v==-1 ){
    return n;
  }else{
    if( d_match[v].isNull() ){
      return n;
    }else{
      Assert( getVarNum( d_match[v] )!=v );
      return getCurrentValue( d_match[v] );
    }
  }
}

bool QuantInfo::getCurrentCanBeEqual( QuantConflictFind * p, int v, TNode n, bool chDiseq ) {
  //check disequalities
  std::map< int, std::map< TNode, int > >::iterator itd = d_curr_var_deq.find( v );
  if( itd!=d_curr_var_deq.end() ){
    for( std::map< TNode, int >::iterator it = itd->second.begin(); it != itd->second.end(); ++it ){
      Node cv = getCurrentValue( it->first );
      Debug("qcf-ccbe") << "compare " << cv << " " << n << std::endl;
      if( cv==n ){
        return false;
      }else if( chDiseq && !isVar( n ) && !isVar( cv ) ){
        //they must actually be disequal if we are looking for conflicts
        if( !p->areDisequal( n, cv ) ){
          return false;
        }
      }
    }
  }
  return true;
}

int QuantInfo::addConstraint( QuantConflictFind * p, int v, TNode n, bool polarity ) {
  v = getCurrentRepVar( v );
  int vn = getVarNum( n );
  vn = vn==-1 ? -1 : getCurrentRepVar( vn );
  n = getCurrentValue( n );
  return addConstraint( p, v, n, vn, polarity, false );
}

int QuantInfo::addConstraint( QuantConflictFind * p, int v, TNode n, int vn, bool polarity, bool doRemove ) {
  //for handling equalities between variables, and disequalities involving variables
  Debug("qcf-match-debug") << "- " << (doRemove ? "un" : "" ) << "constrain : " << v << " -> " << n << " (cv=" << getCurrentValue( n ) << ")";
  Debug("qcf-match-debug") << ", (vn=" << vn << "), polarity = " << polarity << std::endl;
  Assert( doRemove || n==getCurrentValue( n ) );
  Assert( doRemove || v==getCurrentRepVar( v ) );
  Assert( doRemove || vn==getCurrentRepVar( getVarNum( n ) ) );
  if( polarity ){
    if( vn!=v ){
      if( doRemove ){
        if( vn!=-1 ){
          //if set to this in the opposite direction, clean up opposite instead
          //          std::map< int, TNode >::iterator itmn = d_match.find( vn );
          if( d_match[vn]==d_vars[v] ){
            return addConstraint( p, vn, d_vars[v], v, true, true );
          }else{
            //unsetting variables equal
            std::map< int, std::map< TNode, int > >::iterator itd = d_curr_var_deq.find( vn );
            if( itd!=d_curr_var_deq.end() ){
              //remove disequalities owned by this
              std::vector< TNode > remDeq;
              for( std::map< TNode, int >::iterator it = itd->second.begin(); it != itd->second.end(); ++it ){
                if( it->second==v ){
                  remDeq.push_back( it->first );
                }
              }
              for( unsigned i=0; i<remDeq.size(); i++ ){
                d_curr_var_deq[vn].erase( remDeq[i] );
              }
            }
          }
        }
        d_match[v] = TNode::null();
        return 1;
      }else{
        //std::map< int, TNode >::iterator itm = d_match.find( v );

        if( vn!=-1 ){
          Debug("qcf-match-debug") << "  ...Variable bound to variable" << std::endl;
          //std::map< int, TNode >::iterator itmn = d_match.find( vn );
          if( d_match[v].isNull() ){
            //setting variables equal
            bool alreadySet = false;
            if( !d_match[vn].isNull() ){
              alreadySet = true;
              Assert( !isVar( d_match[vn] ) );
            }

            //copy or check disequalities
            std::map< int, std::map< TNode, int > >::iterator itd = d_curr_var_deq.find( v );
            if( itd!=d_curr_var_deq.end() ){
              for( std::map< TNode, int >::iterator it = itd->second.begin(); it != itd->second.end(); ++it ){
                Node dv = getCurrentValue( it->first );
                if( !alreadySet ){
                  if( d_curr_var_deq[vn].find( dv )==d_curr_var_deq[vn].end() ){
                    d_curr_var_deq[vn][dv] = v;
                  }
                }else{
                  if( !p->areMatchDisequal( d_match[vn], dv ) ){
                    Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
                    return -1;
                  }
                }
              }
            }
            if( alreadySet ){
              n = getCurrentValue( n );
            }
          }else{
            if( d_match[vn].isNull() ){
              Debug("qcf-match-debug") << " ...Reverse direction" << std::endl;
              //set the opposite direction
              return addConstraint( p, vn, d_vars[v], v, true, false );
            }else{
              Debug("qcf-match-debug") << "  -> Both variables bound, compare" << std::endl;
              //are they currently equal
              return p->areMatchEqual( d_match[v], d_match[vn] ) ? 0 : -1;
            }
          }
        }else{
          Debug("qcf-match-debug") << "  ...Variable bound to ground" << std::endl;
          if( d_match[v].isNull() ){
          }else{
            //compare ground values
            Debug("qcf-match-debug") << "  -> Ground value, compare " << d_match[v] << " "<< n << std::endl;
            return p->areMatchEqual( d_match[v], n ) ? 0 : -1;
          }
        }
        if( setMatch( p, v, n ) ){
          Debug("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }else{
          Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
          return -1;
        }
      }
    }else{
      Debug("qcf-match-debug") << "  -> redundant, variable identity" << std::endl;
      return 0;
    }
  }else{
    if( vn==v ){
      Debug("qcf-match-debug") << "  -> fail, variable identity" << std::endl;
      return -1;
    }else{
      if( doRemove ){
        Assert( d_curr_var_deq[v].find( n )!=d_curr_var_deq[v].end() );
        d_curr_var_deq[v].erase( n );
        return 1;
      }else{
        if( d_curr_var_deq[v].find( n )==d_curr_var_deq[v].end() ){
          //check if it respects equality
          //std::map< int, TNode >::iterator itm = d_match.find( v );
          if( !d_match[v].isNull() ){
            TNode nv = getCurrentValue( n );
            if( !p->areMatchDisequal( nv, d_match[v] ) ){
              Debug("qcf-match-debug") << "  -> fail, conflicting disequality" << std::endl;
              return -1;
            }
          }
          d_curr_var_deq[v][n] = v;
          Debug("qcf-match-debug") << "  -> success" << std::endl;
          return 1;
        }else{
          Debug("qcf-match-debug") << "  -> redundant disequality" << std::endl;
          return 0;
        }
      }
    }
  }
}

bool QuantInfo::isConstrainedVar( int v ) {
  if( d_curr_var_deq.find( v )!=d_curr_var_deq.end() && !d_curr_var_deq[v].empty() ){
    return true;
  }else{
    Node vv = getVar( v );
    //for( std::map< int, TNode >::iterator it = d_match.begin(); it != d_match.end(); ++it ){
    for( unsigned i=0; i<d_match.size(); i++ ){
      if( d_match[i]==vv ){
        return true;
      }
    }
    for( std::map< int, std::map< TNode, int > >::iterator it = d_curr_var_deq.begin(); it != d_curr_var_deq.end(); ++it ){
      for( std::map< TNode, int >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        if( it2->first==vv ){
          return true;
        }
      }
    }
    return false;
  }
}

bool QuantInfo::setMatch( QuantConflictFind * p, int v, TNode n ) {
  if( getCurrentCanBeEqual( p, v, n ) ){
    Debug("qcf-match-debug") << "-- bind : " << v << " -> " << n << ", checked " <<  d_curr_var_deq[v].size() << " disequalities" << std::endl;
    d_match[v] = n;
    return true;
  }else{
    return false;
  }
}

bool QuantInfo::isMatchSpurious( QuantConflictFind * p ) {
  for( int i=0; i<getNumVars(); i++ ){
    //std::map< int, TNode >::iterator it = d_match.find( i );
    if( !d_match[i].isNull() ){
      if( !getCurrentCanBeEqual( p, i, d_match[i], p->d_effort==QuantConflictFind::effort_conflict ) ){
        return true;
      }
    }
  }
  return false;
}

bool QuantInfo::completeMatch( QuantConflictFind * p, std::vector< int >& assigned ) {
  //assign values for variables that were unassigned (usually not necessary, but handles corner cases)
  Trace("qcf-check") << std::endl;
  std::vector< int > unassigned[2];
  std::vector< TypeNode > unassigned_tn[2];
  for( int i=0; i<getNumVars(); i++ ){
    if( d_match[i].isNull() ){
      //Assert( i<(int)q[0].getNumChildren() );
      int rindex = d_var_mg.find( i )==d_var_mg.end() ? 1 : 0;
      unassigned[rindex].push_back( i );
      unassigned_tn[rindex].push_back( getVar( i ).getType() );
      assigned.push_back( i );
    }
  }
  bool success = true;
  for( unsigned r=0; r<2; r++ ){
    if( success && !unassigned[r].empty() ){
      Trace("qcf-check") << "Assign to unassigned, rep = " << r << "..." << std::endl;
      int index = 0;
      std::vector< int > eqc_count;
      bool doFail = false;
      do {
        if( doFail ){
          Trace("qcf-check-unassign") << "Failure, try again..." << std::endl;
        }
        bool invalidMatch = false;
        while( ( index>=0 && (int)index<(int)unassigned[r].size() ) || invalidMatch || doFail ){
          invalidMatch = false;
          if( !doFail && index==(int)eqc_count.size() ){
            //check if it has now been assigned
            if( r==0 ){
              if( !isConstrainedVar( unassigned[r][index] ) ){
                eqc_count.push_back( -1 );
              }else{
                d_var_mg[ unassigned[r][index] ]->reset( p, true, this );
                eqc_count.push_back( 0 );
              }
            }else{
              eqc_count.push_back( 0 );
            }
          }else{
            if( r==0 ){
              if( !doFail && !isConstrainedVar( unassigned[r][index] ) ){
                Trace("qcf-check-unassign") << "Succeeded, variable unconstrained at " << index << std::endl;
                index++;
              }else if( !doFail && d_var_mg[unassigned[r][index]]->getNextMatch( p, this ) ){
                Trace("qcf-check-unassign") << "Succeeded match with mg at " << index << std::endl;
                index++;
              }else{
                Trace("qcf-check-unassign") << "Failed match with mg at " << index << std::endl;
                do{
                  if( !doFail ){
                    eqc_count.pop_back();
                  }else{
                    doFail = false;
                  }
                  index--;
                }while( index>=0 && eqc_count[index]==-1 );
              }
            }else{
              Assert( doFail || index==(int)eqc_count.size()-1 );
              if( !doFail && eqc_count[index]<(int)p->d_eqcs[unassigned_tn[r][index]].size() ){
                int currIndex = eqc_count[index];
                eqc_count[index]++;
                Trace("qcf-check-unassign") << unassigned[r][index] << "->" << p->d_eqcs[unassigned_tn[r][index]][currIndex] << std::endl;
                if( setMatch( p, unassigned[r][index], p->d_eqcs[unassigned_tn[r][index]][currIndex] ) ){
                  //if( currIndex==0 ){
                  //  Assert( p->areEqual( p->d_model_basis[unassigned_tn[r][index]], p->d_eqcs[unassigned_tn[r][index]][currIndex] ) );
                  //  d_match_term[unassigned[r][index]] = p->d_model_basis[unassigned_tn[r][index]];
                  //}else{
                  d_match_term[unassigned[r][index]] = TNode::null();
                  //}
                  Trace("qcf-check-unassign") << "Succeeded match " << index << std::endl;
                  index++;
                }else{
                  Trace("qcf-check-unassign") << "Failed match " << index << std::endl;
                  invalidMatch = true;
                }
              }else{
                Trace("qcf-check-unassign") << "No more matches " << index << std::endl;
                if( !doFail ){
                  eqc_count.pop_back();
                }else{
                  doFail = false;
                }
                index--;
              }
            }
          }
        }
        success = index>=0;
        if( success ){
          doFail = true;
          Trace("qcf-check-unassign") << "  Try: " << std::endl;
          for( unsigned i=0; i<unassigned[r].size(); i++ ){
            int ui = unassigned[r][i];
            if( !d_match[ui].isNull() ){
              Trace("qcf-check-unassign") << "  Assigned #" << ui << " : " << d_vars[ui] << " -> " << d_match[ui] << std::endl;
            }
          }
        }
      }while( success && isMatchSpurious( p ) );
    }
  }
  if( success ){
    return true;
  }else{
    for( unsigned i=0; i<assigned.size(); i++ ){
      d_match[ assigned[i] ] = TNode::null();
    }
    assigned.clear();
    return false;
  }
}

void QuantInfo::debugPrintMatch( const char * c ) {
  for( int i=0; i<getNumVars(); i++ ){
    Trace(c) << "  " << d_vars[i] << " -> ";
    if( !d_match[i].isNull() ){
      Trace(c) << d_match[i];
    }else{
      Trace(c) << "(unassigned) ";
    }
    if( !d_curr_var_deq[i].empty() ){
      Trace(c) << ", DEQ{ ";
      for( std::map< TNode, int >::iterator it = d_curr_var_deq[i].begin(); it != d_curr_var_deq[i].end(); ++it ){
        Trace(c) << it->first << " ";
      }
      Trace(c) << "}";
    }
    Trace(c) << std::endl;
  }
}

//void QuantInfo::addFuncParent( int v, Node f, int arg ) {
//  if( std::find( d_f_parent[v][f].begin(), d_f_parent[v][f].end(), arg )==d_f_parent[v][f].end() ){
//    d_f_parent[v][f].push_back( arg );
//  }
//}

MatchGen::MatchGen( QuantInfo * qi, Node n, bool isVar, bool beneathQuant ){
  Trace("qcf-qregister-debug") << "Make match gen for " << n << ", isVar = " << isVar << ", beneathQuant = " << beneathQuant << std::endl;
  std::vector< Node > qni_apps;
  d_qni_size = 0;
  if( isVar ){
    Assert( qi->d_var_num.find( n )!=qi->d_var_num.end() );
    if( isHandledUfTerm( n ) ){
      d_qni_var_num[0] = qi->getVarNum( n );
      d_qni_size++;
      d_type = typ_var;
      d_type_not = false;
      d_n = n;
      //Node f = getOperator( n );
      for( unsigned j=0; j<d_n.getNumChildren(); j++ ){
        Node nn = d_n[j];
        Trace("qcf-qregister-debug") << "  " << d_qni_size;
        if( qi->isVar( nn ) ){
          int v = qi->d_var_num[nn];
          Trace("qcf-qregister-debug") << " is var #" << v << std::endl;
          d_qni_var_num[d_qni_size] = v;
          //qi->addFuncParent( v, f, j );
          if( nn.getKind()==BOUND_VARIABLE && !beneathQuant ){
            qi->d_has_var[nn] = true;
          }
        }else{
          Trace("qcf-qregister-debug") << " is gterm " << nn << std::endl;
          d_qni_gterm[d_qni_size] = nn;
        }
        d_qni_size++;
      }
    }else if( n.getKind()==ITE ){
      d_type = typ_ite_var;
      d_type_not = false;
      d_n = n;
      d_children.push_back( MatchGen( qi, d_n[0] ) );
      if( d_children[0].isValid() ){
        d_type = typ_ite_var;
        for( unsigned i=1; i<=2; i++ ){
          Node nn = n.eqNode( n[i] );
          d_children.push_back( MatchGen( qi, nn ) );
          d_children[d_children.size()-1].d_qni_bound_except.push_back( 0 );
          if( !d_children[d_children.size()-1].isValid() && options::qcfMode()<QCF_PARTIAL ){
            setInvalid();
            break;
          }
        }
      }else{
        d_type = typ_invalid;
      }
    }else{
      //for now, unknown term
      d_type = typ_invalid;
    }
  }else{
    if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
      d_type_not = false;
      d_n = n;
      if( d_n.getKind()==NOT ){
        d_n = d_n[0];
        d_type_not = !d_type_not;
      }

      if( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==IFF || d_n.getKind()==ITE || d_n.getKind()==FORALL ){
        //non-literals
        d_type = typ_formula;
        bool nBeneathQuant = beneathQuant || d_n.getKind()==FORALL;
        for( unsigned i=0; i<d_n.getNumChildren(); i++ ){
          if( d_n.getKind()!=FORALL || i==1 ){
            d_children.push_back( MatchGen( qi, d_n[i], false, nBeneathQuant ) );
            if( !d_children[d_children.size()-1].isValid() && options::qcfMode()<QCF_PARTIAL ){
              setInvalid();
              break;
            }
          }
          /*
          else if( isTop && n.getKind()==OR && d_children[d_children.size()-1].d_type==typ_var_eq ){
            Trace("qcf-qregister-debug") << "Remove child, make built-in constraint" << std::endl;
            //if variable equality/disequality at top level, remove immediately
            bool cIsNot = d_children[d_children.size()-1].d_type_not;
            Node cn = d_children[d_children.size()-1].d_n;
            Assert( cn.getKind()==EQUAL );
            Assert( p->d_qinfo[q].isVar( cn[0] ) || p->d_qinfo[q].isVar( cn[1] ) );
            //make it a built-in constraint instead
            for( unsigned i=0; i<2; i++ ){
              if( p->d_qinfo[q].isVar( cn[i] ) ){
                int v = p->d_qinfo[q].getVarNum( cn[i] );
                Node cno = cn[i==0 ? 1 : 0];
                p->d_qinfo[q].d_var_constraint[ cIsNot ? 0 : 1 ][v].push_back( cno );
                break;
              }
            }
            d_children.pop_back();
          }
          */
        }
      }else{
        d_type = typ_invalid;
        //literals
        if( d_n.getKind()==EQUAL ){
          for( unsigned i=0; i<2; i++ ){
            if( quantifiers::TermDb::hasBoundVarAttr( d_n[i] ) ){
              if( !qi->isVar( d_n[i] ) ){
                Trace("qcf-qregister-debug")  << "ERROR : not var " << d_n[i] << std::endl;
              }else if( d_n[i].getKind()==BOUND_VARIABLE && !beneathQuant ){
                qi->d_has_var[d_n[i]] = true;
              }
              Assert( qi->isVar( d_n[i] ) );
            }else{
              d_qni_gterm[i] = d_n[i];
            }
          }
          d_type = typ_eq;
        }else if( isHandledUfTerm( d_n ) ){
          Assert( qi->isVar( d_n ) );
          d_type = typ_pred;
        }else{
          Trace("qcf-invalid") << "Unhandled : " << d_n << std::endl;
        }
      }
    }else{
      //we will just evaluate
      d_n = n;
      d_type = typ_ground;
    }
    //if( d_type!=typ_invalid ){
      //determine an efficient children ordering
      //if( !d_children.empty() ){
        //for( unsigned i=0; i<d_children.size(); i++ ){
        //  d_children_order.push_back( i );
        //}
        //if( !d_n.isNull() && ( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==IFF ) ){
          //sort based on the type of the constraint : ground comes first, then literals, then others
          //MatchGenSort mgs;
          //mgs.d_mg = this;
          //std::sort( d_children_order.begin(), d_children_order.end(), mgs );
        //}
      //}
    //}
  }
  Trace("qcf-qregister-debug")  << "Done make match gen " << n << ", type = ";
  debugPrintType( "qcf-qregister-debug", d_type, true );
  Trace("qcf-qregister-debug") << std::endl;
  //Assert( d_children.size()==d_children_order.size() );

  if( !isValid() && options::qcfMode()>=QCF_PARTIAL ){
    qi->d_isPartial = true;
  }
}

void MatchGen::collectBoundVar( QuantInfo * qi, Node n, std::vector< int >& cbvars ) {
  int v = qi->getVarNum( n );
  if( v!=-1 && std::find( cbvars.begin(), cbvars.end(), v )==cbvars.end() ){
    cbvars.push_back( v );
  }
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    collectBoundVar( qi, n[i], cbvars );
  }
}

void MatchGen::determineVariableOrder( QuantInfo * qi, std::vector< int >& bvars ) {
  Trace("qcf-qregister-debug") << "Determine variable order " << d_n << std::endl;
  bool isCom = d_type==typ_formula && ( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==IFF );
  std::map< int, std::vector< int > > c_to_vars;
  std::map< int, std::vector< int > > vars_to_c;
  std::map< int, int > vb_count;
  std::map< int, int > vu_count;
  std::vector< bool > assigned;
  Trace("qcf-qregister-debug") << "Calculate bound variables..." << std::endl;
  for( unsigned i=0; i<d_children.size(); i++ ){
    collectBoundVar( qi, d_children[i].d_n, c_to_vars[i] );
    assigned.push_back( false );
    vb_count[i] = 0;
    vu_count[i] = 0;
    for( unsigned j=0; j<c_to_vars[i].size(); j++ ){
      int v = c_to_vars[i][j];
      vars_to_c[v].push_back( i );
      if( std::find( bvars.begin(), bvars.end(), v )==bvars.end() ){
        vu_count[i]++;
        if( !isCom ){
          bvars.push_back( v );
        }
      }else{
        vb_count[i]++;
      }
    }
  }
  if( isCom ){
    //children that bind the least number of unbound variables go first
    do {
      int min_score = -1;
      int min_score_index = -1;
      for( unsigned i=0; i<d_children.size(); i++ ){
        if( !assigned[i] ){
          int score = vu_count[i];
          if( min_score==-1 || score<min_score ){
            min_score = score;
            min_score_index = i;
          }
        }
      }
      Trace("qcf-qregister-debug") << "...assign child " << min_score_index << "/" << d_children.size() << std::endl;
      Assert( min_score_index!=-1 );
      //add to children order
      d_children_order.push_back( min_score_index );
      assigned[min_score_index] = true;
      //if( vb_count[min_score_index]==0 ){
      //  d_independent.push_back( min_score_index );
      //}
      //determine order internal to children
      d_children[min_score_index].determineVariableOrder( qi, bvars );
      Trace("qcf-qregister-debug")  << "...bind variables" << std::endl;
      //now, make it a bound variable
      for( unsigned i=0; i<c_to_vars[min_score_index].size(); i++ ){
        int v = c_to_vars[min_score_index][i];
        if( std::find( bvars.begin(), bvars.end(), v )==bvars.end() ){
          for( unsigned j=0; j<vars_to_c[v].size(); j++ ){
            int vc = vars_to_c[v][j];
            vu_count[vc]--;
            vb_count[vc]++;
          }
          bvars.push_back( v );
        }
      }
      Trace("qcf-qregister-debug") << "...done assign child " << min_score_index << std::endl;
    }while( d_children_order.size()!=d_children.size() );
    Trace("qcf-qregister-debug") << "Done assign variable ordering for " << d_n << std::endl;
  }else{
    for( unsigned i=0; i<d_children.size(); i++ ){
      d_children_order.push_back( i );
      d_children[i].determineVariableOrder( qi, bvars );
    }
  }
}


void MatchGen::reset_round( QuantConflictFind * p ) {
  for( unsigned i=0; i<d_children.size(); i++ ){
    d_children[i].reset_round( p );
  }
  for( std::map< int, TNode >::iterator it = d_qni_gterm.begin(); it != d_qni_gterm.end(); ++it ){
    d_qni_gterm_rep[it->first] = p->getRepresentative( it->second );
  }
  if( d_type==typ_ground ){
    int e = p->evaluate( d_n );
    if( e==1 ){
      d_ground_eval[0] = p->d_true;
    }else if( e==-1 ){
      d_ground_eval[0] = p->d_false;
    }
  }else if( d_type==typ_eq ){
    for( unsigned i=0; i<d_n.getNumChildren(); i++ ){
      if( !quantifiers::TermDb::hasBoundVarAttr( d_n[i] ) ){
        d_ground_eval[i] = p->evaluateTerm( d_n[i] );
      }
    }
  }
}

void MatchGen::reset( QuantConflictFind * p, bool tgt, QuantInfo * qi ) {
  d_tgt = d_type_not ? !tgt : tgt;
  Debug("qcf-match") << "     Reset for : " << d_n << ", type : ";
  debugPrintType( "qcf-match", d_type );
  Debug("qcf-match") << ", tgt = " << d_tgt << ", children = " << d_children.size() << " " << d_children_order.size() << std::endl;
  d_qn.clear();
  d_qni.clear();
  d_qni_bound.clear();
  d_child_counter = -1;

  //set up processing matches
  if( d_type==typ_invalid ){
    if( p->d_effort==QuantConflictFind::effort_partial ){
      d_child_counter = 0;
    }
  }else if( d_type==typ_ground ){
    if( d_ground_eval[0]==( d_tgt ? p->d_true : p->d_false ) ){
      d_child_counter = 0;
    }
  }else if( d_type==typ_var ){
    Assert( isHandledUfTerm( d_n ) );
    Node f = getOperator( p, d_n );
    Debug("qcf-match-debug") << "       reset: Var will match operators of " << f << std::endl;
    QcfNodeIndex * qni = p->getQcfNodeIndex( Node::null(), f );
    if( qni!=NULL ){
      d_qn.push_back( qni );
    }
    d_matched_basis = false;
  }else if( d_type==typ_pred || d_type==typ_eq ){
    //add initial constraint
    Node nn[2];
    int vn[2];
    if( d_type==typ_pred ){
      nn[0] = qi->getCurrentValue( d_n );
      vn[0] = qi->getCurrentRepVar( qi->getVarNum( nn[0] ) );
      nn[1] = p->getRepresentative( d_tgt ? p->d_true : p->d_false );
      vn[1] = -1;
      d_tgt = true;
    }else{
      for( unsigned i=0; i<2; i++ ){
        TNode nc;
        std::map< int, TNode >::iterator it = d_qni_gterm_rep.find( i );
        if( it!=d_qni_gterm_rep.end() ){
          nc = it->second;
        }else{
          nc = d_n[i];
        }
        nn[i] = qi->getCurrentValue( nc );
        vn[i] = qi->getCurrentRepVar( qi->getVarNum( nn[i] ) );
      }
    }
    bool success;
    if( vn[0]==-1 && vn[1]==-1 ){
      Debug("qcf-match-debug") << "       reset: check ground values " << nn[0] << " " << nn[1] << " (" << d_tgt << ")" << std::endl;
      //just compare values
      if( d_tgt ){
        success = p->areMatchEqual( nn[0], nn[1] );
      }else{
        if( p->d_effort==QuantConflictFind::effort_conflict ){
          success = p->areDisequal( nn[0], nn[1] );
        }else{
          success = p->areMatchDisequal( nn[0], nn[1] );
        }
      }
    }else{
      //otherwise, add a constraint to a variable
      if( vn[1]!=-1 && vn[0]==-1 ){
        //swap
        Node t = nn[1];
        nn[1] = nn[0];
        nn[0] = t;
        vn[0] = vn[1];
        vn[1] = -1;
      }
      Debug("qcf-match-debug") << "       reset: add constraint " << vn[0] << " -> " << nn[1] << " (vn=" << vn[1] << ")" << std::endl;
      //add some constraint
      int addc = qi->addConstraint( p, vn[0], nn[1], vn[1], d_tgt, false );
      success = addc!=-1;
      //if successful and non-redundant, store that we need to cleanup this
      if( addc==1 ){
        for( unsigned i=0; i<2; i++ ){
          if( vn[i]!=-1 && std::find( d_qni_bound_except.begin(), d_qni_bound_except.end(), i )==d_qni_bound_except.end() ){
            d_qni_bound[vn[i]] = vn[i];
          }
        }
        d_qni_bound_cons[vn[0]] = nn[1];
        d_qni_bound_cons_var[vn[0]] = vn[1];
      }
    }
    //if successful, we will bind values to variables
    if( success ){
      d_qn.push_back( NULL );
    }
  }else{
    if( d_children.empty() ){
      //add dummy
      d_qn.push_back( NULL );
    }else{
      if( d_tgt && d_n.getKind()==FORALL ){
        //return success once
        if( p->d_effort==QuantConflictFind::effort_partial ){
          d_child_counter = -2;
        }
      }else{
        //reset the first child to d_tgt
        d_child_counter = 0;
        getChild( d_child_counter )->reset( p, d_tgt, qi );
      }
    }
  }
  d_binding = false;
  Debug("qcf-match") << "     reset: Finished reset for " << d_n << ", success = " << ( !d_qn.empty() || d_child_counter!=-1 ) << std::endl;
}

bool MatchGen::getNextMatch( QuantConflictFind * p, QuantInfo * qi ) {
  Debug("qcf-match") << "     Get next match for : " << d_n << ", type = ";
  debugPrintType( "qcf-match", d_type );
  Debug("qcf-match") << ", children = " << d_children.size() << ", binding = " << d_binding << std::endl;
  if( d_type==typ_invalid || d_type==typ_ground ){
    if( d_child_counter==0 ){
      d_child_counter = -1;
      return true;
    }else{
      return false;
    }
  }else if( d_type==typ_var || d_type==typ_eq || d_type==typ_pred ){
    bool success = false;
    bool terminate = false;
    do {
      bool doReset = false;
      bool doFail = false;
      if( !d_binding ){
        if( doMatching( p, qi ) ){
          Debug("qcf-match-debug") << "     - Matching succeeded" << std::endl;
          d_binding = true;
          d_binding_it = d_qni_bound.begin();
          doReset = true;
        }else{
          Debug("qcf-match-debug") << "     - Matching failed" << std::endl;
          success = false;
          terminate = true;
        }
      }else{
        doFail = true;
      }
      if( d_binding ){
        //also need to create match for each variable we bound
        success = true;
        Debug("qcf-match-debug") << "     Produce matches for bound variables by " << d_n << ", type = ";
        debugPrintType( "qcf-match-debug", d_type );
        Debug("qcf-match-debug") << "..." << std::endl;

        while( ( success && d_binding_it!=d_qni_bound.end() ) || doFail ){
          std::map< int, MatchGen * >::iterator itm;
          if( !doFail ){
            Debug("qcf-match-debug") << "       check variable " << d_binding_it->second << std::endl;
            itm = qi->d_var_mg.find( d_binding_it->second );
          }
          if( doFail || ( d_binding_it->first!=0 && itm!=qi->d_var_mg.end() ) ){
            Debug("qcf-match-debug") << "       we had bound variable " << d_binding_it->second << ", reset = " << doReset << std::endl;
            if( doReset ){
              itm->second->reset( p, true, qi );
            }
            if( doFail || !itm->second->getNextMatch( p, qi ) ){
              do {
                if( d_binding_it==d_qni_bound.begin() ){
                  Debug("qcf-match-debug") << "       failed." << std::endl;
                  success = false;
                }else{
                  Debug("qcf-match-debug") << "       decrement..." << std::endl;
                  --d_binding_it;
                }
              }while( success && ( d_binding_it->first==0 || qi->d_var_mg.find( d_binding_it->second )==qi->d_var_mg.end() ) );
              doReset = false;
              doFail = false;
            }else{
              Debug("qcf-match-debug") << "       increment..." << std::endl;
              ++d_binding_it;
              doReset = true;
            }
          }else{
            Debug("qcf-match-debug") << "       skip..." << d_binding_it->second << std::endl;
            ++d_binding_it;
            doReset = true;
          }
        }
        if( !success ){
          d_binding = false;
        }else{
          terminate = true;
          if( d_binding_it==d_qni_bound.begin() ){
            d_binding = false;
          }
        }
      }
    }while( !terminate );
    //if not successful, clean up the variables you bound
    if( !success ){
      if( d_type==typ_eq || d_type==typ_pred ){
        //clean up the constraints you added
        for( std::map< int, TNode >::iterator it = d_qni_bound_cons.begin(); it != d_qni_bound_cons.end(); ++it ){
          if( !it->second.isNull() ){
            Debug("qcf-match") << "       Clean up bound var " << it->first << (d_tgt ? "!" : "") << " = " << it->second << std::endl;
            std::map< int, int >::iterator itb = d_qni_bound_cons_var.find( it->first );
            int vn = itb!=d_qni_bound_cons_var.end() ? itb->second : -1;
            qi->addConstraint( p, it->first, it->second, vn, d_tgt, true );
          }
        }
        d_qni_bound_cons.clear();
        d_qni_bound_cons_var.clear();
        d_qni_bound.clear();
      }else{
        //clean up the matches you set
        for( std::map< int, int >::iterator it = d_qni_bound.begin(); it != d_qni_bound.end(); ++it ){
          Debug("qcf-match") << "       Clean up bound var " << it->second << std::endl;
          Assert( it->second<qi->getNumVars() );
          qi->d_match[ it->second ] = TNode::null();
          qi->d_match_term[ it->second ] = TNode::null();
        }
        d_qni_bound.clear();
      }
      /*
      if( d_type==typ_var && p->d_effort==QuantConflictFind::effort_mc && !d_matched_basis ){
        d_matched_basis = true;
        Node f = getOperator( d_n );
        TNode mbo = p->getQuantifiersEngine()->getTermDatabase()->getModelBasisOpTerm( f );
        if( qi->setMatch( p, d_qni_var_num[0], mbo ) ){
          success = true;
          d_qni_bound[0] = d_qni_var_num[0];
        }
      }
      */
    }
    Debug("qcf-match") << "    ...finished matching for " << d_n << ", success = " << success << std::endl;
    return success;
  }else if( d_type==typ_formula || d_type==typ_ite_var ){
    bool success = false;
    if( d_child_counter<0 ){
      if( d_child_counter<-1 ){
        success = true;
        d_child_counter = -1;
      }
    }else{
      while( !success && d_child_counter>=0 ){
        //transition system based on d_child_counter
        if( d_type==typ_top || d_n.getKind()==OR || d_n.getKind()==AND ){
          if( (d_n.getKind()==AND)==d_tgt ){
            //all children must match simultaneously
            if( getChild( d_child_counter )->getNextMatch( p, qi ) ){
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Debug("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << std::endl;
                getChild( d_child_counter )->reset( p, d_tgt, qi );
              }else{
                success = true;
              }
            }else{
              //if( std::find( d_independent.begin(), d_independent.end(), d_child_counter )!=d_independent.end() ){
              //  d_child_counter--;
              //}else{
              d_child_counter--;
              //}
            }
          }else{
            //one child must match
            if( !getChild( d_child_counter )->getNextMatch( p, qi ) ){
              if( d_child_counter<(int)(getNumChildren()-1) ){
                d_child_counter++;
                Debug("qcf-match-debug") << "       Reset child " << d_child_counter << " of " << d_n << ", one match" << std::endl;
                getChild( d_child_counter )->reset( p, d_tgt, qi );
              }else{
                d_child_counter = -1;
              }
            }else{
              success = true;
            }
          }
        }else if( d_n.getKind()==IFF ){
          //construct match based on both children
          if( d_child_counter%2==0 ){
            if( getChild( 0 )->getNextMatch( p, qi ) ){
              d_child_counter++;
              getChild( 1 )->reset( p, d_child_counter==1, qi );
            }else{
              if( d_child_counter==0 ){
                d_child_counter = 2;
                getChild( 0 )->reset( p, !d_tgt, qi );
              }else{
                d_child_counter = -1;
              }
            }
          }
          if( d_child_counter>=0 && d_child_counter%2==1 ){
            if( getChild( 1 )->getNextMatch( p, qi ) ){
              success = true;
            }else{
              d_child_counter--;
            }
          }
        }else if( d_n.getKind()==ITE ){
          if( d_child_counter%2==0 ){
            int index1 = d_child_counter==4 ? 1 : 0;
            if( getChild( index1 )->getNextMatch( p, qi ) ){
              d_child_counter++;
              getChild( d_child_counter==5 ? 2 : (d_tgt==(d_child_counter==1) ? 1 : 2) )->reset( p, d_tgt, qi );
            }else{
              if( d_child_counter==4 || ( d_type==typ_ite_var && d_child_counter==2 ) ){
                d_child_counter = -1;
              }else{
                d_child_counter +=2;
                getChild( d_child_counter==2 ? 0 : 1 )->reset( p, d_child_counter==2 ? !d_tgt : d_tgt, qi );
              }
            }
          }
          if( d_child_counter>=0 && d_child_counter%2==1 ){
            int index2 = d_child_counter==5 ? 2 : (d_tgt==(d_child_counter==1) ? 1 : 2);
            if( getChild( index2 )->getNextMatch( p, qi ) ){
              success = true;
            }else{
              d_child_counter--;
            }
          }
        }else if( d_n.getKind()==FORALL ){
          if( getChild( d_child_counter )->getNextMatch( p, qi ) ){
            success = true;
          }else{
            d_child_counter = -1;
          }
        }
      }
      Debug("qcf-match") << "    ...finished construct match for " << d_n << ", success = " << success << std::endl;
      return success;
    }
  }
  Debug("qcf-match") << "    ...already finished for " << d_n << std::endl;
  return false;
}

bool MatchGen::doMatching( QuantConflictFind * p, QuantInfo * qi ) {
  if( !d_qn.empty() ){
    if( d_qn[0]==NULL ){
      d_qn.clear();
      return true;
    }else{
      Assert( d_type==typ_var );
      Assert( d_qni_size>0 );
      bool invalidMatch;
      do {
        invalidMatch = false;
        Debug("qcf-match-debug") << "       Do matching " << d_n << " " << d_qn.size() << " " << d_qni.size() << std::endl;
        if( d_qn.size()==d_qni.size()+1 ) {
          int index = (int)d_qni.size();
          //initialize
          TNode val;
          std::map< int, int >::iterator itv = d_qni_var_num.find( index );
          if( itv!=d_qni_var_num.end() ){
            //get the representative variable this variable is equal to
            int repVar = qi->getCurrentRepVar( itv->second );
            Debug("qcf-match-debug") << "       Match " << index << " is a variable " << itv->second << ", which is repVar " << repVar << std::endl;
            //get the value the rep variable
            //std::map< int, TNode >::iterator itm = qi->d_match.find( repVar );
            if( !qi->d_match[repVar].isNull() ){
              val = qi->d_match[repVar];
              Debug("qcf-match-debug") << "       Variable is already bound to " << val << std::endl;
            }else{
              //binding a variable
              d_qni_bound[index] = repVar;
              std::map< TNode, QcfNodeIndex >::iterator it = d_qn[index]->d_children.begin();
              if( it != d_qn[index]->d_children.end() ) {
                d_qni.push_back( it );
                //set the match
                if( qi->setMatch( p, d_qni_bound[index], it->first ) ){
                  Debug("qcf-match-debug") << "       Binding variable" << std::endl;
                  if( d_qn.size()<d_qni_size ){
                    d_qn.push_back( &it->second );
                  }
                }else{
                  Debug("qcf-match") << "       Binding variable, currently fail." << std::endl;
                  invalidMatch = true;
                }
              }else{
                Debug("qcf-match-debug") << "       Binding variable, fail, no more variables to bind" << std::endl;
                d_qn.pop_back();
              }
            }
          }else{
            Debug("qcf-match-debug") << "       Match " << index << " is ground term" << std::endl;
            Assert( d_qni_gterm.find( index )!=d_qni_gterm.end() );
            Assert( d_qni_gterm_rep.find( index )!=d_qni_gterm_rep.end() );
            val = d_qni_gterm_rep[index];
            Assert( !val.isNull() );
          }
          if( !val.isNull() ){
            //constrained by val
            std::map< TNode, QcfNodeIndex >::iterator it = d_qn[index]->d_children.find( val );
            if( it!=d_qn[index]->d_children.end() ){
              Debug("qcf-match-debug") << "       Match" << std::endl;
              d_qni.push_back( it );
              if( d_qn.size()<d_qni_size ){
                d_qn.push_back( &it->second );
              }
            }else{
              Debug("qcf-match-debug") << "       Failed to match" << std::endl;
              d_qn.pop_back();
            }
          }
        }else{
          Assert( d_qn.size()==d_qni.size() );
          int index = d_qni.size()-1;
          //increment if binding this variable
          bool success = false;
          std::map< int, int >::iterator itb = d_qni_bound.find( index );
          if( itb!=d_qni_bound.end() ){
            d_qni[index]++;
            if( d_qni[index]!=d_qn[index]->d_children.end() ){
              success = true;
              if( qi->setMatch( p, itb->second, d_qni[index]->first ) ){
                Debug("qcf-match-debug") << "       Bind next variable" << std::endl;
                if( d_qn.size()<d_qni_size ){
                  d_qn.push_back( &d_qni[index]->second );
                }
              }else{
                Debug("qcf-match-debug") << "       Bind next variable, currently fail" << std::endl;
                invalidMatch = true;
              }
            }else{
              Debug("qcf-match-debug") << "       Bind next variable, no more variables to bind" << std::endl;
            }
          }else{
            //TODO : if it equal to something else, also try that
          }
          //if not incrementing, move to next
          if( !success ){
            d_qn.pop_back();
            d_qni.pop_back();
          }
        }
      }while( ( !d_qn.empty() && d_qni.size()!=d_qni_size ) || invalidMatch );
      if( d_qni.size()==d_qni_size ){
        //Assert( !d_qni[d_qni.size()-1]->second.d_children.empty() );
        //Debug("qcf-match-debug") << "       We matched " << d_qni[d_qni.size()-1]->second.d_children.begin()->first << std::endl;
        Assert( !d_qni[d_qni.size()-1]->second.d_children.empty() );
        TNode t = d_qni[d_qni.size()-1]->second.d_children.begin()->first;
        Debug("qcf-match-debug") << "       " << d_n << " matched " << t << std::endl;
        //set the match terms
        for( std::map< int, int >::iterator it = d_qni_bound.begin(); it != d_qni_bound.end(); ++it ){
          Debug("qcf-match-debug") << "       position " << it->first << " bounded " << it->second << " / " << qi->d_q[0].getNumChildren() << std::endl;
          if( it->second<(int)qi->d_q[0].getNumChildren() && it->first>0 ){   //if it is an actual variable, we are interested in knowing the actual term
            Assert( !qi->d_match[ it->second ].isNull() );
            Assert( p->areEqual( t[it->first-1], qi->d_match[ it->second ] ) );
            qi->d_match_term[it->second] = t[it->first-1];
          }
        }
      }
    }
  }
  return !d_qn.empty();
}

void MatchGen::debugPrintType( const char * c, short typ, bool isTrace ) {
  if( isTrace ){
    switch( typ ){
    case typ_invalid: Trace(c) << "invalid";break;
    case typ_ground: Trace(c) << "ground";break;
    case typ_eq: Trace(c) << "eq";break;
    case typ_pred: Trace(c) << "pred";break;
    case typ_formula: Trace(c) << "formula";break;
    case typ_var: Trace(c) << "var";break;
    case typ_ite_var: Trace(c) << "ite_var";break;
    case typ_top: Trace(c) << "top";break;
    }
  }else{
    switch( typ ){
    case typ_invalid: Debug(c) << "invalid";break;
    case typ_ground: Debug(c) << "ground";break;
    case typ_eq: Debug(c) << "eq";break;
    case typ_pred: Debug(c) << "pred";break;
    case typ_formula: Debug(c) << "formula";break;
    case typ_var: Debug(c) << "var";break;
    case typ_ite_var: Debug(c) << "ite_var";break;
    case typ_top: Debug(c) << "top";break;
    }
  }
}

void MatchGen::setInvalid() {
  d_type = typ_invalid;
  d_children.clear();
}

bool MatchGen::isHandledUfTerm( TNode n ) {
  return n.getKind()==APPLY_UF;// || n.getKind()==GEQ;
}

Node MatchGen::getOperator( QuantConflictFind * p, Node n ) {
  if( isHandledUfTerm( n ) ){
    return n.getOperator();
  }else{
    return Node::null();
  }
}


QuantConflictFind::QuantConflictFind( QuantifiersEngine * qe, context::Context* c ) :
QuantifiersModule( qe ),
d_c( c ),
d_conflict( c, false ),
d_qassert( c ) {
  d_fid_count = 0;
  d_true = NodeManager::currentNM()->mkConst<bool>(true);
  d_false = NodeManager::currentNM()->mkConst<bool>(false);
}

Node QuantConflictFind::mkEqNode( Node a, Node b ) {
  if( a.getType().isBoolean() ){
    return a.iffNode( b );
  }else{
    return a.eqNode( b );
  }
}

//-------------------------------------------------- registration

void QuantConflictFind::registerQuantifier( Node q ) {
  d_quants.push_back( q );
  d_quant_id[q] = d_quants.size();
  Trace("qcf-qregister") << "Register ";
  debugPrintQuant( "qcf-qregister", q );
  Trace("qcf-qregister") << " : " << q << std::endl;
  //make QcfNode structure
  Trace("qcf-qregister") << "- Get relevant equality/disequality pairs, calculate flattening..." << std::endl;
  d_qinfo[q].initialize( q, q[1] );

  //debug print
  Trace("qcf-qregister") << "- Flattened structure is :" << std::endl;
  Trace("qcf-qregister") << "    ";
  debugPrintQuantBody( "qcf-qregister", q, q[1] );
  Trace("qcf-qregister") << std::endl;
  if( d_qinfo[q].d_vars.size()>q[0].getNumChildren() ){
    Trace("qcf-qregister") << "  with additional constraints : " << std::endl;
    for( unsigned j=q[0].getNumChildren(); j<d_qinfo[q].d_vars.size(); j++ ){
      Trace("qcf-qregister") << "    ?x" << j << " = ";
      debugPrintQuantBody( "qcf-qregister", q, d_qinfo[q].d_vars[j], false );
      Trace("qcf-qregister") << std::endl;
    }
  }

  Trace("qcf-qregister") << "Done registering quantifier." << std::endl;
}

int QuantConflictFind::evaluate( Node n, bool pref, bool hasPref ) {
  int ret = 0;
  if( n.getKind()==EQUAL ){
    Node n1 = evaluateTerm( n[0] );
    Node n2 = evaluateTerm( n[1] );
    Debug("qcf-eval") << "Evaluate : Normalize " << n << " to " << n1 << " = " << n2 << std::endl;
    if( areEqual( n1, n2 ) ){
      ret = 1;
    }else if( areDisequal( n1, n2 ) ){
      ret = -1;
    }
    //else if( d_effort>QuantConflictFind::effort_conflict ){
    //  ret = -1;
    //}
  }else if( MatchGen::isHandledUfTerm( n ) ){  //predicate
    Node nn = evaluateTerm( n );
    Debug("qcf-eval") << "Evaluate : Normalize " << nn << " to " << n << std::endl;
    if( areEqual( nn, d_true ) ){
      ret = 1;
    }else if( areEqual( nn, d_false ) ){
      ret = -1;
    }
    //else if( d_effort>QuantConflictFind::effort_conflict ){
    //  ret = -1;
    //}
  }else if( n.getKind()==NOT ){
    return -evaluate( n[0] );
  }else if( n.getKind()==ITE ){
    int cev1 = evaluate( n[0] );
    int cevc[2] = { 0, 0 };
    for( unsigned i=0; i<2; i++ ){
      if( ( i==0 && cev1!=-1 ) || ( i==1 && cev1!=1 ) ){
        cevc[i] = evaluate( n[i+1] );
        if( cev1!=0 ){
          ret = cevc[i];
          break;
        }else if( cevc[i]==0 ){
          break;
        }
      }
    }
    if( ret==0 && cevc[0]!=0 && cevc[0]==cevc[1] ){
      ret = cevc[0];
    }
  }else if( n.getKind()==IFF ){
    int cev1 = evaluate( n[0] );
    if( cev1!=0 ){
      int cev2 = evaluate( n[1] );
      if( cev2!=0 ){
        ret = cev1==cev2 ? 1 : -1;
      }
    }

  }else{
    int ssval = 0;
    if( n.getKind()==OR ){
      ssval = 1;
    }else if( n.getKind()==AND ){
      ssval = -1;
    }
    bool isUnk = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int cev = evaluate( n[i] );
      if( cev==ssval ){
        ret = ssval;
        break;
      }else if( cev==0 ){
        isUnk = true;
      }
    }
    if( ret==0 && !isUnk ){
      ret = -ssval;
    }
  }
  Debug("qcf-eval") << "Evaluate " << n << " to " << ret << std::endl;
  return ret;
}

bool QuantConflictFind::areMatchEqual( TNode n1, TNode n2 ) {
  //if( d_effort==QuantConflictFind::effort_mc ){
  //  return n1==n2 || !areDisequal( n1, n2 );
  //}else{
  return n1==n2;
  //}
}

bool QuantConflictFind::areMatchDisequal( TNode n1, TNode n2 ) {
  //if( d_effort==QuantConflictFind::effort_conflict ){
  //  return areDisequal( n1, n2 );
  //}else{
  return n1!=n2;
  //}
}

//-------------------------------------------------- handling assertions / eqc

void QuantConflictFind::assertNode( Node q ) {
  Trace("qcf-proc") << "QCF : assertQuantifier : ";
  debugPrintQuant("qcf-proc", q);
  Trace("qcf-proc") << std::endl;
  d_qassert.push_back( q );
  //set the eqRegistries that this depends on to true
  //for( std::map< EqRegistry *, bool >::iterator it = d_qinfo[q].d_rel_eqr.begin(); it != d_qinfo[q].d_rel_eqr.end(); ++it ){
  //  it->first->d_active.set( true );
  //}
}

eq::EqualityEngine * QuantConflictFind::getEqualityEngine() {
  //return ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( theory::THEORY_UF ))->getEqualityEngine();
  return d_quantEngine->getTheoryEngine()->getMasterEqualityEngine();
}
bool QuantConflictFind::areEqual( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areEqual( n1,n2 );
}
bool QuantConflictFind::areDisequal( Node n1, Node n2 ) {
  return getEqualityEngine()->hasTerm( n1 ) && getEqualityEngine()->hasTerm( n2 ) && getEqualityEngine()->areDisequal( n1,n2, false );
}
Node QuantConflictFind::getRepresentative( Node n ) {
  if( getEqualityEngine()->hasTerm( n ) ){
    return getEqualityEngine()->getRepresentative( n );
  }else{
    return n;
  }
}
Node QuantConflictFind::evaluateTerm( Node n ) {
  if( MatchGen::isHandledUfTerm( n ) ){
    Node f = MatchGen::getOperator( this, n );
    Node nn;
    computeUfTerms( f );
    if( getEqualityEngine()->hasTerm( n ) ){
      computeArgReps( n );
      nn = d_uf_terms[f].existsTerm( n, d_arg_reps[n] );
    }else{
      std::vector< TNode > args;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node c = evaluateTerm( n[i] );
        args.push_back( c );
      }
      nn = d_uf_terms[f].existsTerm( n, args );
    }
    if( !nn.isNull() ){
      Debug("qcf-eval") << "GT: Term " << nn << " for " << n << " hasTerm = " << getEqualityEngine()->hasTerm( n )  << std::endl;
      return getRepresentative( nn );
    }else{
      Debug("qcf-eval") << "GT: No term for " << n << " hasTerm = " << getEqualityEngine()->hasTerm( n )  << std::endl;
      return n;
    }
  }else if( n.getKind()==ITE ){
    int v = evaluate( n[0], false, false );
    if( v==1 ){
      return evaluateTerm( n[1] );
    }else if( v==-1 ){
      return evaluateTerm( n[2] );
    }
  }
  return getRepresentative( n );
}

/*
QuantConflictFind::EqcInfo * QuantConflictFind::getEqcInfo( Node n, bool doCreate ) {
  std::map< Node, EqcInfo * >::iterator it2 = d_eqc_info.find( n );
  if( it2==d_eqc_info.end() ){
    if( doCreate ){
      EqcInfo * eqci = new EqcInfo( d_c );
      d_eqc_info[n] = eqci;
      return eqci;
    }else{
      return NULL;
    }
  }
  return it2->second;
}
*/

QcfNodeIndex * QuantConflictFind::getQcfNodeIndex( Node eqc, Node f ) {
  computeUfTerms( f );
  std::map< TNode, QcfNodeIndex >::iterator itut = d_eqc_uf_terms.find( f );
  if( itut==d_eqc_uf_terms.end() ){
    return NULL;
  }else{
    if( eqc.isNull() ){
      return &itut->second;
    }else{
      std::map< TNode, QcfNodeIndex >::iterator itute = itut->second.d_children.find( eqc );
      if( itute!=itut->second.d_children.end() ){
        return &itute->second;
      }else{
        return NULL;
      }
    }
  }
}

QcfNodeIndex * QuantConflictFind::getQcfNodeIndex( Node f ) {
  computeUfTerms( f );
  std::map< TNode, QcfNodeIndex >::iterator itut = d_uf_terms.find( f );
  if( itut!=d_uf_terms.end() ){
    return &itut->second;
  }else{
    return NULL;
  }
}

/** new node */
void QuantConflictFind::newEqClass( Node n ) {
  //Trace("qcf-proc-debug") << "QCF : newEqClass : " << n << std::endl;
  //Trace("qcf-proc2-debug") << "QCF : finished newEqClass : " << n << std::endl;
}

/** merge */
void QuantConflictFind::merge( Node a, Node b ) {
  /*
  if( b.getKind()==EQUAL ){
    if( a==d_true ){
      //will merge anyways
      //merge( b[0], b[1] );
    }else if( a==d_false ){
      assertDisequal( b[0], b[1] );
    }
  }else{
    Trace("qcf-proc") << "QCF : merge : " << a << " " << b << std::endl;
    EqcInfo * eqc_b = getEqcInfo( b, false );
    EqcInfo * eqc_a = NULL;
    if( eqc_b ){
      eqc_a = getEqcInfo( a );
      //move disequalities of b into a
      for( NodeBoolMap::iterator it = eqc_b->d_diseq.begin(); it != eqc_b->d_diseq.end(); ++it ){
        if( (*it).second ){
          Node n = (*it).first;
          EqcInfo * eqc_n = getEqcInfo( n, false );
          Assert( eqc_n );
          if( !eqc_n->isDisequal( a ) ){
            Assert( !eqc_a->isDisequal( n ) );
            eqc_n->setDisequal( a );
            eqc_a->setDisequal( n );
            //setEqual( eqc_a, eqc_b, a, n, false );
          }
          eqc_n->setDisequal( b, false );
        }
      }
      ////move all previous EqcRegistry's regarding equalities within b
      //for( NodeBoolMap::iterator it = eqc_b->d_rel_eqr_e.begin(); it != eqc_b->d_rel_eqr_e.end(); ++it ){
      //  if( (*it).second ){
      //    eqc_a->d_rel_eqr_e[(*it).first] = true;
      //  }
      //}
    }
    //process new equalities
    //setEqual( eqc_a, eqc_b, a, b, true );
    Trace("qcf-proc2") << "QCF : finished merge : " << a << " " << b << std::endl;
  }
  */
}

/** assert disequal */
void QuantConflictFind::assertDisequal( Node a, Node b ) {
  /*
  a = getRepresentative( a );
  b = getRepresentative( b );
  Trace("qcf-proc") << "QCF : assert disequal : " << a << " " << b << std::endl;
  EqcInfo * eqc_a = getEqcInfo( a );
  EqcInfo * eqc_b = getEqcInfo( b );
  if( !eqc_a->isDisequal( b ) ){
    Assert( !eqc_b->isDisequal( a ) );
    eqc_b->setDisequal( a );
    eqc_a->setDisequal( b );
    //setEqual( eqc_a, eqc_b, a, b, false );
  }
  Trace("qcf-proc2") << "QCF : finished assert disequal : " << a << " " << b << std::endl;
  */
}

//-------------------------------------------------- check function

/** check */
void QuantConflictFind::check( Theory::Effort level ) {
  Trace("qcf-check") << "QCF : check : " << level << std::endl;
  if( d_conflict ){
    Trace("qcf-check2") << "QCF : finished check : already in conflict." << std::endl;
    if( level>=Theory::EFFORT_FULL ){
      Trace("qcf-warn") << "ALREADY IN CONFLICT? " << level << std::endl;
      //Assert( false );
    }
  }else{
    int addedLemmas = 0;
    if( d_performCheck ){
      ++(d_statistics.d_inst_rounds);
      double clSet = 0;
      if( Trace.isOn("qcf-engine") ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Trace("qcf-engine") << "---Conflict Find Engine Round, effort = " << level << "---" << std::endl;
      }
      Trace("qcf-check") << "Compute relevant equalities..." << std::endl;
      computeRelevantEqr();

      //determine order for quantified formulas
      std::vector< Node > qorder;
      std::map< Node, bool > qassert;
      //mark which are asserted
      for( unsigned i=0; i<d_qassert.size(); i++ ){
        qassert[d_qassert[i]] = true;
      }
      //add which ones are specified in the order
      for( unsigned i=0; i<d_quant_order.size(); i++ ){
        Node n = d_quant_order[i];
        if( std::find( qorder.begin(), qorder.end(), n )==qorder.end() && qassert.find( n )!=qassert.end() ){
          qorder.push_back( n );
        }
      }
      d_quant_order.clear();
      d_quant_order.insert( d_quant_order.begin(), qorder.begin(), qorder.end() );
      //add remaining
      for( unsigned i=0; i<d_qassert.size(); i++ ){
        Node n = d_qassert[i];
        if( std::find( qorder.begin(), qorder.end(), n )==qorder.end() ){
          qorder.push_back( n );
        }
      }



      if( Trace.isOn("qcf-debug") ){
        Trace("qcf-debug") << std::endl;
        debugPrint("qcf-debug");
        Trace("qcf-debug") << std::endl;
      }
      short end_e;
      if( options::qcfMode()==QCF_CONFLICT_ONLY ){
        end_e = effort_conflict;
      }else if( options::qcfMode()==QCF_PROP_EQ ){
        end_e = effort_prop_eq;
      }else if( options::qcfMode()==QCF_PARTIAL ){
        end_e = effort_partial;
      }else{
        end_e = effort_mc;
      }
      for( short e = effort_conflict; e<=end_e; e++ ){
        d_effort = e;
        Trace("qcf-check") << "Checking quantified formulas at effort " << e << "..." << std::endl;
        for( unsigned j=0; j<qorder.size(); j++ ){
          Node q = qorder[j];
          QuantInfo * qi = &d_qinfo[q];

          Assert( d_qinfo.find( q )!=d_qinfo.end() );
          if( qi->d_mg->isValid() ){
            if( qi->isPartial()==(e==effort_partial) ){
              Trace("qcf-check") << "Check quantified formula ";
              debugPrintQuant("qcf-check", q);
              Trace("qcf-check") << " : " << q << "..." << std::endl;

              Trace("qcf-check-debug") << "Reset round..." << std::endl;
              qi->reset_round( this );
              //try to make a matches making the body false
              Trace("qcf-check-debug") << "Reset..." << std::endl;
              qi->d_mg->reset( this, false, qi );
              Trace("qcf-check-debug") << "Get next match..." << std::endl;
              while( qi->d_mg->getNextMatch( this, qi ) ){

                Trace("qcf-check") << "*** Produced match at effort " << e << " : " << std::endl;
                qi->debugPrintMatch("qcf-check");
                Trace("qcf-check") << std::endl;

                if( !qi->isMatchSpurious( this ) ){
                  std::vector< int > assigned;
                  if( qi->completeMatch( this, assigned ) ){
                    std::vector< Node > terms;
                    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
                      //Node cv = qi->getCurrentValue( qi->d_match[i] );
                      int repVar = qi->getCurrentRepVar( i );
                      Node cv;
                      //std::map< int, TNode >::iterator itmt = qi->d_match_term.find( repVar );
                      if( !qi->d_match_term[repVar].isNull() ){
                        cv = qi->d_match_term[repVar];
                      }else{
                        cv = qi->d_match[repVar];
                      }
                      Debug("qcf-check-inst") << "INST : " << i << " -> " << cv << ", from " << qi->d_match[i] << std::endl;
                      terms.push_back( cv );
                    }
                    if( Debug.isOn("qcf-check-inst") ){
                      //if( e==effort_conflict ){
                      Node inst = d_quantEngine->getInstantiation( q, terms );
                      Debug("qcf-check-inst") << "Check instantiation " << inst << "..." << std::endl;
                      Assert( evaluate( inst )!=1 );
                      Assert( evaluate( inst )==-1 || e>effort_conflict );
                      //}
                    }
                    if( d_quantEngine->addInstantiation( q, terms ) ){
                      Trace("qcf-check") << "   ... Added instantiation" << std::endl;
                      ++addedLemmas;
                      if( e==effort_conflict ){
                        d_quant_order.insert( d_quant_order.begin(), q );
                        d_conflict.set( true );
                        ++(d_statistics.d_conflict_inst);
                        break;
                      }else if( e==effort_prop_eq ){
                        ++(d_statistics.d_prop_inst);
                      }else if( e==effort_partial ){
                        ++(d_statistics.d_partial_inst);
                      }
                    }else{
                      Trace("qcf-check") << "   ... Failed to add instantiation" << std::endl;
                      //Assert( false );
                    }
                    //clean up assigned
                    for( unsigned i=0; i<assigned.size(); i++ ){
                      qi->d_match[ assigned[i] ] = TNode::null();
                    }
                  }else{
                    Trace("qcf-check") << "   ... Spurious instantiation (cannot assign unassigned variables)" << std::endl;
                  }
                }else{
                  Trace("qcf-check") << "   ... Spurious instantiation (does not meet variable constraints)" << std::endl;
                }
              }
              if( d_conflict ){
                break;
              }
            }
          }
        }
        if( addedLemmas>0 ){
          d_quantEngine->flushLemmas();
          break;
        }
      }
      if( Trace.isOn("qcf-engine") ){
        double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
        Trace("qcf-engine") << "Finished conflict find engine, time = " << (clSet2-clSet);
        if( addedLemmas>0 ){
          Trace("qcf-engine") << ", effort = " << ( d_effort==effort_conflict ? "conflict" : ( d_effort==effort_prop_eq ? "prop_eq" : (d_effort==effort_partial ? "partial" : "mc" ) ) );
          Trace("qcf-engine") << ", addedLemmas = " << addedLemmas;
        }
        Trace("qcf-engine") << std::endl;
      }
    }
    Trace("qcf-check2") << "QCF : finished check : " << level << std::endl;
  }
}

bool QuantConflictFind::needsCheck( Theory::Effort level ) {
  d_performCheck = false;
  if( !d_conflict ){
    if( level==Theory::EFFORT_LAST_CALL ){
      d_performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_LAST_CALL;
    }else if( level==Theory::EFFORT_FULL ){
      d_performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_DEFAULT;
    }else if( level==Theory::EFFORT_STANDARD ){
      d_performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_STD;
    }
  }
  return d_performCheck;
}

void QuantConflictFind::computeRelevantEqr() {
  d_uf_terms.clear();
  d_eqc_uf_terms.clear();
  d_eqcs.clear();
  d_model_basis.clear();
  d_arg_reps.clear();
  //double clSet = 0;
  //if( Trace.isOn("qcf-opt") ){
  //  clSet = double(clock())/double(CLOCKS_PER_SEC);
  //}

  //long nTermst = 0;
  //long nTerms = 0;
  //long nEqc = 0;

  //which nodes are irrelevant for disequality matches
  std::map< TNode, bool > irrelevant_dnode;
  //now, store matches
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( getEqualityEngine() );
  while( !eqcs_i.isFinished() ){
    //nEqc++;
    Node r = (*eqcs_i);
    TypeNode rtn = r.getType();
    if( options::qcfMode()==QCF_MC ){
      std::map< TypeNode, std::vector< TNode > >::iterator itt = d_eqcs.find( rtn );
      if( itt==d_eqcs.end() ){
        Node mb = getQuantifiersEngine()->getTermDatabase()->getModelBasisTerm( rtn );
        if( !getEqualityEngine()->hasTerm( mb ) ){
          Trace("qcf-warn") << "WARNING: Model basis term does not exist!" << std::endl;
          Assert( false );
        }
        Node mbr = getRepresentative( mb );
        if( mbr!=r ){
          d_eqcs[rtn].push_back( mbr );
        }
        d_eqcs[rtn].push_back( r );
        d_model_basis[rtn] = mb;
      }else{
        itt->second.push_back( r );
      }
    }else{
      d_eqcs[rtn].push_back( r );
    }
    eq::EqClassIterator eqc_i = eq::EqClassIterator( r, getEqualityEngine() );
    while( !eqc_i.isFinished() ){
      TNode n = (*eqc_i);
      if( quantifiers::TermDb::hasBoundVarAttr( n ) ){
        std::cout << "BAD TERM IN DB : " << n << std::endl;
        exit( 199 );
      }
      ++eqc_i;
    }

    //if( r.getType().isInteger() ){
    //  Trace("qcf-mv") << "Model value for eqc(" << r << ") : " << d_quantEngine->getValuation().getModelValue( r ) << std::endl;
    //}
    //EqcInfo * eqcir = getEqcInfo( r, false );
    //get relevant nodes that we are disequal from
    /*
    std::vector< Node > deqc;
    if( eqcir ){
      for( NodeBoolMap::iterator it = eqcir->d_diseq.begin(); it != eqcir->d_diseq.end(); ++it ){
        if( (*it).second ){
          //Node rd = (*it).first;
          //if( rd!=getRepresentative( rd ) ){
          //  std::cout << "Bad rep!" << std::endl;
          //  exit( 0 );
          //}
          deqc.push_back( (*it).first );
        }
      }
    }
    */
    //process disequalities
    /*
    eq::EqClassIterator eqc_i = eq::EqClassIterator( r, getEqualityEngine() );
    while( !eqc_i.isFinished() ){
      TNode n = (*eqc_i);
      if( n.getKind()!=EQUAL ){
        nTermst++;
        //node_to_rep[n] = r;
        //if( n.getNumChildren()>0 ){
        //  if( n.getKind()!=APPLY_UF ){
        //    std::cout << n.getKind() << " " << n.getOperator() << " " << n << std::endl;
        //  }
        //}
        if( !quantifiers::TermDb::hasBoundVarAttr( n ) ){    //temporary

          bool isRedundant;
          std::map< TNode, std::vector< TNode > >::iterator it_na;
          TNode fn;
          if( MatchGen::isHandledUfTerm( n ) ){
            Node f = MatchGen::getOperator( this, n );
            computeArgReps( n );
            it_na = d_arg_reps.find( n );
            Assert( it_na!=d_arg_reps.end() );
            Node nadd = d_eqc_uf_terms[f].d_children[r].addTerm( n, d_arg_reps[n] );
            isRedundant = (nadd!=n);
            d_uf_terms[f].addTerm( n, d_arg_reps[n] );
          }else{
            isRedundant = false;
          }
          nTerms += isRedundant ? 0 : 1;
        }else{
          if( Debug.isOn("qcf-nground") ){
            Debug("qcf-nground") << "Non-ground term in eqc : " << n << std::endl;
            Assert( false );
          }
        }
      }
      ++eqc_i;
    }
    */
    ++eqcs_i;
  }
  /*
  if( Trace.isOn("qcf-opt") ){
    double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
    Trace("qcf-opt") << "Compute rel eqc : " << std::endl;
    Trace("qcf-opt") << "   " << nEqc << " equivalence classes. " << std::endl;
    Trace("qcf-opt") << "   " << nTerms << " / " << nTermst << " terms." << std::endl;
    Trace("qcf-opt") << "   Time : " << (clSet2-clSet) << std::endl;
  }
  */
}

void QuantConflictFind::computeArgReps( TNode n ) {
  if( d_arg_reps.find( n )==d_arg_reps.end() ){
    Assert( MatchGen::isHandledUfTerm( n ) );
    for( unsigned j=0; j<n.getNumChildren(); j++ ){
      d_arg_reps[n].push_back( getRepresentative( n[j] ) );
    }
  }
}

void QuantConflictFind::computeUfTerms( TNode f ) {
  if( d_uf_terms.find( f )==d_uf_terms.end() ){
    d_uf_terms[f].clear();
    unsigned nt = d_quantEngine->getTermDatabase()->d_op_map[f].size();
    for( unsigned i=0; i<nt; i++ ){
      Node n = d_quantEngine->getTermDatabase()->d_op_map[f][i];
      if( !n.getAttribute(NoMatchAttribute()) ){
        Assert( getEqualityEngine()->hasTerm( n ) );
        Node r = getRepresentative( n );
        computeArgReps( n );
        d_eqc_uf_terms[f].d_children[r].addTerm( n, d_arg_reps[n] );
        d_uf_terms[f].addTerm( n, d_arg_reps[n] );
      }
    }
  }
}

//-------------------------------------------------- debugging


void QuantConflictFind::debugPrint( const char * c ) {
  //print the equivalance classes
  Trace(c) << "----------EQ classes" << std::endl;
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( getEqualityEngine() );
  while( !eqcs_i.isFinished() ){
    Node n = (*eqcs_i);
    //if( !n.getType().isInteger() ){
    Trace(c) << "  - " << n << " : {";
    eq::EqClassIterator eqc_i = eq::EqClassIterator( n, getEqualityEngine() );
    bool pr = false;
    while( !eqc_i.isFinished() ){
      Node nn = (*eqc_i);
      if( nn.getKind()!=EQUAL && nn!=n ){
        Trace(c) << (pr ? "," : "" ) << " " << nn;
        pr = true;
      }
      ++eqc_i;
    }
    Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
    /*
    EqcInfo * eqcn = getEqcInfo( n, false );
    if( eqcn ){
      Trace(c) << "    DEQ : {";
      pr = false;
      for( NodeBoolMap::iterator it = eqcn->d_diseq.begin(); it != eqcn->d_diseq.end(); ++it ){
        if( (*it).second ){
          Trace(c) << (pr ? "," : "" ) << " " << (*it).first;
          pr = true;
        }
      }
      Trace(c) << (pr ? " " : "" ) << "}" << std::endl;
    }
    //}
    */
    ++eqcs_i;
  }
}

void QuantConflictFind::debugPrintQuant( const char * c, Node q ) {
  Trace(c) << "Q" << d_quant_id[q];
}

void QuantConflictFind::debugPrintQuantBody( const char * c, Node q, Node n, bool doVarNum ) {
  if( n.getNumChildren()==0 ){
    Trace(c) << n;
  }else if( doVarNum && d_qinfo[q].d_var_num.find( n )!=d_qinfo[q].d_var_num.end() ){
    Trace(c) << "?x" << d_qinfo[q].d_var_num[n];
  }else{
    Trace(c) << "(";
    if( n.getKind()==APPLY_UF ){
      Trace(c) << n.getOperator();
    }else{
      Trace(c) << n.getKind();
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Trace(c) << " ";
      debugPrintQuantBody( c, q, n[i] );
    }
    Trace(c) << ")";
  }
}

QuantConflictFind::Statistics::Statistics():
  d_inst_rounds("QuantConflictFind::Inst_Rounds", 0),
  d_conflict_inst("QuantConflictFind::Instantiations_Conflict_Find", 0 ),
  d_prop_inst("QuantConflictFind::Instantiations_Prop", 0 ),
  d_partial_inst("QuantConflictFind::Instantiations_Partial", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_conflict_inst);
  StatisticsRegistry::registerStat(&d_prop_inst);
  StatisticsRegistry::registerStat(&d_partial_inst);
}

QuantConflictFind::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_conflict_inst);
  StatisticsRegistry::unregisterStat(&d_prop_inst);
  StatisticsRegistry::unregisterStat(&d_partial_inst);
}

}