/*********************                                                        */
/*! \file quant_conflict_find.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements conflict-based instantiation (Reynolds et al FMCAD 2014)
 **
 **/

#include "theory/quantifiers/quant_conflict_find.h"

#include <vector>

#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantInfo::QuantInfo() : d_unassigned_nvar(0), d_una_index(0), d_mg(nullptr) {}

QuantInfo::~QuantInfo() {
  delete d_mg;
  for(std::map< int, MatchGen * >::iterator i = d_var_mg.begin(),
          iend=d_var_mg.end(); i != iend; ++i) {
    MatchGen* currentMatchGenerator = (*i).second;
    delete currentMatchGenerator;
  }
  d_var_mg.clear();
}


void QuantInfo::initialize( QuantConflictFind * p, Node q, Node qn ) {
  d_q = q;
  d_extra_var.clear();
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_match.push_back( TNode::null() );
    d_match_term.push_back( TNode::null() );
  }

  //register the variables
  for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
    d_var_num[q[0][i]] = i;
    d_vars.push_back( q[0][i] );
    d_var_types.push_back( q[0][i].getType() );
  }

  registerNode( qn, true, true );


  Trace("qcf-qregister") << "- Make match gen structure..." << std::endl;
  d_mg = new MatchGen( this, qn );

  if( d_mg->isValid() ){
    /*
    for( unsigned j=0; j<q[0].getNumChildren(); j++ ){
      if( d_inMatchConstraint.find( q[0][j] )==d_inMatchConstraint.end() ){
        Trace("qcf-invalid") << "QCF invalid : variable " << q[0][j] << " does not exist in a matching constraint." << std::endl;
        d_mg->setInvalid();
        break;
      }
    }
    */
    for( unsigned j=q[0].getNumChildren(); j<d_vars.size(); j++ ){
      if( d_vars[j].getKind()!=BOUND_VARIABLE ){
        d_var_mg[j] = NULL;
        bool is_tsym = false;
        if( !MatchGen::isHandledUfTerm( d_vars[j] ) && d_vars[j].getKind()!=ITE ){
          is_tsym = true;
          d_tsym_vars.push_back( j );
        }
        if( !is_tsym || options::qcfTConstraint() ){
          d_var_mg[j] = new MatchGen( this, d_vars[j], true );
        }
        if( !d_var_mg[j] || !d_var_mg[j]->isValid() ){
          Trace("qcf-invalid") << "QCF invalid : cannot match for " << d_vars[j] << std::endl;
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
  }else{
    Trace("qcf-invalid") << "QCF invalid : body of formula cannot be processed." << std::endl;
  }
  Trace("qcf-qregister-summary") << "QCF register : " << ( d_mg->isValid() ? "VALID " : "INVALID" ) << " : " << q << std::endl;
  
  if( d_mg->isValid() && options::qcfEagerCheckRd() ){
    //optimization : record variable argument positions for terms that must be matched
    std::vector< TNode > vars;
    //TODO: revisit this, makes QCF faster, but misses conflicts due to caring about paths that may not be relevant (starExec jobs 14136/14137)
    if( options::qcfSkipRd() ){
      for( unsigned j=q[0].getNumChildren(); j<d_vars.size(); j++ ){
        vars.push_back( d_vars[j] );
      }
    }else{
      //get all variables that are always relevant
      std::map< TNode, bool > visited;
      getPropagateVars( p, vars, q[1], false, visited );
    }
    for( unsigned j=0; j<vars.size(); j++ ){
      Node v = vars[j];
      TNode f = p->getTermDatabase()->getMatchOperator( v );
      if( !f.isNull() ){
        Trace("qcf-opt") << "Record variable argument positions in " << v << ", op=" << f << "..." << std::endl;
        for( unsigned k=0; k<v.getNumChildren(); k++ ){
          Node n = v[k];
          std::map< TNode, int >::iterator itv = d_var_num.find( n );
          if( itv!=d_var_num.end() ){
            Trace("qcf-opt") << "  arg " << k << " is var #" << itv->second << std::endl;
            if( std::find( d_var_rel_dom[itv->second][f].begin(), d_var_rel_dom[itv->second][f].end(), k )==d_var_rel_dom[itv->second][f].end() ){
              d_var_rel_dom[itv->second][f].push_back( k );
            }
          }
        }
      }
    }    
  }
}

void QuantInfo::getPropagateVars( QuantConflictFind * p, std::vector< TNode >& vars, TNode n, bool pol, std::map< TNode, bool >& visited ){
  std::map< TNode, bool >::iterator itv = visited.find( n );
  if( itv==visited.end() ){
    visited[n] = true;
    bool rec = true;
    bool newPol = pol;
    if( d_var_num.find( n )!=d_var_num.end() ){
      Assert( std::find( vars.begin(), vars.end(), n )==vars.end() );
      vars.push_back( n );
      TNode f = p->getTermDatabase()->getMatchOperator( n );
      if( !f.isNull() ){
        if( std::find( p->d_func_rel_dom[f].begin(), p->d_func_rel_dom[f].end(), d_q )==p->d_func_rel_dom[f].end() ){
          p->d_func_rel_dom[f].push_back( d_q );
        }
      } 
    }else if( MatchGen::isHandledBoolConnective( n ) ){
      Assert( n.getKind()!=IMPLIES );
      QuantPhaseReq::getEntailPolarity( n, 0, true, pol, rec, newPol );
    }
    Trace("qcf-opt-debug") << "getPropagateVars " << n << ", pol = " << pol << ", rec = " << rec << std::endl;
    if( rec ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        getPropagateVars( p, vars, n[i], pol, visited );
      }
    }
  }
}

bool QuantInfo::isBaseMatchComplete() {
  return d_vars_set.size()==(d_q[0].getNumChildren()+d_extra_var.size());
}

void QuantInfo::registerNode( Node n, bool hasPol, bool pol, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Register : " << n << std::endl;
  if( n.getKind()==FORALL ){
    registerNode( n[1], hasPol, pol, true );
  }else{
    if( !MatchGen::isHandledBoolConnective( n ) ){
      if (expr::hasBoundVar(n))
      {
        // literals
        if (n.getKind() == EQUAL)
        {
          for (unsigned i = 0; i < n.getNumChildren(); i++)
          {
            flatten(n[i], beneathQuant);
          }
        }
        else if (MatchGen::isHandledUfTerm(n))
        {
          flatten(n, beneathQuant);
        }
        else if (n.getKind() == ITE)
        {
          for (unsigned i = 1; i <= 2; i++)
          {
            flatten(n[i], beneathQuant);
          }
          registerNode(n[0], false, pol, beneathQuant);
        }
        else if (options::qcfTConstraint())
        {
          // a theory-specific predicate
          for (unsigned i = 0; i < n.getNumChildren(); i++)
          {
            flatten(n[i], beneathQuant);
          }
        }
      }
    }else{
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
}

void QuantInfo::flatten( Node n, bool beneathQuant ) {
  Trace("qcf-qregister-debug2") << "Flatten : " << n << std::endl;
  if (expr::hasBoundVar(n))
  {
    if( n.getKind()==BOUND_VARIABLE ){
      d_inMatchConstraint[n] = true;
    }
    if( d_var_num.find( n )==d_var_num.end() ){
      Trace("qcf-qregister-debug2") << "Add FLATTEN VAR : " << n << std::endl;
      d_var_num[n] = d_vars.size();
      d_vars.push_back( n );
      d_var_types.push_back( n.getType() );
      d_match.push_back( TNode::null() );
      d_match_term.push_back( TNode::null() );
      if( n.getKind()==ITE ){
        registerNode( n, false, false );
      }else if( n.getKind()==BOUND_VARIABLE ){
        d_extra_var.push_back( n );
      }else{
        for( unsigned i=0; i<n.getNumChildren(); i++ ){
          flatten( n[i], beneathQuant );
        }
      }
    }else{
      Trace("qcf-qregister-debug2") << "...already processed" << std::endl;
    }
  }else{
    Trace("qcf-qregister-debug2") << "...is ground." << std::endl;
  }
}


bool QuantInfo::reset_round( QuantConflictFind * p ) {
  for( unsigned i=0; i<d_match.size(); i++ ){
    d_match[i] = TNode::null();
    d_match_term[i] = TNode::null();
  }
  d_vars_set.clear();
  d_curr_var_deq.clear();
  d_tconstraints.clear();
  
  d_mg->reset_round( p );
  for( std::map< int, MatchGen * >::iterator it = d_var_mg.begin(); it != d_var_mg.end(); ++it ){
    if (!it->second->reset_round(p))
    {
      return false;
    }
  }
  //now, reset for matching
  d_mg->reset( p, false, this );
  return true;
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

TNode QuantInfo::getCurrentExpValue( TNode n ) {
  int v = getVarNum( n );
  if( v==-1 ){
    return n;
  }else{
    if( d_match[v].isNull() ){
      return n;
    }else{
      Assert( getVarNum( d_match[v] )!=v );
      if( d_match_term[v].isNull() ){
        return getCurrentValue( d_match[v] );
      }else{
        return d_match_term[v];
      }
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
          //TODO : check for entailed disequal

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
        unsetMatch( p, v );
        return 1;
      }else{
        //std::map< int, TNode >::iterator itm = d_match.find( v );
        bool isGroundRep = false;
        bool isGround = false;
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
            //isGroundRep = true;   ??
            isGround = true;
          }else{
            //compare ground values
            Debug("qcf-match-debug") << "  -> Ground value, compare " << d_match[v] << " "<< n << std::endl;
            return p->areMatchEqual( d_match[v], n ) ? 0 : -1;
          }
        }
        if( setMatch( p, v, n, isGroundRep, isGround ) ){
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

bool QuantInfo::setMatch( QuantConflictFind * p, int v, TNode n, bool isGroundRep, bool isGround ) {
  if( getCurrentCanBeEqual( p, v, n ) ){
    if( isGroundRep ){
      //fail if n does not exist in the relevant domain of each of the argument positions
      std::map< int, std::map< TNode, std::vector< unsigned > > >::iterator it = d_var_rel_dom.find( v );
      if( it!=d_var_rel_dom.end() ){
        for( std::map< TNode, std::vector< unsigned > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
          for( unsigned j=0; j<it2->second.size(); j++ ){
            Debug("qcf-match-debug2") << n << " in relevant domain " <<  it2->first << "." << it2->second[j] << "?" << std::endl;
            if( !p->getTermDatabase()->inRelevantDomain( it2->first, it2->second[j], n ) ){
              Debug("qcf-match-debug") << "  -> fail, since " << n << " is not in relevant domain of " << it2->first << "." << it2->second[j] << std::endl;
              return false;
            }
          }
        }
      }
    }
    Debug("qcf-match-debug") << "-- bind : " << v << " -> " << n << ", checked " <<  d_curr_var_deq[v].size() << " disequalities" << std::endl;
    if( isGround ){
      if( d_vars[v].getKind()==BOUND_VARIABLE ){
        d_vars_set[v] = true;
        Debug("qcf-match-debug") << "---- now bound " << d_vars_set.size() << " / " << d_q[0].getNumChildren() << " base variables." << std::endl;
      }
    }
    d_match[v] = n;
    return true;
  }else{
    return false;
  }
}

void QuantInfo::unsetMatch( QuantConflictFind * p, int v ) {
  Debug("qcf-match-debug") << "-- unbind : " << v << std::endl;
  if( d_vars[v].getKind()==BOUND_VARIABLE && d_vars_set.find( v )!=d_vars_set.end() ){
    d_vars_set.erase( v );
  }
  d_match[ v ] = TNode::null();
}

bool QuantInfo::isMatchSpurious( QuantConflictFind * p ) {
  for( int i=0; i<getNumVars(); i++ ){
    //std::map< int, TNode >::iterator it = d_match.find( i );
    if( !d_match[i].isNull() ){
      if (!getCurrentCanBeEqual(p, i, d_match[i], p->atConflictEffort())) {
        return true;
      }
    }
  }
  return false;
}

bool QuantInfo::isTConstraintSpurious(QuantConflictFind* p,
                                      std::vector<Node>& terms)
{
  if( options::qcfEagerTest() ){
    //check whether the instantiation evaluates as expected
    if (p->atConflictEffort()) {
      Trace("qcf-instance-check") << "Possible conflict instance for " << d_q << " : " << std::endl;
      std::map< TNode, TNode > subs;
      for( unsigned i=0; i<terms.size(); i++ ){
        Trace("qcf-instance-check") << "  " << terms[i] << std::endl;
        subs[d_q[0][i]] = terms[i];
      }
      TermDb* tdb = p->getTermDatabase();
      for( unsigned i=0; i<d_extra_var.size(); i++ ){
        Node n = getCurrentExpValue( d_extra_var[i] );
        Trace("qcf-instance-check") << "  " << d_extra_var[i] << " -> " << n << std::endl;
        subs[d_extra_var[i]] = n;
      }
      if (!tdb->isEntailed(d_q[1], subs, false, false))
      {
        Trace("qcf-instance-check") << "...not entailed to be false." << std::endl;
        return true;
      }
    }else{
      Node inst =
          p->d_quantEngine->getInstantiate()->getInstantiation(d_q, terms);
      inst = Rewriter::rewrite(inst);
      Node inst_eval = p->getTermDatabase()->evaluateTerm(
          inst, nullptr, options::qcfTConstraint(), true);
      if( Trace.isOn("qcf-instance-check") ){
        Trace("qcf-instance-check") << "Possible propagating instance for " << d_q << " : " << std::endl;
        for( unsigned i=0; i<terms.size(); i++ ){
          Trace("qcf-instance-check") << "  " << terms[i] << std::endl;
        }
        Trace("qcf-instance-check") << "...evaluates to " << inst_eval << std::endl;
      }
      if (inst_eval.isNull()
          || (inst_eval.isConst() && inst_eval.getConst<bool>()))
      {
        Trace("qcf-instance-check") << "...spurious." << std::endl;
        return true;
      }else{
        Assert(p->isPropagatingInstance(inst_eval));
        Trace("qcf-instance-check") << "...not spurious." << std::endl;
      }
    }
  }
  if( !d_tconstraints.empty() ){
    //check constraints
    for( std::map< Node, bool >::iterator it = d_tconstraints.begin(); it != d_tconstraints.end(); ++it ){
      //apply substitution to the tconstraint
      Node cons =
          p->getTermUtil()->substituteBoundVariables(it->first, d_q, terms);
      cons = it->second ? cons : cons.negate();
      if (!entailmentTest(p, cons, p->atConflictEffort())) {
        return true;
      }
    }
  }
  // spurious if quantifiers engine is in conflict
  return p->d_quantEngine->inConflict();
}

bool QuantInfo::entailmentTest( QuantConflictFind * p, Node lit, bool chEnt ) {
  Trace("qcf-tconstraint-debug") << "Check : " << lit << std::endl;
  Node rew = Rewriter::rewrite( lit );
  if( rew==p->d_false ){
    Trace("qcf-tconstraint-debug") << "...constraint " << lit << " is disentailed (rewrites to false)." << std::endl;
    return false;
  }else if( rew!=p->d_true ){
    //if checking for conflicts, we must be sure that the (negation of) constraint is (not) entailed 
    if( !chEnt ){
      rew = Rewriter::rewrite( rew.negate() );
    }
    //check if it is entailed
    Trace("qcf-tconstraint-debug") << "Check entailment of " << rew << "..." << std::endl;
    std::pair<bool, Node> et = p->getQuantifiersEngine()->getTheoryEngine()->entailmentCheck(THEORY_OF_TYPE_BASED, rew );
    ++(p->d_statistics.d_entailment_checks);
    Trace("qcf-tconstraint-debug") << "ET result : " << et.first << " " << et.second << std::endl;
    if( !et.first ){
      Trace("qcf-tconstraint-debug") << "...cannot show entailment of " << rew << "." << std::endl;
      return !chEnt;
    }else{
      return chEnt;
    }
  }else{
    Trace("qcf-tconstraint-debug") << "...rewrites to true." << std::endl;
    return true;
  }
}

bool QuantInfo::completeMatch( QuantConflictFind * p, std::vector< int >& assigned, bool doContinue ) {
  //assign values for variables that were unassigned (usually not necessary, but handles corner cases)
  bool doFail = false;
  bool success = true;
  if( doContinue ){
    doFail = true;
    success = false;
  }else{
    if( isBaseMatchComplete() && options::qcfEagerTest() ){
      return true;
    }
    //solve for interpreted symbol matches
    //   this breaks the invariant that all introduced constraints are over existing terms
    for( int i=(int)(d_tsym_vars.size()-1); i>=0; i-- ){
      int index = d_tsym_vars[i];
      TNode v = getCurrentValue( d_vars[index] );
      int slv_v = -1;
      if( v==d_vars[index] ){
        slv_v = index;
      }
      Trace("qcf-tconstraint-debug") << "Solve " << d_vars[index] << " = " << v << " " << d_vars[index].getKind() << std::endl;
      if( d_vars[index].getKind()==PLUS || d_vars[index].getKind()==MULT ){
        Kind k = d_vars[index].getKind();
        std::vector< TNode > children;
        for( unsigned j=0; j<d_vars[index].getNumChildren(); j++ ){
          int vn = getVarNum( d_vars[index][j] );
          if( vn!=-1 ){
            TNode vv = getCurrentValue( d_vars[index][j] );
            if( vv==d_vars[index][j] ){
              //we will assign this
              if( slv_v==-1 ){
                Trace("qcf-tconstraint-debug") << "...will solve for var #" << vn << std::endl;
                slv_v = vn;
                if (!p->atConflictEffort()) {
                  break;
                }
              }else{
                Node z = p->getZero( k );
                if( !z.isNull() ){
                  Trace("qcf-tconstraint-debug") << "...set " << d_vars[vn] << " = " << z << std::endl;
                  assigned.push_back( vn );
                  if( !setMatch( p, vn, z, false, true ) ){
                    success = false;
                    break;
                  }
                }
              }
            }else{
              Trace("qcf-tconstraint-debug") << "...sum value " << vv << std::endl;
              children.push_back( vv );
            }
          }else{
            Trace("qcf-tconstraint-debug") << "...sum " << d_vars[index][j] << std::endl;
            children.push_back( d_vars[index][j] );
          }
        }
        if( success ){
          if( slv_v!=-1 ){
            Node lhs;
            if( children.empty() ){
              lhs = p->getZero( k );
            }else if( children.size()==1 ){
              lhs = children[0];
            }else{
              lhs = NodeManager::currentNM()->mkNode( k, children );
            }
            Node sum;
            if( v==d_vars[index] ){
              sum = lhs;
            }else{
              if (p->atConflictEffort()) {
                Kind kn = k;
                if( d_vars[index].getKind()==PLUS ){
                  kn = MINUS;
                }
                if( kn!=k ){
                  sum = NodeManager::currentNM()->mkNode( kn, v, lhs );
                }
              }
            }
            if( !sum.isNull() ){
              assigned.push_back( slv_v );
              Trace("qcf-tconstraint-debug") << "...set " << d_vars[slv_v] << " = " << sum << std::endl;
              if( !setMatch( p, slv_v, sum, false, true ) ){
                success = false;
              }
              p->d_tempCache.push_back( sum );
            }
          }else{
            //must show that constraint is met
            Node sum = NodeManager::currentNM()->mkNode( k, children );
            Node eq = sum.eqNode( v );
            if( !entailmentTest( p, eq ) ){
              success = false;
            }
            p->d_tempCache.push_back( sum );
          }
        }
      }

      if( !success ){
        break;
      }
    }
    if( success ){
      //check what is left to assign
      d_unassigned.clear();
      d_unassigned_tn.clear();
      std::vector< int > unassigned[2];
      std::vector< TypeNode > unassigned_tn[2];
      for( int i=0; i<getNumVars(); i++ ){
        if( d_match[i].isNull() ){
          int rindex = d_var_mg.find( i )==d_var_mg.end() ? 1 : 0;
          unassigned[rindex].push_back( i );
          unassigned_tn[rindex].push_back( getVar( i ).getType() );
          assigned.push_back( i );
        }
      }
      d_unassigned_nvar = unassigned[0].size();
      for( unsigned i=0; i<2; i++ ){
        d_unassigned.insert( d_unassigned.end(), unassigned[i].begin(), unassigned[i].end() );
        d_unassigned_tn.insert( d_unassigned_tn.end(), unassigned_tn[i].begin(), unassigned_tn[i].end() );
      }
      d_una_eqc_count.clear();
      d_una_index = 0;
    }
  }

  if( !d_unassigned.empty() && ( success || doContinue ) ){
    Trace("qcf-check") << "Assign to unassigned (" << d_unassigned.size() << ")..." << std::endl;
    do {
      if( doFail ){
        Trace("qcf-check-unassign") << "Failure, try again..." << std::endl;
      }
      bool invalidMatch = false;
      while( ( d_una_index>=0 && (int)d_una_index<(int)d_unassigned.size() ) || invalidMatch || doFail ){
        invalidMatch = false;
        if( !doFail && d_una_index==(int)d_una_eqc_count.size() ){
          //check if it has now been assigned
          if( d_una_index<d_unassigned_nvar ){
            if( !isConstrainedVar( d_unassigned[d_una_index] ) ){
              d_una_eqc_count.push_back( -1 );
            }else{
              d_var_mg[ d_unassigned[d_una_index] ]->reset( p, true, this );
              d_una_eqc_count.push_back( 0 );
            }
          }else{
            d_una_eqc_count.push_back( 0 );
          }
        }else{
          bool failed = false;
          if( !doFail ){
            if( d_una_index<d_unassigned_nvar ){
              if( !isConstrainedVar( d_unassigned[d_una_index] ) ){
                Trace("qcf-check-unassign") << "Succeeded, variable unconstrained at " << d_una_index << std::endl;
                d_una_index++;
              }else if( d_var_mg[d_unassigned[d_una_index]]->getNextMatch( p, this ) ){
                Trace("qcf-check-unassign") << "Succeeded match with mg at " << d_una_index << std::endl;
                d_una_index++;
              }else{
                failed = true;
                Trace("qcf-check-unassign") << "Failed match with mg at " << d_una_index << std::endl;
              }
            }else{
              Assert( doFail || d_una_index==(int)d_una_eqc_count.size()-1 );
              if( d_una_eqc_count[d_una_index]<(int)p->d_eqcs[d_unassigned_tn[d_una_index]].size() ){
                int currIndex = d_una_eqc_count[d_una_index];
                d_una_eqc_count[d_una_index]++;
                Trace("qcf-check-unassign") << d_unassigned[d_una_index] << "->" << p->d_eqcs[d_unassigned_tn[d_una_index]][currIndex] << std::endl;
                if( setMatch( p, d_unassigned[d_una_index], p->d_eqcs[d_unassigned_tn[d_una_index]][currIndex], true, true ) ){
                  d_match_term[d_unassigned[d_una_index]] = TNode::null();
                  Trace("qcf-check-unassign") << "Succeeded match " << d_una_index << std::endl;
                  d_una_index++;
                }else{
                  Trace("qcf-check-unassign") << "Failed match " << d_una_index << std::endl;
                  invalidMatch = true;
                }
              }else{
                failed = true;
                Trace("qcf-check-unassign") << "No more matches " << d_una_index << std::endl;
              }
            }
          }
          if( doFail || failed ){
            do{
              if( !doFail ){
                d_una_eqc_count.pop_back();
              }else{
                doFail = false;
              }
              d_una_index--;
            }while( d_una_index>=0 && d_una_eqc_count[d_una_index]==-1 );
          }
        }
      }
      success = d_una_index>=0;
      if( success ){
        doFail = true;
        Trace("qcf-check-unassign") << "  Try: " << std::endl;
        for( unsigned i=0; i<d_unassigned.size(); i++ ){
          int ui = d_unassigned[i];
          if( !d_match[ui].isNull() ){
            Trace("qcf-check-unassign") << "  Assigned #" << ui << " : " << d_vars[ui] << " -> " << d_match[ui] << std::endl;
          }
        }
      }
    }while( success && isMatchSpurious( p ) );
    Trace("qcf-check") << "done assigning." << std::endl;
  }
  if( success ){
    for( unsigned i=0; i<d_unassigned.size(); i++ ){
      int ui = d_unassigned[i];
      if( !d_match[ui].isNull() ){
        Trace("qcf-check") << "  Assigned #" << ui << " : " << d_vars[ui] << " -> " << d_match[ui] << std::endl;
      }
    }
    return true;
  }else{
    revertMatch( p, assigned );
    assigned.clear();
    return false;
  }
}

void QuantInfo::getMatch( std::vector< Node >& terms ){
  for( unsigned i=0; i<d_q[0].getNumChildren(); i++ ){
    //Node cv = qi->getCurrentValue( qi->d_match[i] );
    int repVar = getCurrentRepVar( i );
    Node cv;
    //std::map< int, TNode >::iterator itmt = qi->d_match_term.find( repVar );
    if( !d_match_term[repVar].isNull() ){
      cv = d_match_term[repVar];
    }else{
      cv = d_match[repVar];
    }
    Debug("qcf-check-inst") << "INST : " << i << " -> " << cv << ", from " << d_match[i] << std::endl;
    terms.push_back( cv );
  }
}

void QuantInfo::revertMatch( QuantConflictFind * p, std::vector< int >& assigned ) {
  for( unsigned i=0; i<assigned.size(); i++ ){
    unsetMatch( p, assigned[i] );
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
    if( !d_match_term[i].isNull() && d_match_term[i]!=d_match[i] ){
      Trace(c) << ", EXP : " << d_match_term[i];
    }
    Trace(c) <<  std::endl;
  }
  if( !d_tconstraints.empty() ){
    Trace(c) << "ADDITIONAL CONSTRAINTS : " << std::endl;
    for( std::map< Node, bool >::iterator it = d_tconstraints.begin(); it != d_tconstraints.end(); ++it ){
      Trace(c) << "   " << it->first << " -> " << it->second << std::endl;
    }
  }
}

MatchGen::MatchGen()
  : d_matched_basis(),
    d_binding(),
    d_tgt(),
    d_tgt_orig(),
    d_wasSet(),
    d_n(),
    d_type( typ_invalid ),
    d_type_not()
{
  d_qni_size = 0;
  d_child_counter = -1;
  d_use_children = true;
}


MatchGen::MatchGen( QuantInfo * qi, Node n, bool isVar )
  : d_matched_basis(),
    d_binding(),
    d_tgt(),
    d_tgt_orig(),
    d_wasSet(),
    d_n(),
    d_type(),
    d_type_not()
{
  //initialize temporary
  d_child_counter = -1;
  d_use_children = true;
  
  Trace("qcf-qregister-debug") << "Make match gen for " << n << ", isVar = " << isVar << std::endl;
  std::vector< Node > qni_apps;
  d_qni_size = 0;
  if( isVar ){
    Assert( qi->d_var_num.find( n )!=qi->d_var_num.end() );
    if( n.getKind()==ITE ){
      d_type = typ_invalid;
    }else{
      d_type = isHandledUfTerm( n ) ? typ_var : typ_tsym;
      d_qni_var_num[0] = qi->getVarNum( n );
      d_qni_size++;
      d_type_not = false;
      d_n = n;
      //Node f = getMatchOperator( n );
      for( unsigned j=0; j<d_n.getNumChildren(); j++ ){
        Node nn = d_n[j];
        Trace("qcf-qregister-debug") << "  " << d_qni_size;
        if( qi->isVar( nn ) ){
          int v = qi->d_var_num[nn];
          Trace("qcf-qregister-debug") << " is var #" << v << std::endl;
          d_qni_var_num[d_qni_size] = v;
          //qi->addFuncParent( v, f, j );
        }else{
          Trace("qcf-qregister-debug") << " is gterm " << nn << std::endl;
          d_qni_gterm[d_qni_size] = nn;
        }
        d_qni_size++;
      }
    }
  }else{
    if (expr::hasBoundVar(n))
    {
      d_type_not = false;
      d_n = n;
      if( d_n.getKind()==NOT ){
        d_n = d_n[0];
        d_type_not = !d_type_not;
      }

      if( isHandledBoolConnective( d_n ) ){
        //non-literals
        d_type = typ_formula;
        for( unsigned i=0; i<d_n.getNumChildren(); i++ ){
          if( d_n.getKind()!=FORALL || i==1 ){
            d_children.push_back( MatchGen( qi, d_n[i], false ) );
            if( !d_children[d_children.size()-1].isValid() ){
              setInvalid();
              break;
            }
          }
        }
      }else{
        d_type = typ_invalid;
        //literals
        if( isHandledUfTerm( d_n ) ){
          Assert( qi->isVar( d_n ) );
          d_type = typ_pred;
        }else if( d_n.getKind()==BOUND_VARIABLE ){
          Assert( d_n.getType().isBoolean() );
          d_type = typ_bool_var;
        }else if( d_n.getKind()==EQUAL || options::qcfTConstraint() ){
          for (unsigned i = 0; i < d_n.getNumChildren(); i++)
          {
            if (expr::hasBoundVar(d_n[i]))
            {
              if (!qi->isVar(d_n[i]))
              {
                Trace("qcf-qregister-debug")
                    << "ERROR : not var " << d_n[i] << std::endl;
              }
              Assert(qi->isVar(d_n[i]));
              if (d_n.getKind() != EQUAL && qi->isVar(d_n[i]))
              {
                d_qni_var_num[i + 1] = qi->d_var_num[d_n[i]];
              }
            }
            else
            {
              d_qni_gterm[i] = d_n[i];
            }
          }
          d_type = d_n.getKind() == EQUAL ? typ_eq : typ_tconstraint;
          Trace("qcf-tconstraint") << "T-Constraint : " << d_n << std::endl;
        }
      }
    }else{
      //we will just evaluate
      d_n = n;
      d_type = typ_ground;
    }
  }
  Trace("qcf-qregister-debug")  << "Done make match gen " << n << ", type = ";
  debugPrintType( "qcf-qregister-debug", d_type, true );
  Trace("qcf-qregister-debug") << std::endl;
  //Assert( d_children.size()==d_children_order.size() );

}

void MatchGen::collectBoundVar( QuantInfo * qi, Node n, std::vector< int >& cbvars, std::map< Node, bool >& visited, bool& hasNested ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==FORALL ){
      hasNested = true;
    }
    int v = qi->getVarNum( n );
    if( v!=-1 && std::find( cbvars.begin(), cbvars.end(), v )==cbvars.end() ){
      cbvars.push_back( v );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      collectBoundVar( qi, n[i], cbvars, visited, hasNested );
    }
  }
}

void MatchGen::determineVariableOrder( QuantInfo * qi, std::vector< int >& bvars ) {
  Trace("qcf-qregister-debug") << "Determine variable order " << d_n << ", #bvars = " << bvars.size() << std::endl;
  bool isComm = d_type==typ_formula && ( d_n.getKind()==OR || d_n.getKind()==AND || d_n.getKind()==EQUAL );
  if( isComm ){
    std::map< int, std::vector< int > > c_to_vars;
    std::map< int, std::vector< int > > vars_to_c;
    std::map< int, int > vb_count;
    std::map< int, int > vu_count;
    std::map< int, bool > has_nested;
    std::vector< bool > assigned;
    Trace("qcf-qregister-debug") << "Calculate bound variables..." << std::endl;
    for( unsigned i=0; i<d_children.size(); i++ ){
      std::map< Node, bool > visited;
      has_nested[i] = false;
      collectBoundVar( qi, d_children[i].d_n, c_to_vars[i], visited, has_nested[i] );
      assigned.push_back( false );
      vb_count[i] = 0;
      vu_count[i] = 0;
      for( unsigned j=0; j<c_to_vars[i].size(); j++ ){
        int v = c_to_vars[i][j];
        vars_to_c[v].push_back( i );
        if( std::find( bvars.begin(), bvars.end(), v )==bvars.end() ){
          vu_count[i]++;
        }else{
          vb_count[i]++;
        }
      }
    }
    //children that bind no unbound variable, then the most number of bound, unbound variables go first
    Trace("qcf-qregister-vo") << "Variable order for " << d_n << " : " << std::endl;
    do {
      int min_score0 = -1;
      int min_score = -1;
      int min_score_index = -1;
      for( unsigned i=0; i<d_children.size(); i++ ){
        if( !assigned[i] ){
          Trace("qcf-qregister-debug2") << "Child " << i << " has b/ub : " << vb_count[i] << "/" << vu_count[i] << std::endl;
          int score0 = 0;//has_nested[i] ? 0 : 1;
          int score;
          if( !options::qcfVoExp() ){
            score = vu_count[i];
          }else{
            score =  vu_count[i]==0 ? 0 : ( 1 + qi->d_vars.size()*( qi->d_vars.size() - vb_count[i] ) + ( qi->d_vars.size() - vu_count[i] )  );
          }
          if( min_score==-1 || score0<min_score0 || ( score0==min_score0 && score<min_score ) ){
            min_score0 = score0;
            min_score = score;
            min_score_index = i;
          }
        }
      }
      Trace("qcf-qregister-vo") << "  " << d_children_order.size()+1 << ": " << d_children[min_score_index].d_n << " : ";
      Trace("qcf-qregister-vo") << vu_count[min_score_index] << " " << vb_count[min_score_index] << " " << has_nested[min_score_index] << std::endl;
      Trace("qcf-qregister-debug") << "...assign child " << min_score_index << std::endl;
      Trace("qcf-qregister-debug") << "...score : " << min_score << std::endl;
      Assert( min_score_index!=-1 );
      //add to children order
      d_children_order.push_back( min_score_index );
      assigned[min_score_index] = true;
      //determine order internal to children
      d_children[min_score_index].determineVariableOrder( qi, bvars );
      Trace("qcf-qregister-debug")  << "...bind variables" << std::endl;
      //now, make it a bound variable
      if( vu_count[min_score_index]>0 ){
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
      }
      Trace("qcf-qregister-debug") << "...done assign child " << min_score_index << std::endl;
    }while( d_children_order.size()!=d_children.size() );
    Trace("qcf-qregister-debug") << "Done assign variable ordering for " << d_n << std::endl;
  }else{
    for( unsigned i=0; i<d_children.size(); i++ ){
      d_children_order.push_back( i );
      d_children[i].determineVariableOrder( qi, bvars );
      //now add to bvars
      std::map< Node, bool > visited;
      std::vector< int > cvars;
      bool has_nested = false;
      collectBoundVar( qi, d_children[i].d_n, cvars, visited, has_nested );
      for( unsigned j=0; j<cvars.size(); j++ ){
        if( std::find( bvars.begin(), bvars.end(), cvars[j] )==bvars.end() ){
          bvars.push_back( cvars[j] );
        }
      }
    }
  }
}

bool MatchGen::reset_round(QuantConflictFind* p)
{
  d_wasSet = false;
  for( unsigned i=0; i<d_children.size(); i++ ){
    if (!d_children[i].reset_round(p))
    {
      return false;
    }
  }
  for( std::map< int, TNode >::iterator it = d_qni_gterm.begin(); it != d_qni_gterm.end(); ++it ){
    d_qni_gterm_rep[it->first] = p->getRepresentative( it->second );
  }
  if( d_type==typ_ground ){
    // int e = p->evaluate( d_n );
    // if( e==1 ){
    //  d_ground_eval[0] = p->d_true;
    //}else if( e==-1 ){
    //  d_ground_eval[0] = p->d_false;
    //}
    // modified
    TermDb* tdb = p->getTermDatabase();
    QuantifiersEngine* qe = p->getQuantifiersEngine();
    for (unsigned i = 0; i < 2; i++)
    {
      if (tdb->isEntailed(d_n, i == 0))
      {
        d_ground_eval[0] = i==0 ? p->d_true : p->d_false;
      }
      if (qe->inConflict())
      {
        return false;
      }
    }
  }else if( d_type==typ_eq ){
    TermDb* tdb = p->getTermDatabase();
    QuantifiersEngine* qe = p->getQuantifiersEngine();
    for (unsigned i = 0, size = d_n.getNumChildren(); i < size; i++)
    {
      if (!expr::hasBoundVar(d_n[i]))
      {
        TNode t = tdb->getEntailedTerm(d_n[i]);
        if (qe->inConflict())
        {
          return false;
        }
        if (t.isNull())
        {
          d_ground_eval[i] = d_n[i];
        }
        else
        {
          d_ground_eval[i] = t;
        }
      }
    }
  }
  d_qni_bound_cons.clear();
  d_qni_bound_cons_var.clear();
  d_qni_bound.clear();
  return true;
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
  d_use_children = true;
  d_tgt_orig = d_tgt;

  //set up processing matches
  if( d_type==typ_invalid ){
    d_use_children = false;
  }else if( d_type==typ_ground ){
    d_use_children = false;
    if( d_ground_eval[0]==( d_tgt ? p->d_true : p->d_false ) ){
      d_child_counter = 0;
    }
  }else if( qi->isBaseMatchComplete() && options::qcfEagerTest() ){
    d_use_children = false;
    d_child_counter = 0;
  }else if( d_type==typ_bool_var ){
    //get current value of the variable
    TNode n = qi->getCurrentValue( d_n );
    int vn = qi->getCurrentRepVar( qi->getVarNum( n ) );
    if( vn==-1 ){
      //evaluate the value, see if it is compatible
      //int e = p->evaluate( n );
      //if( ( e==1 && d_tgt ) || ( e==0 && !d_tgt ) ){
      //  d_child_counter = 0;
      //}
      //modified 
      if( p->getTermDatabase()->isEntailed( n, d_tgt ) ){ 
        d_child_counter = 0;
      }
    }else{
      //unassigned, set match to true/false
      d_qni_bound[0] = vn;
      qi->setMatch( p, vn, d_tgt ? p->d_true : p->d_false, false, true );
      d_child_counter = 0;
    }
    if( d_child_counter==0 ){
      d_qn.push_back( NULL );
    }
  }else if( d_type==typ_var ){
    Assert( isHandledUfTerm( d_n ) );
    TNode f = getMatchOperator( p, d_n );
    Debug("qcf-match-debug") << "       reset: Var will match operators of " << f << std::endl;
    TNodeTrie* qni = p->getTermDatabase()->getTermArgTrie(Node::null(), f);
    if (qni == nullptr || qni->empty())
    {
      //inform irrelevant quantifiers
      p->setIrrelevantFunction( f );
    }
    else
    {
      d_qn.push_back(qni);
    }
    d_matched_basis = false;
  }else if( d_type==typ_tsym || d_type==typ_tconstraint ){
    for( std::map< int, int >::iterator it = d_qni_var_num.begin(); it != d_qni_var_num.end(); ++it ){
      int repVar = qi->getCurrentRepVar( it->second );
      if( qi->d_match[repVar].isNull() ){
        Debug("qcf-match-debug") << "Force matching on child #" << it->first << ", which is var #" << repVar << std::endl;
        d_qni_bound[it->first] = repVar;
      }
    }
    d_qn.push_back( NULL );
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
      //Trace("qcf-explain") << "    reset : " << d_n << " check ground values " << nn[0] << " " << nn[1] << " (tgt=" << d_tgt << ")" << std::endl;
      Debug("qcf-match-debug") << "       reset: check ground values " << nn[0] << " " << nn[1] << " (" << d_tgt << ")" << std::endl;
      //just compare values
      if( d_tgt ){
        success = p->areMatchEqual( nn[0], nn[1] );
      }else{
        if (p->atConflictEffort()) {
          success = p->areDisequal( nn[0], nn[1] );
        }else{
          success = p->areMatchDisequal( nn[0], nn[1] );
        }
      }
    }else{
      //otherwise, add a constraint to a variable  TODO: this may be over-eager at effort > conflict, since equality may be a propagation
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
        //Trace("qcf-explain") << "       reset: " << d_n << " add constraint " << vn[0] << " -> " << nn[1] << " (vn=" << vn[1] << ")" << ", d_tgt = " << d_tgt << std::endl;
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
        //fail
      } else if (d_n.getKind() == FORALL && p->atConflictEffort() &&
                 !options::qcfNestedConflict()) {
        //fail
      }else{
        //reset the first child to d_tgt
        d_child_counter = 0;
        getChild( d_child_counter )->reset( p, d_tgt, qi );
      }
    }
  }
  d_binding = false;
  d_wasSet = true;
  Debug("qcf-match") << "     reset: Finished reset for " << d_n << ", success = " << ( !d_qn.empty() || d_child_counter!=-1 ) << std::endl;
}

bool MatchGen::getNextMatch( QuantConflictFind * p, QuantInfo * qi ) {
  Debug("qcf-match") << "     Get next match for : " << d_n << ", type = ";
  debugPrintType( "qcf-match", d_type );
  Debug("qcf-match") << ", children = " << d_children.size() << ", binding = " << d_binding << std::endl;
  if( !d_use_children ){
    if( d_child_counter==0 ){
      d_child_counter = -1;
      return true;
    }else{
      d_wasSet = false;
      return false;
    }
  }else if( d_type==typ_var || d_type==typ_eq || d_type==typ_pred || d_type==typ_bool_var || d_type==typ_tconstraint || d_type==typ_tsym ){
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
          //for tconstraint, add constraint
          if( d_type==typ_tconstraint ){
            std::map< Node, bool >::iterator it = qi->d_tconstraints.find( d_n );
            if( it==qi->d_tconstraints.end() ){
              qi->d_tconstraints[d_n] = d_tgt;
              //store that we added this constraint
              d_qni_bound_cons[0] = d_n;
            }else if( d_tgt!=it->second ){
              success = false;
              terminate = true;
            }
          }
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
          QuantInfo::VarMgMap::const_iterator itm;
          if( !doFail ){
            Debug("qcf-match-debug") << "       check variable " << d_binding_it->second << std::endl;
            itm = qi->var_mg_find( d_binding_it->second );
          }
          if( doFail || ( d_binding_it->first!=0 && itm != qi->var_mg_end() ) ){
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
                  --d_binding_it;
                  Debug("qcf-match-debug") << "       decrement..." << std::endl;
                }
              }while( success &&
                      ( d_binding_it->first==0 ||
                        (!qi->containsVarMg(d_binding_it->second))));
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
            //Trace("qcf-explain") << "       cleanup: " << d_n << " remove constraint " << it->first << " -> " << it->second << " (vn=" << vn << ")" << ", d_tgt = " << d_tgt << std::endl;
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
          qi->unsetMatch( p, it->second );
          qi->d_match_term[ it->second ] = TNode::null();
        }
        d_qni_bound.clear();
      }
      if( d_type==typ_tconstraint ){
        //remove constraint if applicable
        if( d_qni_bound_cons.find( 0 )!=d_qni_bound_cons.end() ){
          qi->d_tconstraints.erase( d_n );
          d_qni_bound_cons.clear();
        }
      }
    }
    Debug("qcf-match") << "    ...finished matching for " << d_n << ", success = " << success << std::endl;
    d_wasSet = success;
    return success;
  }
  else if (d_type == typ_formula)
  {
    bool success = false;
    if( d_child_counter<0 ){
      if( d_child_counter<-1 ){
        success = true;
        d_child_counter = -1;
      }
    }else{
      while( !success && d_child_counter>=0 ){
        //transition system based on d_child_counter
        if( d_n.getKind()==OR || d_n.getKind()==AND ){
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
        }else if( d_n.getKind()==EQUAL ){
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
              if (d_child_counter == 4)
              {
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
        d_wasSet = success;
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
              std::map<TNode, TNodeTrie>::iterator it =
                  d_qn[index]->d_data.begin();
              if( it != d_qn[index]->d_data.end() ) {
                d_qni.push_back( it );
                //set the match
                if( it->first.getType().isComparableTo( qi->d_var_types[repVar] ) && qi->setMatch( p, d_qni_bound[index], it->first, true, true ) ){
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
            std::map<TNode, TNodeTrie>::iterator it =
                d_qn[index]->d_data.find(val);
            if( it!=d_qn[index]->d_data.end() ){
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
            if( d_qni[index]!=d_qn[index]->d_data.end() ){
              success = true;
              if( qi->setMatch( p, itb->second, d_qni[index]->first, true, true ) ){
                Debug("qcf-match-debug") << "       Bind next variable" << std::endl;
                if( d_qn.size()<d_qni_size ){
                  d_qn.push_back( &d_qni[index]->second );
                }
              }else{
                Debug("qcf-match-debug") << "       Bind next variable, currently fail" << std::endl;
                invalidMatch = true;
              }
            }else{
              qi->unsetMatch( p, itb->second );
              qi->d_match_term[ itb->second ] = TNode::null();
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
        //Assert( !d_qni[d_qni.size()-1]->second.d_data.empty() );
        //Debug("qcf-match-debug") << "       We matched " << d_qni[d_qni.size()-1]->second.d_children.begin()->first << std::endl;
        Assert( !d_qni[d_qni.size()-1]->second.d_data.empty() );
        TNode t = d_qni[d_qni.size()-1]->second.d_data.begin()->first;
        Debug("qcf-match-debug") << "       " << d_n << " matched " << t << std::endl;
        qi->d_match_term[d_qni_var_num[0]] = t;
        //set the match terms
        for( std::map< int, int >::iterator it = d_qni_bound.begin(); it != d_qni_bound.end(); ++it ){
          Debug("qcf-match-debug") << "       position " << it->first << " bounded " << it->second << " / " << qi->d_q[0].getNumChildren() << std::endl;
          //if( it->second<(int)qi->d_q[0].getNumChildren() ){   //if it is an actual variable, we are interested in knowing the actual term
          if( it->first>0 ){
            Assert( !qi->d_match[ it->second ].isNull() );
            Assert( p->areEqual( t[it->first-1], qi->d_match[ it->second ] ) );
            qi->d_match_term[it->second] = t[it->first-1];
          }
          //}
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
    case typ_bool_var: Trace(c) << "bool_var";break;
    }
  }else{
    switch( typ ){
    case typ_invalid: Debug(c) << "invalid";break;
    case typ_ground: Debug(c) << "ground";break;
    case typ_eq: Debug(c) << "eq";break;
    case typ_pred: Debug(c) << "pred";break;
    case typ_formula: Debug(c) << "formula";break;
    case typ_var: Debug(c) << "var";break;
    case typ_bool_var: Debug(c) << "bool_var";break;
    }
  }
}

void MatchGen::setInvalid() {
  d_type = typ_invalid;
  d_children.clear();
}

bool MatchGen::isHandledBoolConnective( TNode n ) {
  return TermUtil::isBoolConnectiveTerm( n ) && n.getKind()!=SEP_STAR;
}

bool MatchGen::isHandledUfTerm( TNode n ) {
  //return n.getKind()==APPLY_UF || n.getKind()==STORE || n.getKind()==SELECT ||
  //       n.getKind()==APPLY_CONSTRUCTOR || n.getKind()==APPLY_SELECTOR_TOTAL || n.getKind()==APPLY_TESTER;
  //TODO : treat APPLY_TESTER as a T-constraint instead of matching (currently leads to overabundance of instantiations)
  //return inst::Trigger::isAtomicTriggerKind( n.getKind() ) && ( !options::qcfTConstraint() || n.getKind()!=APPLY_TESTER );
  return inst::Trigger::isAtomicTriggerKind( n.getKind() );
}

Node MatchGen::getMatchOperator( QuantConflictFind * p, Node n ) {
  if( isHandledUfTerm( n ) ){
    return p->getTermDatabase()->getMatchOperator( n );
  }else{
    return Node::null();
  }
}

bool MatchGen::isHandled( TNode n ) {
  if (n.getKind() != BOUND_VARIABLE && expr::hasBoundVar(n))
  {
    if( !isHandledBoolConnective( n ) && !isHandledUfTerm( n ) && n.getKind()!=EQUAL && n.getKind()!=ITE ){
      return false;
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( !isHandled( n[i] ) ){
        return false;
      }
    }
  }
  return true;
}

QuantConflictFind::QuantConflictFind(QuantifiersEngine* qe, context::Context* c)
    : QuantifiersModule(qe),
      d_conflict(c, false),
      d_true(NodeManager::currentNM()->mkConst<bool>(true)),
      d_false(NodeManager::currentNM()->mkConst<bool>(false)),
      d_effort(EFFORT_INVALID)
{
}

//-------------------------------------------------- registration

void QuantConflictFind::registerQuantifier( Node q ) {
  if( d_quantEngine->hasOwnership( q, this ) ){
    d_quants.push_back( q );
    d_quant_id[q] = d_quants.size();
    if( Trace.isOn("qcf-qregister") ){
      Trace("qcf-qregister") << "Register ";
      debugPrintQuant( "qcf-qregister", q );
      Trace("qcf-qregister") << " : " << q << std::endl;
    }
    //make QcfNode structure
    Trace("qcf-qregister") << "- Get relevant equality/disequality pairs, calculate flattening..." << std::endl;
    d_qinfo[q].initialize( this, q, q[1] );

    //debug print
    if( Trace.isOn("qcf-qregister") ){
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
  }
}

bool QuantConflictFind::areMatchEqual( TNode n1, TNode n2 ) {
  //if( d_effort==QuantConflictFind::effort_mc ){
  //  return n1==n2 || !areDisequal( n1, n2 );
  //}else{
  return n1==n2;
  //}
}

bool QuantConflictFind::areMatchDisequal( TNode n1, TNode n2 ) {
  // if( d_effort==QuantConflictFind::Effort::Conflict ){
  //  return areDisequal( n1, n2 );
  //}else{
  return n1!=n2;
  //}
}

//-------------------------------------------------- check function

bool QuantConflictFind::needsCheck( Theory::Effort level ) {
  bool performCheck = false;
  if( options::quantConflictFind() && !d_conflict ){
    if( level==Theory::EFFORT_LAST_CALL ){
      performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_LAST_CALL;
    }else if( level==Theory::EFFORT_FULL ){
      performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_DEFAULT;
    }else if( level==Theory::EFFORT_STANDARD ){
      performCheck = options::qcfWhenMode()==QCF_WHEN_MODE_STD;
    }
  }
  return performCheck;
}

void QuantConflictFind::reset_round( Theory::Effort level ) {
  Trace("qcf-check") << "QuantConflictFind::reset_round" << std::endl;
  Trace("qcf-check") << "Compute relevant equivalence classes..." << std::endl;
  d_eqcs.clear();

  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator(getEqualityEngine());
  TermDb* tdb = getTermDatabase();
  while (!eqcs_i.isFinished())
  {
    Node r = (*eqcs_i);
    if (tdb->hasTermCurrent(r))
    {
      TypeNode rtn = r.getType();
      if (!options::cbqi() || !TermUtil::hasInstConstAttr(r))
      {
        d_eqcs[rtn].push_back(r);
      }
    }
    ++eqcs_i;
  }
}

void QuantConflictFind::setIrrelevantFunction( TNode f ) {
  if( d_irr_func.find( f )==d_irr_func.end() ){
    d_irr_func[f] = true;
    std::map< TNode, std::vector< Node > >::iterator it = d_func_rel_dom.find( f );
    if( it != d_func_rel_dom.end()){
      for( unsigned j=0; j<it->second.size(); j++ ){
        d_irr_quant[it->second[j]] = true;
      }
    }
  }
}

namespace {

// Returns the beginning of a range of efforts. The range can be iterated
// through as unsigned using operator++.
inline QuantConflictFind::Effort QcfEffortStart() {
  return QuantConflictFind::EFFORT_CONFLICT;
}

// Returns the beginning of a range of efforts. The value returned is included
// in the range.
inline QuantConflictFind::Effort QcfEffortEnd() {
  return options::qcfMode() == QCF_PROP_EQ ? QuantConflictFind::EFFORT_PROP_EQ
                                           : QuantConflictFind::EFFORT_CONFLICT;
}

}  // namespace

/** check */
void QuantConflictFind::check(Theory::Effort level, QEffort quant_e)
{
  CodeTimer codeTimer(d_quantEngine->d_statistics.d_qcf_time);
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  Trace("qcf-check") << "QCF : check : " << level << std::endl;
  if (d_conflict)
  {
    Trace("qcf-check2") << "QCF : finished check : already in conflict."
                        << std::endl;
    if (level >= Theory::EFFORT_FULL)
    {
      Trace("qcf-warn") << "ALREADY IN CONFLICT? " << level << std::endl;
    }
    return;
  }
  unsigned addedLemmas = 0;
  ++(d_statistics.d_inst_rounds);
  double clSet = 0;
  int prevEt = 0;
  if (Trace.isOn("qcf-engine"))
  {
    prevEt = d_statistics.d_entailment_checks.getData();
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qcf-engine") << "---Conflict Find Engine Round, effort = " << level
                        << "---" << std::endl;
  }

  // reset the round-specific information
  d_irr_func.clear();
  d_irr_quant.clear();

  if (Trace.isOn("qcf-debug"))
  {
    Trace("qcf-debug") << std::endl;
    debugPrint("qcf-debug");
    Trace("qcf-debug") << std::endl;
  }
  bool isConflict = false;
  FirstOrderModel* fm = d_quantEngine->getModel();
  unsigned nquant = fm->getNumAssertedQuantifiers();
  // for each effort level (find conflict, find propagating)
  for (unsigned e = QcfEffortStart(), end = QcfEffortEnd(); e <= end; ++e)
  {
    // set the effort (data member for convienence of access)
    d_effort = static_cast<Effort>(e);
    Trace("qcf-check") << "Checking quantified formulas at effort " << e
                       << "..." << std::endl;
    // for each quantified formula
    for (unsigned i = 0; i < nquant; i++)
    {
      Node q = fm->getAssertedQuantifier(i, true);
      if (d_quantEngine->hasOwnership(q, this)
          && d_irr_quant.find(q) == d_irr_quant.end()
          && fm->isQuantifierActive(q))
      {
        // check this quantified formula
        checkQuantifiedFormula(q, isConflict, addedLemmas);
        if (d_conflict || d_quantEngine->inConflict())
        {
          break;
        }
      }
    }
    // We are done if we added a lemma, or discovered a conflict in another
    // way. An example of the latter case is when two disequal congruent terms
    // are discovered during term indexing.
    if (addedLemmas > 0 || d_quantEngine->inConflict())
    {
      break;
    }
  }
  if (isConflict)
  {
    d_conflict.set(true);
  }
  if (Trace.isOn("qcf-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qcf-engine") << "Finished conflict find engine, time = "
                        << (clSet2 - clSet);
    if (addedLemmas > 0)
    {
      Trace("qcf-engine") << ", effort = "
                          << (d_effort == EFFORT_CONFLICT
                                  ? "conflict"
                                  : (d_effort == EFFORT_PROP_EQ ? "prop_eq"
                                                                : "mc"));
      Trace("qcf-engine") << ", addedLemmas = " << addedLemmas;
    }
    Trace("qcf-engine") << std::endl;
    int currEt = d_statistics.d_entailment_checks.getData();
    if (currEt != prevEt)
    {
      Trace("qcf-engine") << "  Entailment checks = " << (currEt - prevEt)
                          << std::endl;
    }
  }
  Trace("qcf-check2") << "QCF : finished check : " << level << std::endl;
}

void QuantConflictFind::checkQuantifiedFormula(Node q,
                                               bool& isConflict,
                                               unsigned& addedLemmas)
{
  QuantInfo* qi = &d_qinfo[q];
  Assert(d_qinfo.find(q) != d_qinfo.end());
  if (!qi->matchGeneratorIsValid())
  {
    // quantified formula is not properly set up for matching
    return;
  }
  if (Trace.isOn("qcf-check"))
  {
    Trace("qcf-check") << "Check quantified formula ";
    debugPrintQuant("qcf-check", q);
    Trace("qcf-check") << " : " << q << "..." << std::endl;
  }

  Trace("qcf-check-debug") << "Reset round..." << std::endl;
  if (!qi->reset_round(this))
  {
    // it is typically the case that another conflict (e.g. in the term
    // database) was discovered if we fail here.
    return;
  }
  // try to make a matches making the body false or propagating
  Trace("qcf-check-debug") << "Get next match..." << std::endl;
  Instantiate* qinst = d_quantEngine->getInstantiate();
  while (qi->getNextMatch(this))
  {
    if (d_quantEngine->inConflict())
    {
      Trace("qcf-check") << "   ... Quantifiers engine discovered conflict, ";
      Trace("qcf-check") << "probably related to disequal congruent terms in "
                            "master equality engine"
                         << std::endl;
      return;
    }
    if (Trace.isOn("qcf-inst"))
    {
      Trace("qcf-inst") << "*** Produced match at effort " << d_effort << " : "
                        << std::endl;
      qi->debugPrintMatch("qcf-inst");
      Trace("qcf-inst") << std::endl;
    }
    // check whether internal match constraints are satisfied
    if (qi->isMatchSpurious(this))
    {
      Trace("qcf-inst") << "   ... Spurious (match is inconsistent)"
                        << std::endl;
      continue;
    }
    // check whether match can be completed
    std::vector<int> assigned;
    if (!qi->completeMatch(this, assigned))
    {
      Trace("qcf-inst") << "   ... Spurious (cannot assign unassigned vars)"
                        << std::endl;
      continue;
    }
    // check whether the match is spurious according to (T-)entailment checks
    std::vector<Node> terms;
    qi->getMatch(terms);
    bool tcs = qi->isTConstraintSpurious(this, terms);
    if (tcs)
    {
      Trace("qcf-inst") << "   ... Spurious (match is T-inconsistent)"
                        << std::endl;
    }
    else
    {
      // otherwise, we have a conflict/propagating instance
      // for debugging
      if (Debug.isOn("qcf-check-inst"))
      {
        Node inst = qinst->getInstantiation(q, terms);
        Debug("qcf-check-inst")
            << "Check instantiation " << inst << "..." << std::endl;
        Assert(!getTermDatabase()->isEntailed(inst, true));
        Assert(getTermDatabase()->isEntailed(inst, false)
               || d_effort > EFFORT_CONFLICT);
      }
      // Process the lemma: either add an instantiation or specific lemmas
      // constructed during the isTConstraintSpurious call, or both.
      if (!qinst->addInstantiation(q, terms))
      {
        Trace("qcf-inst") << "   ... Failed to add instantiation" << std::endl;
        // This should only happen if the algorithm generates the same
        // propagating instance twice this round. In this case, return
        // to avoid exponential behavior.
        return;
      }
      Trace("qcf-check") << "   ... Added instantiation" << std::endl;
      if (Trace.isOn("qcf-inst"))
      {
        Trace("qcf-inst") << "*** Was from effort " << d_effort << " : "
                          << std::endl;
        qi->debugPrintMatch("qcf-inst");
        Trace("qcf-inst") << std::endl;
      }
      ++addedLemmas;
      if (d_effort == EFFORT_CONFLICT)
      {
        // mark relevant: this ensures that quantified formula q is
        // checked first on the next round. This is an optimization to
        // ensure that quantified formulas that are more likely to have
        // conflicting instances are checked earlier.
        d_quantEngine->markRelevant(q);
        ++(d_quantEngine->d_statistics.d_instantiations_qcf);
        if (options::qcfAllConflict())
        {
          isConflict = true;
        }
        else
        {
          d_conflict.set(true);
        }
        return;
      }
      else if (d_effort == EFFORT_PROP_EQ)
      {
        d_quantEngine->markRelevant(q);
        ++(d_quantEngine->d_statistics.d_instantiations_qcf);
      }
    }
    // clean up assigned
    qi->revertMatch(this, assigned);
    d_tempCache.clear();
  }
  Trace("qcf-check") << "Done, conflict = " << d_conflict << std::endl;
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
  d_entailment_checks("QuantConflictFind::Entailment_Checks",0)
{
  smtStatisticsRegistry()->registerStat(&d_inst_rounds);
  smtStatisticsRegistry()->registerStat(&d_entailment_checks);
}

QuantConflictFind::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_inst_rounds);
  smtStatisticsRegistry()->unregisterStat(&d_entailment_checks);
}

TNode QuantConflictFind::getZero( Kind k ) {
  std::map< Kind, Node >::iterator it = d_zero.find( k );
  if( it==d_zero.end() ){
    Node nn;
    if( k==PLUS ){
      nn = NodeManager::currentNM()->mkConst( Rational(0) );
    }
    d_zero[k] = nn;
    return nn;
  }else{
    return it->second;
  }
}

std::ostream& operator<<(std::ostream& os, const QuantConflictFind::Effort& e) {
  switch (e) {
    case QuantConflictFind::EFFORT_INVALID:
      os << "Invalid";
      break;
    case QuantConflictFind::EFFORT_CONFLICT:
      os << "Conflict";
      break;
    case QuantConflictFind::EFFORT_PROP_EQ:
      os << "PropEq";
      break;
  }
  return os;
}

bool QuantConflictFind::isPropagatingInstance(Node n) const
{
  std::unordered_set<TNode, TNodeHashFunction> visited;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      Kind ck = cur.getKind();
      if (ck == FORALL)
      {
        // do nothing
      }
      else if (TermUtil::isBoolConnective(ck))
      {
        for (TNode cc : cur)
        {
          visit.push_back(cc);
        }
      }
      else if (!getEqualityEngine()->hasTerm(cur))
      {
        Trace("qcf-instance-check-debug")
            << "...not propagating instance because of " << n << std::endl;
        return false;
      }
    }
  } while (!visit.empty());
  return true;
}

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */
