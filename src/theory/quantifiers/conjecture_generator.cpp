/*********************                                                        */
/*! \file conjecture_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief conjecture generator class
 **
 **/

#include "theory/quantifiers/conjecture_generator.h"
#include "expr/term_canonize.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "util/random.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

struct sortConjectureScore {
  std::vector< int > d_scores;
  bool operator() (unsigned i, unsigned j) { return d_scores[i]>d_scores[j]; }
};


void OpArgIndex::addTerm( std::vector< TNode >& terms, TNode n, unsigned index ){
  if( index==n.getNumChildren() ){
    Assert(n.hasOperator());
    if( std::find( d_ops.begin(), d_ops.end(), n.getOperator() )==d_ops.end() ){
      d_ops.push_back( n.getOperator() );
      d_op_terms.push_back( n );
    }
  }else{
    d_child[terms[index]].addTerm( terms, n, index+1 );
  }
}

Node OpArgIndex::getGroundTerm( ConjectureGenerator * s, std::vector< TNode >& args ) {
  if( d_ops.empty() ){
    for( std::map< TNode, OpArgIndex >::iterator it = d_child.begin(); it != d_child.end(); ++it ){
      std::map< TNode, Node >::iterator itf = s->d_ground_eqc_map.find( it->first );
      if( itf!=s->d_ground_eqc_map.end() ){
        args.push_back( itf->second );
        Node n = it->second.getGroundTerm( s, args );
        args.pop_back();
        if( !n.isNull() ){
          return n;
        }
      }
    }
    return Node::null();
  }
  std::vector<TNode> args2;
  if (d_op_terms[0].getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    args2.push_back( d_ops[0] );
  }
  args2.insert(args2.end(), args.begin(), args.end());
  return NodeManager::currentNM()->mkNode(d_op_terms[0].getKind(), args2);
}

void OpArgIndex::getGroundTerms( ConjectureGenerator * s, std::vector< TNode >& terms ) {
  terms.insert( terms.end(), d_op_terms.begin(), d_op_terms.end() );
  for( std::map< TNode, OpArgIndex >::iterator it = d_child.begin(); it != d_child.end(); ++it ){
    if( s->isGroundEqc( it->first ) ){
      it->second.getGroundTerms( s, terms );
    }
  }
}

ConjectureGenerator::ConjectureGenerator(QuantifiersEngine* qe,
                                         context::Context* c)
    : QuantifiersModule(qe),
      d_notify(*this),
      d_uequalityEngine(d_notify, c, "ConjectureGenerator::ee", false),
      d_ee_conjectures(c),
      d_conj_count(0),
      d_subs_confirmCount(0),
      d_subs_unkCount(0),
      d_fullEffortCount(0),
      d_hasAddedLemma(false)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
  d_uequalityEngine.addFunctionKind( kind::APPLY_UF );
  d_uequalityEngine.addFunctionKind( kind::APPLY_CONSTRUCTOR );

}

ConjectureGenerator::~ConjectureGenerator()
{
  for (std::map<Node, EqcInfo*>::iterator i = d_eqc_info.begin(),
                                          iend = d_eqc_info.end();
       i != iend;
       ++i)
  {
    EqcInfo* current = (*i).second;
    Assert(current != nullptr);
    delete current;
  }
}

void ConjectureGenerator::eqNotifyNewClass( TNode t ){
  Trace("thm-ee-debug") << "UEE : new equivalence class " << t << std::endl;
  d_upendingAdds.push_back( t );
}

void ConjectureGenerator::eqNotifyMerge(TNode t1, TNode t2)
{
  //get maintained representatives
  TNode rt1 = t1;
  TNode rt2 = t2;
  std::map< Node, EqcInfo* >::iterator it1 = d_eqc_info.find( t1 );
  if( it1!=d_eqc_info.end() && !it1->second->d_rep.get().isNull() ){
    rt1 = it1->second->d_rep.get();
  }
  std::map< Node, EqcInfo* >::iterator it2 = d_eqc_info.find( t2 );
  if( it2!=d_eqc_info.end() && !it2->second->d_rep.get().isNull() ){
    rt2 = it2->second->d_rep.get();
  }
  Trace("thm-ee-debug") << "UEE : equality holds : " << t1 << " == " << t2 << std::endl;
  Trace("thm-ee-debug") << "      ureps : " << rt1 << " == " << rt2 << std::endl;
  Trace("thm-ee-debug") << "      relevant : " << d_pattern_is_relevant[rt1] << " " << d_pattern_is_relevant[rt2] << std::endl;
  Trace("thm-ee-debug") << "      normal : " << d_pattern_is_normal[rt1] << " " << d_pattern_is_normal[rt2] << std::endl;
  Trace("thm-ee-debug") << "      size :   " << d_pattern_fun_sum[rt1] << " " << d_pattern_fun_sum[rt2] << std::endl;

  if( isUniversalLessThan( rt2, rt1 ) ){
    EqcInfo * ei;
    if( it1==d_eqc_info.end() ){
      ei = getOrMakeEqcInfo( t1, true );
    }else{
      ei = it1->second;
    }
    ei->d_rep = t2;
  }
}


ConjectureGenerator::EqcInfo::EqcInfo( context::Context* c ) : d_rep( c, Node::null() ){

}

ConjectureGenerator::EqcInfo* ConjectureGenerator::getOrMakeEqcInfo( TNode n, bool doMake ) {
  //Assert( getUniversalRepresentative( n )==n );
  std::map< Node, EqcInfo* >::iterator eqc_i = d_eqc_info.find( n );
  if( eqc_i!=d_eqc_info.end() ){
    return eqc_i->second;
  }else if( doMake ){
    EqcInfo* ei = new EqcInfo( d_quantEngine->getSatContext() );
    d_eqc_info[n] = ei;
    return ei;
  }else{
    return NULL;
  }
}

void ConjectureGenerator::setUniversalRelevant( TNode n ) {
  //add pattern information
  registerPattern( n, n.getType() );
  d_urelevant_terms[n] = true;
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    setUniversalRelevant( n[i] );
  }
}

bool ConjectureGenerator::isUniversalLessThan( TNode rt1, TNode rt2 ) {
  //prefer the one that is (normal, smaller) lexographically
  Assert(d_pattern_is_relevant.find(rt1) != d_pattern_is_relevant.end());
  Assert(d_pattern_is_relevant.find(rt2) != d_pattern_is_relevant.end());
  Assert(d_pattern_is_normal.find(rt1) != d_pattern_is_normal.end());
  Assert(d_pattern_is_normal.find(rt2) != d_pattern_is_normal.end());
  Assert(d_pattern_fun_sum.find(rt1) != d_pattern_fun_sum.end());
  Assert(d_pattern_fun_sum.find(rt2) != d_pattern_fun_sum.end());

  if( d_pattern_is_relevant[rt1] && !d_pattern_is_relevant[rt2] ){
    Trace("thm-ee-debug") << "UEE : LT due to relevant." << std::endl;
    return true;
  }else if( d_pattern_is_relevant[rt1]==d_pattern_is_relevant[rt2] ){
    if( d_pattern_is_normal[rt1] && !d_pattern_is_normal[rt2] ){
      Trace("thm-ee-debug") << "UEE : LT due to normal." << std::endl;
      return true;
    }else if( d_pattern_is_normal[rt1]==d_pattern_is_normal[rt2] ){
      if( d_pattern_fun_sum[rt1]<d_pattern_fun_sum[rt2] ){
        Trace("thm-ee-debug") << "UEE : LT due to size." << std::endl;
        //decide which representative to use : based on size of the term
        return true;
      }else if( d_pattern_fun_sum[rt1]==d_pattern_fun_sum[rt2] ){
        //same size : tie goes to term that has already been reported
        return isReportedCanon( rt1 ) && !isReportedCanon( rt2 );
      }
    }
  }
  return false;
}


bool ConjectureGenerator::isReportedCanon( TNode n ) {
  return std::find( d_ue_canon.begin(), d_ue_canon.end(), n )==d_ue_canon.end();
}

void ConjectureGenerator::markReportedCanon( TNode n ) {
  if( !isReportedCanon( n ) ){
    d_ue_canon.push_back( n );
  }
}

bool ConjectureGenerator::areUniversalEqual( TNode n1, TNode n2 ) {
  return n1==n2 || ( d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areEqual( n1, n2 ) );
}

bool ConjectureGenerator::areUniversalDisequal( TNode n1, TNode n2 ) {
  return n1!=n2 && d_uequalityEngine.hasTerm( n1 ) && d_uequalityEngine.hasTerm( n2 ) && d_uequalityEngine.areDisequal( n1, n2, false );
}

Node ConjectureGenerator::getUniversalRepresentative(TNode n, bool add)
{
  if( add ){
    if( d_urelevant_terms.find( n )==d_urelevant_terms.end() ){
      setUniversalRelevant( n );
      //add term to universal equality engine
      d_uequalityEngine.addTerm( n );
      // addding this term to equality engine will lead to a set of new terms (the new subterms of n)
      // now, do instantiation-based merging for each of these terms
      Trace("thm-ee-debug") << "Merge equivalence classes based on instantiations of terms..." << std::endl;
      //merge all pending equalities
      while( !d_upendingAdds.empty() ){
        Trace("sg-pending") << "Add " << d_upendingAdds.size() << " pending terms..." << std::endl;
        std::vector< Node > pending;
        pending.insert( pending.end(), d_upendingAdds.begin(), d_upendingAdds.end() );
        d_upendingAdds.clear();
        for( unsigned i=0; i<pending.size(); i++ ){
          Node t = pending[i];
          TypeNode tn = t.getType();
          Trace("thm-ee-add") << "UEE : Add universal term " << t << std::endl;
          std::vector< Node > eq_terms;
          //if occurs modulo equality at ground level, it is equivalent to representative of ground equality engine
          Node gt = getTermDatabase()->evaluateTerm(t);
          if( !gt.isNull() && gt!=t ){
            eq_terms.push_back( gt );
          }
          //get all equivalent terms based on theorem database
          d_thm_index.getEquivalentTerms( t, eq_terms );
          if( !eq_terms.empty() ){
            Trace("thm-ee-add") << "UEE : Based on ground EE/theorem DB, it is equivalent to " << eq_terms.size() << " terms : " << std::endl;
            //add equivalent terms as equalities to universal engine
            for (const Node& eqt : eq_terms)
            {
              Trace("thm-ee-add") << "  " << eqt << std::endl;
              bool assertEq = false;
              if (d_urelevant_terms.find(eqt) != d_urelevant_terms.end())
              {
                assertEq = true;
              }
              else
              {
                Assert(eqt.getType() == tn);
                registerPattern(eqt, tn);
                if (isUniversalLessThan(eqt, t)
                    || (options::conjectureUeeIntro()
                        && d_pattern_fun_sum[t] >= d_pattern_fun_sum[eqt]))
                {
                  setUniversalRelevant(eqt);
                  assertEq = true;
                }
              }
              if( assertEq ){
                Node exp;
                d_uequalityEngine.assertEquality(t.eqNode(eqt), true, exp);
              }else{
                Trace("thm-ee-no-add")
                    << "Do not add : " << t << " == " << eqt << std::endl;
              }
            }
          }else{
            Trace("thm-ee-add") << "UEE : No equivalent terms." << std::endl;
          }
        }
      }
    }
  }

  if( d_uequalityEngine.hasTerm( n ) ){
    Node r = d_uequalityEngine.getRepresentative( n );
    EqcInfo * ei = getOrMakeEqcInfo( r );
    if( ei && !ei->d_rep.get().isNull() ){
      return ei->d_rep.get();
    }else{
      return r;
    }
  }else{
    return n;
  }
}

Node ConjectureGenerator::getFreeVar( TypeNode tn, unsigned i ) {
  return d_quantEngine->getTermCanonize()->getCanonicalFreeVar(tn, i);
}

bool ConjectureGenerator::isHandledTerm( TNode n ){
  return d_quantEngine->getTermDatabase()->isTermActive( n ) && inst::Trigger::isAtomicTrigger( n ) && ( n.getKind()!=APPLY_UF || n.getOperator().getKind()!=SKOLEM );
}

Node ConjectureGenerator::getGroundEqc( TNode r ) {
  std::map< TNode, Node >::iterator it = d_ground_eqc_map.find( r );
  return it!=d_ground_eqc_map.end() ? it->second : Node::null();
}

bool ConjectureGenerator::isGroundEqc( TNode r ) {
  return d_ground_eqc_map.find( r )!=d_ground_eqc_map.end();
}

bool ConjectureGenerator::isGroundTerm( TNode n ) {
  return std::find( d_ground_terms.begin(), d_ground_terms.end(), n )!=d_ground_terms.end();
}

bool ConjectureGenerator::needsCheck( Theory::Effort e ) {
  // synchonized with instantiation engine
  return d_quantEngine->getInstWhenNeedsCheck( e );
}

bool ConjectureGenerator::hasEnumeratedUf( Node n ) {
  if( options::conjectureGenGtEnum()>0 ){
    std::map< Node, bool >::iterator it = d_uf_enum.find( n.getOperator() );
    if( it==d_uf_enum.end() ){
      d_uf_enum[n.getOperator()] = true;
      std::vector< Node > lem;
      getEnumeratePredUfTerm( n, options::conjectureGenGtEnum(), lem );
      if( !lem.empty() ){
        for( unsigned j=0; j<lem.size(); j++ ){
          d_quantEngine->addLemma( lem[j], false );
          d_hasAddedLemma = true;
        }
        return false;
      }
    }
  }
  return true;
}

void ConjectureGenerator::reset_round( Theory::Effort e ) {

}
void ConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e == QEFFORT_STANDARD)
  {
    d_fullEffortCount++;
    if( d_fullEffortCount%optFullCheckFrequency()==0 ){
      d_hasAddedLemma = false;
      d_tge.d_cg = this;
      double clSet = 0;
      if( Trace.isOn("sg-engine") ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Trace("sg-engine") << "---Conjecture Engine Round, effort = " << e << "---" << std::endl;
      }
      eq::EqualityEngine * ee = getEqualityEngine();
      d_conj_count = 0;

      Trace("sg-proc") << "Get eq classes..." << std::endl;
      d_op_arg_index.clear();
      d_ground_eqc_map.clear();
      d_bool_eqc[0] = Node::null();
      d_bool_eqc[1] = Node::null();
      std::vector< TNode > eqcs;
      d_em.clear();
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
      while( !eqcs_i.isFinished() ){
        TNode r = (*eqcs_i);
        Trace("sg-proc-debug") << "...eqc : " << r << std::endl;
        eqcs.push_back( r );
        if( r.getType().isBoolean() ){
          if (areEqual(r, d_true))
          {
            d_ground_eqc_map[r] = d_true;
            d_bool_eqc[0] = r;
          }
          else if (areEqual(r, d_false))
          {
            d_ground_eqc_map[r] = d_false;
            d_bool_eqc[1] = r;
          }
        }
        d_em[r] = eqcs.size();
        eq::EqClassIterator ieqc_i = eq::EqClassIterator( r, ee );
        while( !ieqc_i.isFinished() ){
          TNode n = (*ieqc_i);
          Trace("sg-proc-debug") << "......term : " << n << std::endl;
          if( getTermDatabase()->hasTermCurrent( n ) ){
            if( isHandledTerm( n ) ){
              getTermDatabase()->computeArgReps( n );
              d_op_arg_index[r].addTerm( getTermDatabase()->d_arg_reps[n], n );
            }
          }
          ++ieqc_i;
        }
        ++eqcs_i;
      }
      Assert(!d_bool_eqc[0].isNull());
      Assert(!d_bool_eqc[1].isNull());
      d_urelevant_terms.clear();
      Trace("sg-proc") << "...done get eq classes" << std::endl;

      Trace("sg-proc") << "Determine ground EQC..." << std::endl;
      bool success;
      do{
        success = false;
        for( unsigned i=0; i<eqcs.size(); i++ ){
          TNode r = eqcs[i];
          if( d_ground_eqc_map.find( r )==d_ground_eqc_map.end() ){
            std::vector< TNode > args;
            Trace("sg-pat-debug") << "******* Get ground term for " << r << std::endl;
            Node n;
            if (Skolemize::isInductionTerm(r))
            {
              n = d_op_arg_index[r].getGroundTerm( this, args );
            }else{
              n = r;
            }
            if( !n.isNull() ){
              Trace("sg-pat") << "Ground term for eqc " << r << " : " << std::endl;
              Trace("sg-pat") << "   " << n << std::endl;
              d_ground_eqc_map[r] = n;
              success = true;
            }else{
              Trace("sg-pat-debug") << "...could not find ground term." << std::endl;
            }
          }
        }
      }while( success );
      //also get ground terms
      d_ground_terms.clear();
      for( unsigned i=0; i<eqcs.size(); i++ ){
        TNode r = eqcs[i];
        d_op_arg_index[r].getGroundTerms( this, d_ground_terms );
      }
      Trace("sg-proc") << "...done determine ground EQC" << std::endl;

      //debug printing
      if( Trace.isOn("sg-gen-eqc") ){
        for( unsigned i=0; i<eqcs.size(); i++ ){
          TNode r = eqcs[i];
          //print out members
          bool firstTime = true;
          bool isFalse = areEqual(r, d_false);
          eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
          while( !eqc_i.isFinished() ){
            TNode n = (*eqc_i);
            if( getTermDatabase()->hasTermCurrent( n ) && getTermDatabase()->isTermActive( n ) && ( n.getKind()!=EQUAL || isFalse ) ){
              if( firstTime ){
                Trace("sg-gen-eqc") << "e" << d_em[r] << " : { " << std::endl;
                firstTime = false;
              }
              if( n.hasOperator() ){
                Trace("sg-gen-eqc") << "   (" << n.getOperator();
                getTermDatabase()->computeArgReps( n );
                for (TNode ar : getTermDatabase()->d_arg_reps[n])
                {
                  Trace("sg-gen-eqc") << " e" << d_em[ar];
                }
                Trace("sg-gen-eqc") << ") :: " << n << std::endl;
              }else{
                Trace("sg-gen-eqc") << "   " << n << std::endl;
              }
            }
            ++eqc_i;
          }
          if( !firstTime ){
            Trace("sg-gen-eqc") << "}" << std::endl;
            //print out ground term
            std::map< TNode, Node >::iterator it = d_ground_eqc_map.find( r );
            if( it!=d_ground_eqc_map.end() ){
              Trace("sg-gen-eqc") << "- Ground term : " << it->second << std::endl;
            }
          }
        }
      }

      Trace("sg-proc") << "Compute relevant eqc..." << std::endl;
      d_tge.d_relevant_eqc[0].clear();
      d_tge.d_relevant_eqc[1].clear();
      for( unsigned i=0; i<eqcs.size(); i++ ){
        TNode r = eqcs[i];
        std::map< TNode, Node >::iterator it = d_ground_eqc_map.find( r );
        unsigned index = 1;
        if( it==d_ground_eqc_map.end() ){
          index = 0;
        }
        //based on unproven conjectures? TODO
        d_tge.d_relevant_eqc[index].push_back( r );
      }
      Trace("sg-gen-tg-debug") << "Initial relevant eqc : ";
      for( unsigned i=0; i<d_tge.d_relevant_eqc[0].size(); i++ ){
        Trace("sg-gen-tg-debug") << "e" << d_em[d_tge.d_relevant_eqc[0][i]] << " ";
      }
      Trace("sg-gen-tg-debug") << std::endl;
      Trace("sg-proc") << "...done compute relevant eqc" << std::endl;


      Trace("sg-proc") << "Collect signature information..." << std::endl;
      d_tge.collectSignatureInformation();
      if( d_hasAddedLemma ){
        Trace("sg-proc") << "...added enumeration lemmas." << std::endl;
      }
      Trace("sg-proc") << "...done collect signature information" << std::endl;



      Trace("sg-proc") << "Build theorem index..." << std::endl;
      d_ue_canon.clear();
      d_thm_index.clear();
      std::vector< Node > provenConj;
      quantifiers::FirstOrderModel* m = d_quantEngine->getModel();
      for( unsigned i=0; i<m->getNumAssertedQuantifiers(); i++ ){
        Node q = m->getAssertedQuantifier( i );
        Trace("thm-db-debug") << "Is " << q << " a relevant theorem?" << std::endl;
        Node conjEq;
        if( q[1].getKind()==EQUAL ){
          bool isSubsume = false;
          bool inEe = false;
          for( unsigned r=0; r<2; r++ ){
            TNode nl = q[1][r==0 ? 0 : 1];
            TNode nr = q[1][r==0 ? 1 : 0];
            Node eq = nl.eqNode( nr );
            if( r==1 || std::find( d_conjectures.begin(), d_conjectures.end(), q )==d_conjectures.end() ){
              //check if it contains only relevant functions
              if( d_tge.isRelevantTerm( eq ) ){
                //make it canonical
                Trace("sg-proc-debug") << "get canonical " << eq << std::endl;
                eq = d_quantEngine->getTermCanonize()->getCanonicalTerm(eq);
              }else{
                eq = Node::null();
              }
            }
            if( !eq.isNull() ){
              if( r==0 ){
                inEe = d_ee_conjectures.find( q[1] )!=d_ee_conjectures.end();
                if( !inEe ){
                  //add to universal equality engine
                  Node nlu = getUniversalRepresentative(eq[0], true);
                  Node nru = getUniversalRepresentative(eq[1], true);
                  if (areUniversalEqual(nlu, nru))
                  {
                    isSubsume = true;
                    //set inactive (will be ignored by other modules)
                    d_quantEngine->getModel()->setQuantifierActive( q, false );
                  }
                  else
                  {
                    Node exp;
                    d_ee_conjectures[q[1]] = true;
                    d_uequalityEngine.assertEquality(
                        nlu.eqNode(nru), true, exp);
                  }
                }
                Trace("sg-conjecture") << "*** CONJECTURE : currently proven" << (isSubsume ? " and subsumed" : "");
                Trace("sg-conjecture") << " : " << q[1] << std::endl;
                provenConj.push_back( q );
              }
              if( !isSubsume ){
                Trace("thm-db-debug") << "Adding theorem to database " << eq[0] << " == " << eq[1] << std::endl;
                d_thm_index.addTheorem( eq[0], eq[1] );
              }else{
                break;
              }
            }else{
              break;
            }
          }
        }
      }
      //examine status of other conjectures
      for( unsigned i=0; i<d_conjectures.size(); i++ ){
        Node q = d_conjectures[i];
        if( std::find( provenConj.begin(), provenConj.end(), q )==provenConj.end() ){
          //check each skolem variable
          bool disproven = true;
          std::vector<Node> skolems;
          d_quantEngine->getSkolemize()->getSkolemConstants(q, skolems);
          Trace("sg-conjecture") << "    CONJECTURE : ";
          std::vector< Node > ce;
          for (unsigned j = 0; j < skolems.size(); j++)
          {
            TNode rk = getRepresentative(skolems[j]);
            std::map< TNode, Node >::iterator git = d_ground_eqc_map.find( rk );
            //check if it is a ground term
            if( git==d_ground_eqc_map.end() ){
              Trace("sg-conjecture") << "ACTIVE : " << q;
              if( Trace.isOn("sg-gen-eqc") ){
                Trace("sg-conjecture") << " { ";
                for (unsigned k = 0; k < skolems.size(); k++)
                {
                  Trace("sg-conjecture") << skolems[k] << (j == k ? "*" : "")
                                         << " ";
                }
                Trace("sg-conjecture") << "}";
              }
              Trace("sg-conjecture") << std::endl;
              disproven = false;
              break;
            }else{
              ce.push_back( git->second );
            }
          }
          if( disproven ){
            Trace("sg-conjecture") << "disproven : " << q << " : ";
            for (unsigned j = 0, ceSize = ce.size(); j < ceSize; j++)
            {
              Trace("sg-conjecture") << q[0][j] << " -> " << ce[j] << " ";
            }
            Trace("sg-conjecture") << std::endl;
          }
        }
      }
      Trace("thm-db") << "Theorem database is : " << std::endl;
      d_thm_index.debugPrint( "thm-db" );
      Trace("thm-db") << std::endl;
      Trace("sg-proc") << "...done build theorem index" << std::endl;


      //clear patterns
      d_patterns.clear();
      d_pattern_var_id.clear();
      d_pattern_var_duplicate.clear();
      d_pattern_is_normal.clear();
      d_pattern_is_relevant.clear();
      d_pattern_fun_id.clear();
      d_pattern_fun_sum.clear();
      d_rel_patterns.clear();
      d_rel_pattern_var_sum.clear();
      d_rel_pattern_typ_index.clear();
      d_rel_pattern_subs_index.clear();

      unsigned rel_term_count = 0;
      std::map< TypeNode, unsigned > rt_var_max;
      std::vector< TypeNode > rt_types;
      std::map< TypeNode, std::map< int, std::vector< Node > > > conj_lhs;
      unsigned addedLemmas = 0;
      unsigned maxDepth = options::conjectureGenMaxDepth();
      for( unsigned depth=1; depth<=maxDepth; depth++ ){
        Trace("sg-proc") << "Generate relevant LHS at depth " << depth << "..." << std::endl;
        Trace("sg-rel-term") << "Relevant terms of depth " << depth << " : " << std::endl;
        //set up environment
        d_tge.d_var_id.clear();
        d_tge.d_var_limit.clear();
        d_tge.reset( depth, true, TypeNode::null() );
        while( d_tge.getNextTerm() ){
          //construct term
          Node nn = d_tge.getTerm();
          if( !options::conjectureFilterCanonical() || considerTermCanon( nn, true ) ){
            rel_term_count++;
            Trace("sg-rel-term") << "*** Relevant term : ";
            d_tge.debugPrint( "sg-rel-term", "sg-rel-term-debug2" );
            Trace("sg-rel-term") << std::endl;

            for( unsigned r=0; r<2; r++ ){
              Trace("sg-rel-term-debug") << "...from equivalence classes (" << r << ") : ";
              int index = d_tge.d_ccand_eqc[r].size()-1;
              for( unsigned j=0; j<d_tge.d_ccand_eqc[r][index].size(); j++ ){
                Trace("sg-rel-term-debug") << "e" << d_em[d_tge.d_ccand_eqc[r][index][j]] << " ";
              }
              Trace("sg-rel-term-debug") << std::endl;
            }
            TypeNode tnn = nn.getType();
            Trace("sg-gen-tg-debug") << "...term is " << nn << std::endl;
            conj_lhs[tnn][depth].push_back( nn );

            //add information about pattern
            Trace("sg-gen-tg-debug") << "Collect pattern information..." << std::endl;
            Assert(std::find(d_rel_patterns[tnn].begin(),
                             d_rel_patterns[tnn].end(),
                             nn)
                   == d_rel_patterns[tnn].end());
            d_rel_patterns[tnn].push_back( nn );
            //build information concerning the variables in this pattern
            unsigned sum = 0;
            std::map< TypeNode, unsigned > typ_to_subs_index;
            std::vector< TNode > gsubs_vars;
            for( std::map< TypeNode, unsigned >::iterator it = d_tge.d_var_id.begin(); it != d_tge.d_var_id.end(); ++it ){
              if( it->second>0 ){
                typ_to_subs_index[it->first] = sum;
                sum += it->second;
                for( unsigned i=0; i<it->second; i++ ){
                  gsubs_vars.push_back(
                      d_quantEngine->getTermCanonize()->getCanonicalFreeVar(
                          it->first, i));
                }
              }
            }
            d_rel_pattern_var_sum[nn] = sum;
            //register the pattern
            registerPattern( nn, tnn );
            Assert(d_pattern_is_normal[nn]);
            Trace("sg-gen-tg-debug") << "...done collect pattern information" << std::endl;

            //record information about types
            Trace("sg-gen-tg-debug") << "Collect type information..." << std::endl;
            PatternTypIndex * pti = &d_rel_pattern_typ_index;
            for( std::map< TypeNode, unsigned >::iterator it = d_tge.d_var_id.begin(); it != d_tge.d_var_id.end(); ++it ){
              pti = &pti->d_children[it->first][it->second];
              //record maximum
              if( rt_var_max.find( it->first )==rt_var_max.end() || it->second>rt_var_max[it->first] ){
                rt_var_max[it->first] = it->second;
              }
            }
            if( std::find( rt_types.begin(), rt_types.end(), tnn )==rt_types.end() ){
              rt_types.push_back( tnn );
            }
            pti->d_terms.push_back( nn );
            Trace("sg-gen-tg-debug") << "...done collect type information" << std::endl;

            Trace("sg-gen-tg-debug") << "Build substitutions for ground EQC..." << std::endl;
            std::vector< TNode > gsubs_terms;
            gsubs_terms.resize( gsubs_vars.size() );
            int index = d_tge.d_ccand_eqc[1].size()-1;
            for( unsigned j=0; j<d_tge.d_ccand_eqc[1][index].size(); j++ ){
              TNode r = d_tge.d_ccand_eqc[1][index][j];
              Trace("sg-rel-term-debug") << "  Matches for e" << d_em[r] << ", which is ground term " << d_ground_eqc_map[r] << ":" << std::endl;
              std::map< TypeNode, std::map< unsigned, TNode > > subs;
              std::map< TNode, bool > rev_subs;
              //only get ground terms
              unsigned mode = 2;
              d_tge.resetMatching( r, mode );
              while( d_tge.getNextMatch( r, subs, rev_subs ) ){
                //we will be building substitutions
                bool firstTime = true;
                for( std::map< TypeNode, std::map< unsigned, TNode > >::iterator it = subs.begin(); it != subs.end(); ++it ){
                  unsigned tindex = typ_to_subs_index[it->first];
                  for( std::map< unsigned, TNode >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
                    if( !firstTime ){
                      Trace("sg-rel-term-debug") << ", ";
                    }else{
                      firstTime = false;
                      Trace("sg-rel-term-debug") << "    ";
                    }
                    Trace("sg-rel-term-debug") << it->first << ":x" << it2->first << " -> " << it2->second;
                    Assert(tindex + it2->first < gsubs_terms.size());
                    gsubs_terms[tindex+it2->first] = it2->second;
                  }
                }
                Trace("sg-rel-term-debug") << std::endl;
                d_rel_pattern_subs_index[nn].addSubstitution( r, gsubs_vars, gsubs_terms );
              }
            }
            Trace("sg-gen-tg-debug") << "...done build substitutions for ground EQC" << std::endl;
          }else{
            Trace("sg-gen-tg-debug") << "> not canonical : " << nn << std::endl;
          }
        }
        Trace("sg-proc") << "...done generate terms at depth " << depth << std::endl;
        Trace("sg-stats") << "--------> Total LHS of depth " << depth << " : " << rel_term_count << std::endl;
        //Trace("conjecture-count") << "Total LHS of depth " << depth << " : " << conj_lhs[depth].size() << std::endl;

        /* test...
        for( unsigned i=0; i<rt_types.size(); i++ ){
          Trace("sg-term-enum") << "Term enumeration for " << rt_types[i] << " : " << std::endl;
          Trace("sg-term-enum") << "Ground term : " << rt_types[i].mkGroundTerm() << std::endl;
          for( unsigned j=0; j<150; j++ ){
            Trace("sg-term-enum") << "  " << getEnumerateTerm( rt_types[i], j ) << std::endl;
          }
        }
        */

        //consider types from relevant terms
        for( unsigned rdepth=0; rdepth<=depth; rdepth++ ){
          //set up environment
          d_tge.d_var_id.clear();
          d_tge.d_var_limit.clear();
          for( std::map< TypeNode, unsigned >::iterator it = rt_var_max.begin(); it != rt_var_max.end(); ++it ){
            d_tge.d_var_id[ it->first ] = it->second;
            d_tge.d_var_limit[ it->first ] = it->second;
          }
          std::shuffle(rt_types.begin(), rt_types.end(), Random::getRandom());
          std::map< TypeNode, std::vector< Node > > conj_rhs;
          for( unsigned i=0; i<rt_types.size(); i++ ){

            Trace("sg-proc") << "Generate relevant RHS terms of type " << rt_types[i] << " at depth " << rdepth << "..." << std::endl;
            d_tge.reset( rdepth, false, rt_types[i] );

            while( d_tge.getNextTerm() ){
              Node rhs = d_tge.getTerm();
              if( considerTermCanon( rhs, false ) ){
                Trace("sg-rel-prop") << "Relevant RHS : " << rhs << std::endl;
                //register pattern
                Assert(rhs.getType() == rt_types[i]);
                registerPattern( rhs, rt_types[i] );
                if( rdepth<depth ){
                  //consider against all LHS at depth
                  for( unsigned j=0; j<conj_lhs[rt_types[i]][depth].size(); j++ ){
                    processCandidateConjecture( conj_lhs[rt_types[i]][depth][j], rhs, depth, rdepth );
                  }
                }else{
                  conj_rhs[rt_types[i]].push_back( rhs );
                }
              }
            }
          }
          flushWaitingConjectures( addedLemmas, depth, rdepth );
          //consider against all LHS up to depth
          if( rdepth==depth ){
            for( unsigned lhs_depth = 1; lhs_depth<=depth; lhs_depth++ ){
              if( (int)addedLemmas<options::conjectureGenPerRound() ){
                Trace("sg-proc") << "Consider conjectures at depth (" << lhs_depth << ", " << rdepth << ")..." << std::endl;
                for( std::map< TypeNode, std::vector< Node > >::iterator it = conj_rhs.begin(); it != conj_rhs.end(); ++it ){
                  for( unsigned j=0; j<it->second.size(); j++ ){
                    for( unsigned k=0; k<conj_lhs[it->first][lhs_depth].size(); k++ ){
                      processCandidateConjecture( conj_lhs[it->first][lhs_depth][k], it->second[j], lhs_depth, rdepth );
                    }
                  }
                }
                flushWaitingConjectures( addedLemmas, lhs_depth, depth );
              }
            }
          }
          if( (int)addedLemmas>=options::conjectureGenPerRound() ){
            break;
          }
        }
        if( (int)addedLemmas>=options::conjectureGenPerRound() ){
          break;
        }
      }
      Trace("sg-stats") << "Total conjectures considered : " << d_conj_count << std::endl;
      if( Trace.isOn("thm-ee") ){
        Trace("thm-ee") << "Universal equality engine is : " << std::endl;
        eq::EqClassesIterator ueqcs_i = eq::EqClassesIterator( &d_uequalityEngine );
        while( !ueqcs_i.isFinished() ){
          TNode r = (*ueqcs_i);
          bool firstTime = true;
          Node rr = getUniversalRepresentative(r);
          Trace("thm-ee") << "  " << rr;
          Trace("thm-ee") << " : { ";
          eq::EqClassIterator ueqc_i = eq::EqClassIterator( r, &d_uequalityEngine );
          while( !ueqc_i.isFinished() ){
            TNode n = (*ueqc_i);
            if( rr!=n ){
              if( firstTime ){
                Trace("thm-ee") << std::endl;
                firstTime = false;
              }
              Trace("thm-ee") << "    " << n << std::endl;
            }
            ++ueqc_i;
          }
          if( !firstTime ){ Trace("thm-ee") << "  "; }
          Trace("thm-ee") << "}" << std::endl;
          ++ueqcs_i;
        }
        Trace("thm-ee") << std::endl;
      }
      if( Trace.isOn("sg-engine") ){
        double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
        Trace("sg-engine") << "Finished conjecture generator, time = " << (clSet2-clSet) << std::endl;
      }
    }
  }
}

unsigned ConjectureGenerator::flushWaitingConjectures( unsigned& addedLemmas, int ldepth, int rdepth ) {
  if( !d_waiting_conjectures_lhs.empty() ){
    Trace("sg-proc") << "Generated " << d_waiting_conjectures_lhs.size() << " conjectures at depth " << ldepth << "/" << rdepth << "." << std::endl;
    if( (int)addedLemmas<options::conjectureGenPerRound() ){
      /*
      std::vector< unsigned > indices;
      for( unsigned i=0; i<d_waiting_conjectures_lhs.size(); i++ ){
        indices.push_back( i );
      }
      bool doSort = false;
      if( doSort ){
        //sort them based on score
        sortConjectureScore scs;
        scs.d_scores.insert( scs.d_scores.begin(), d_waiting_conjectures_score.begin(), d_waiting_conjectures_score.end() );
        std::sort( indices.begin(), indices.end(), scs );
      }
      //if( doSort && d_waiting_conjectures_score[indices[0]]<optFilterScoreThreshold() ){
      */
      unsigned prevCount = d_conj_count;
      for( unsigned i=0; i<d_waiting_conjectures_lhs.size(); i++ ){
        if( d_waiting_conjectures_score[i]>=optFilterScoreThreshold() ){
          //we have determined a relevant subgoal
          Node lhs = d_waiting_conjectures_lhs[i];
          Node rhs = d_waiting_conjectures_rhs[i];
          if( options::conjectureFilterCanonical() && ( getUniversalRepresentative( lhs )!=lhs || getUniversalRepresentative( rhs )!=rhs ) ){
            //skip
          }else{
            Trace("sg-engine") << "*** Consider conjecture : " << lhs << " == " << rhs << std::endl;
            Trace("sg-engine-debug") << "      score : " << d_waiting_conjectures_score[i] << std::endl;
            if( optStatsOnly() ){
              d_conj_count++;
            }else{
              std::vector< Node > bvs;
              for (const std::pair<TypeNode, unsigned>& lhs_pattern :
                   d_pattern_var_id[lhs])
              {
                for (unsigned j = 0; j <= lhs_pattern.second; j++)
                {
                  bvs.push_back(getFreeVar(lhs_pattern.first, j));
                }
              }
              Node rsg;
              if( !bvs.empty() ){
                Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, bvs );
                rsg = NodeManager::currentNM()->mkNode( FORALL, bvl, lhs.eqNode( rhs ) );
              }else{
                rsg = lhs.eqNode( rhs );
              }
              rsg = Rewriter::rewrite( rsg );
              d_conjectures.push_back( rsg );
              d_eq_conjectures[lhs].push_back( rhs );
              d_eq_conjectures[rhs].push_back( lhs );

              Node lem = NodeManager::currentNM()->mkNode( OR, rsg.negate(), rsg );
              d_quantEngine->addLemma( lem, false );
              d_quantEngine->addRequirePhase( rsg, false );
              addedLemmas++;
              if( (int)addedLemmas>=options::conjectureGenPerRound() ){
                break;
              }
            }
          }
        }
      }
      Trace("sg-proc") << "...have now added " << addedLemmas << " conjecture lemmas." << std::endl;
      if( optStatsOnly() ){
        Trace("sg-stats") << "Generated " << (d_conj_count-prevCount) << " conjectures at depth " << ldepth << "/" << rdepth << "." << std::endl;
      }
    }
    d_waiting_conjectures_lhs.clear();
    d_waiting_conjectures_rhs.clear();
    d_waiting_conjectures_score.clear();
    d_waiting_conjectures.clear();
  }
  return addedLemmas;
}

bool ConjectureGenerator::considerTermCanon( Node ln, bool genRelevant ){
  if( !ln.isNull() ){
    //do not consider if it is non-canonical, and either:
    //  (1) we are not generating relevant terms, or
    //  (2) its canonical form is a generalization.
    Node lnr = getUniversalRepresentative(ln, true);
    if( lnr==ln ){
      markReportedCanon( ln );
    }else if( !genRelevant || isGeneralization( lnr, ln ) ){
      Trace("sg-gen-consider-term") << "Do not consider term, " << ln << " is not canonical representation (which is " << lnr << ")." << std::endl;
      return false;
    }
  }
  Trace("sg-gen-tg-debug") << "Will consider term canon " << ln << std::endl;
  Trace("sg-gen-consider-term-debug") << std::endl;
  return true;
}

unsigned ConjectureGenerator::collectFunctions( TNode opat, TNode pat, std::map< TNode, unsigned >& funcs,
                                             std::map< TypeNode, unsigned >& mnvn, std::map< TypeNode, unsigned >& mxvn ){
  if( pat.hasOperator() ){
    funcs[pat.getOperator()]++;
    if( !d_tge.isRelevantFunc( pat.getOperator() ) ){
      d_pattern_is_relevant[opat] = false;
    }
    unsigned sum = 1;
    for( unsigned i=0; i<pat.getNumChildren(); i++ ){
      sum += collectFunctions( opat, pat[i], funcs, mnvn, mxvn );
    }
    return sum;
  }else{
    Assert(pat.getNumChildren() == 0);
    funcs[pat]++;
    //for variables
    if( pat.getKind()==BOUND_VARIABLE ){
      if( funcs[pat]>1 ){
        //duplicate variable
        d_pattern_var_duplicate[opat]++;
      }else{
        //check for max/min
        TypeNode tn = pat.getType();
        unsigned vn = pat.getAttribute(InstVarNumAttribute());
        std::map< TypeNode, unsigned >::iterator it = mnvn.find( tn );
        if( it!=mnvn.end() ){
          if( vn<it->second ){
            d_pattern_is_normal[opat] = false;
            mnvn[tn] = vn;
          }else if( vn>mxvn[tn] ){
            if( vn!=mxvn[tn]+1 ){
              d_pattern_is_normal[opat] = false;
            }
            mxvn[tn] = vn;
          }
        }else{
          //first variable of this type
          mnvn[tn] = vn;
          mxvn[tn] = vn;
        }
      }
    }else{
      d_pattern_is_relevant[opat] = false;
    }
    return 1;
  }
}

void ConjectureGenerator::registerPattern( Node pat, TypeNode tpat ) {
  if( std::find( d_patterns[tpat].begin(), d_patterns[tpat].end(), pat )==d_patterns[tpat].end() ){
    d_patterns[TypeNode::null()].push_back( pat );
    d_patterns[tpat].push_back( pat );

    Assert(d_pattern_fun_id.find(pat) == d_pattern_fun_id.end());
    Assert(d_pattern_var_id.find(pat) == d_pattern_var_id.end());

    //collect functions
    std::map< TypeNode, unsigned > mnvn;
    d_pattern_fun_sum[pat] = collectFunctions( pat, pat, d_pattern_fun_id[pat], mnvn, d_pattern_var_id[pat] );
    if( d_pattern_is_normal.find( pat )==d_pattern_is_normal.end() ){
      d_pattern_is_normal[pat] = true;
    }
    if( d_pattern_is_relevant.find( pat )==d_pattern_is_relevant.end() ){
      d_pattern_is_relevant[pat] = true;
    }
  }
}

bool ConjectureGenerator::isGeneralization( TNode patg, TNode pat, std::map< TNode, TNode >& subs ) {
  if( patg.getKind()==BOUND_VARIABLE ){
    std::map< TNode, TNode >::iterator it = subs.find( patg );
    if( it!=subs.end() ){
      return it->second==pat;
    }else{
      subs[patg] = pat;
      return true;
    }
  }else{
    Assert(patg.hasOperator());
    if( !pat.hasOperator() || patg.getOperator()!=pat.getOperator() ){
      return false;
    }else{
      Assert(patg.getNumChildren() == pat.getNumChildren());
      for( unsigned i=0; i<patg.getNumChildren(); i++ ){
        if( !isGeneralization( patg[i], pat[i], subs ) ){
          return false;
        }
      }
      return true;
    }
  }
}

int ConjectureGenerator::calculateGeneralizationDepth( TNode n, std::vector< TNode >& fv ) {
  if( n.getKind()==BOUND_VARIABLE ){
    if( std::find( fv.begin(), fv.end(), n )==fv.end() ){
      fv.push_back( n );
      return 0;
    }else{
      return 1;
    }
  }else{
    int depth = 1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      depth += calculateGeneralizationDepth( n[i], fv );
    }
    return depth;
  }
}

Node ConjectureGenerator::getPredicateForType( TypeNode tn ) {
  std::map< TypeNode, Node >::iterator it = d_typ_pred.find( tn );
  if( it==d_typ_pred.end() ){
    TypeNode op_tn = NodeManager::currentNM()->mkFunctionType( tn, NodeManager::currentNM()->booleanType() );
    Node op = NodeManager::currentNM()->mkSkolem( "PE", op_tn, "was created by conjecture ground term enumerator." );
    d_typ_pred[tn] = op;
    return op;
  }else{
    return it->second;
  }
}

void ConjectureGenerator::getEnumerateUfTerm( Node n, unsigned num, std::vector< Node >& terms ) {
  if( n.getNumChildren()>0 ){
    Trace("sg-gt-enum-debug") << "Get enumerate uf terms " << n << " (" << num
                              << ")" << std::endl;
    TermEnumeration* te = d_quantEngine->getTermEnumeration();
    // below, we do a fair enumeration of vectors vec of indices whose sum is
    // 1,2,3, ...
    std::vector< int > vec;
    std::vector< TypeNode > types;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      vec.push_back( 0 );
      TypeNode tn = n[i].getType();
      if (tn.isClosedEnumerable())
      {
        types.push_back( tn );
      }else{
        return;
      }
    }
    // the index of the last child is determined by the limit of the sum
    // of indices of children (size_limit) and the sum of the indices of the
    // other children (vec_sum). Hence, we pop here and add this value at each
    // iteration of the loop.
    vec.pop_back();
    int size_limit = 0;
    int vec_sum = -1;
    unsigned index = 0;
    unsigned last_size = terms.size();
    while( terms.size()<num ){
      if( vec_sum==-1 ){
        vec_sum = 0;
        // we will construct a new child below
        // since sum is 0, the index of last child is limit
        vec.push_back( size_limit );
      }
      else if (index < vec.size())
      {
        Assert(index < types.size());
        //see if we can iterate current
        if (vec_sum < size_limit
            && !te->getEnumerateTerm(types[index], vec[index] + 1).isNull())
        {
          vec[index]++;
          vec_sum++;
          // we will construct a new child below
          // add the index of the last child, its index is (limit-sum)
          vec.push_back( size_limit - vec_sum );
        }else{
          // reset the index
          vec_sum -= vec[index];
          vec[index] = 0;
          index++;
        }
      }
      if (index < vec.size())
      {
        // if we are ready to construct the term
        if( vec.size()==n.getNumChildren() ){
          Node lc =
              te->getEnumerateTerm(types[vec.size() - 1], vec[vec.size() - 1]);
          if( !lc.isNull() ){
            for( unsigned i=0; i<vec.size(); i++ ){
              Trace("sg-gt-enum-debug") << vec[i] << " ";
            }
            Trace("sg-gt-enum-debug") << " / " << size_limit << std::endl;
            for( unsigned i=0; i<n.getNumChildren(); i++ ){
              Trace("sg-gt-enum-debug") << n[i].getType() << " ";
            }
            Trace("sg-gt-enum-debug") << std::endl;
            std::vector< Node > children;
            children.push_back( n.getOperator() );
            for( unsigned i=0; i<(vec.size()-1); i++ ){
              Node nn = te->getEnumerateTerm(types[i], vec[i]);
              Assert(!nn.isNull());
              Assert(nn.getType() == n[i].getType());
              children.push_back( nn );
            }
            children.push_back( lc );
            Node nenum = NodeManager::currentNM()->mkNode(APPLY_UF, children);
            Trace("sg-gt-enum")
                << "Ground term enumerate : " << nenum << std::endl;
            terms.push_back(nenum);
          }
          // pop the index for the last child
          vec.pop_back();
          index = 0;
        }
      }else{
        // no more indices to increment, we reset and increment size_limit
        if( terms.size()>last_size ){
          last_size = terms.size();
          size_limit++;
          for( unsigned i=0; i<vec.size(); i++ ){
            vec[i] = 0;
          }
          vec_sum = -1;
        }else{
          // No terms were generated at the previous size.
          // Thus, we've saturated, no more terms can be enumerated.
          return;
        }
      }
    }
  }else{
    terms.push_back( n );
  }
}

void ConjectureGenerator::getEnumeratePredUfTerm( Node n, unsigned num, std::vector< Node >& terms ) {
  std::vector< Node > uf_terms;
  getEnumerateUfTerm( n, num, uf_terms );
  Node p = getPredicateForType( n.getType() );
  for( unsigned i=0; i<uf_terms.size(); i++ ){
    terms.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, p, uf_terms[i] ) );
  }
}

void ConjectureGenerator::processCandidateConjecture( TNode lhs, TNode rhs, unsigned lhs_depth, unsigned rhs_depth ) {
  int score = considerCandidateConjecture( lhs, rhs );
  if( score>0 ){
    Trace("sg-conjecture") << "* Candidate conjecture : " << lhs << " == " << rhs << std::endl;
    Trace("sg-conjecture-debug") << "     LHS, RHS generalization depth : " << lhs_depth << ", " << rhs_depth << std::endl;
    Trace("sg-conjecture-debug") << "     confirmed = " << d_subs_confirmCount << ", #witnesses range = " << d_subs_confirmWitnessRange.size() << "." << std::endl;
    Trace("sg-conjecture-debug") << "     #witnesses for ";
    bool firstTime = true;
    for( std::map< TNode, std::vector< TNode > >::iterator it = d_subs_confirmWitnessDomain.begin(); it != d_subs_confirmWitnessDomain.end(); ++it ){
      if( !firstTime ){
        Trace("sg-conjecture-debug") << ", ";
      }
      Trace("sg-conjecture-debug") << it->first << " : " << it->second.size();
      //if( it->second.size()==1 ){
      //  Trace("sg-conjecture-debug") << " (" << it->second[0] << ")";
      //}
      Trace("sg-conjecture-debug2") << " (";
      for( unsigned j=0; j<it->second.size(); j++ ){
        if( j>0 ){ Trace("sg-conjecture-debug2") << " "; }
        Trace("sg-conjecture-debug2") << d_ground_eqc_map[it->second[j]];
      }
      Trace("sg-conjecture-debug2") << ")";
      firstTime = false;
    }
    Trace("sg-conjecture-debug") << std::endl;
    Trace("sg-conjecture-debug") << "     unknown = " << d_subs_unkCount << std::endl;
    //Assert( getUniversalRepresentative( rhs )==rhs );
    //Assert( getUniversalRepresentative( lhs )==lhs );
    d_waiting_conjectures_lhs.push_back( lhs );
    d_waiting_conjectures_rhs.push_back( rhs );
    d_waiting_conjectures_score.push_back( score );
    d_waiting_conjectures[lhs].push_back( rhs );
    d_waiting_conjectures[rhs].push_back( lhs );
  }else{
    Trace("sg-conjecture-debug2") << "...do not consider " << lhs << " == " << rhs << ", score = " << score << std::endl;
  }
}

int ConjectureGenerator::considerCandidateConjecture( TNode lhs, TNode rhs ) {
  Assert(lhs.getType() == rhs.getType());

  Trace("sg-cconj-debug") << "Consider candidate conjecture : " << lhs << " == " << rhs << "?" << std::endl;
  if( lhs==rhs ){
    Trace("sg-cconj-debug") << "  -> trivial." << std::endl;
    return -1;
  }else{
    if( lhs.getKind()==APPLY_CONSTRUCTOR && rhs.getKind()==APPLY_CONSTRUCTOR ){
      Trace("sg-cconj-debug") << "  -> irrelevant by syntactic analysis." << std::endl;
      return -1;
    }
    //variables of LHS must subsume variables of RHS
    for( std::map< TypeNode, unsigned >::iterator it = d_pattern_var_id[rhs].begin(); it != d_pattern_var_id[rhs].end(); ++it ){
      std::map< TypeNode, unsigned >::iterator itl = d_pattern_var_id[lhs].find( it->first );
      if( itl!=d_pattern_var_id[lhs].end() ){
        if( itl->second<it->second ){
          Trace("sg-cconj-debug") << "  -> variables of sort " << it->first << " are not subsumed." << std::endl;
          return -1;
        }else{
          Trace("sg-cconj-debug2") << "  variables of sort " << it->first << " are : " << itl->second << " vs " << it->second << std::endl;
        }
      }else{
        Trace("sg-cconj-debug") << "  -> has no variables of sort " << it->first << "." << std::endl;
        return -1;
      }
    }

    //currently active conjecture?
    std::map< Node, std::vector< Node > >::iterator iteq = d_eq_conjectures.find( lhs );
    if( iteq!=d_eq_conjectures.end() ){
      if( std::find( iteq->second.begin(), iteq->second.end(), rhs )!=iteq->second.end() ){
        Trace("sg-cconj-debug") << "  -> this conjecture is already active." << std::endl;
        return -1;
      }
    }
    //current a waiting conjecture?
    std::map< Node, std::vector< Node > >::iterator itw = d_waiting_conjectures.find( lhs );
    if( itw!=d_waiting_conjectures.end() ){
      if( std::find( itw->second.begin(), itw->second.end(), rhs )!=itw->second.end() ){
        Trace("sg-cconj-debug") << "  -> already are considering this conjecture." << std::endl;
        return -1;
      }
    }
    //check if canonical representation (should be, but for efficiency this is not guarenteed)
    //if( options::conjectureFilterCanonical() && ( getUniversalRepresentative( lhs )!=lhs || getUniversalRepresentative( rhs )!=rhs ) ){
    //  Trace("sg-cconj") << "  -> after processing, not canonical." << std::endl;
    //  return -1;
    //}

    int score;
    bool scoreSet = false;

    Trace("sg-cconj") << "Consider possible candidate conjecture : " << lhs << " == " << rhs << "?" << std::endl;
    //find witness for counterexample, if possible
    if( options::conjectureFilterModel() ){
      Assert(d_rel_pattern_var_sum.find(lhs) != d_rel_pattern_var_sum.end());
      Trace("sg-cconj-debug") << "Notify substitutions over " << d_rel_pattern_var_sum[lhs] << " variables." << std::endl;
      std::map< TNode, TNode > subs;
      d_subs_confirmCount = 0;
      d_subs_confirmWitnessRange.clear();
      d_subs_confirmWitnessDomain.clear();
      d_subs_unkCount = 0;
      if( !d_rel_pattern_subs_index[lhs].notifySubstitutions( this, subs, rhs, d_rel_pattern_var_sum[lhs] ) ){
        Trace("sg-cconj") << "  -> found witness that falsifies the conjecture." << std::endl;
        return -1;
      }
      //score is the minimum number of distinct substitutions for a variable
      for( std::map< TNode, std::vector< TNode > >::iterator it = d_subs_confirmWitnessDomain.begin(); it != d_subs_confirmWitnessDomain.end(); ++it ){
        int num = (int)it->second.size();
        if( !scoreSet || num<score ){
          score = num;
          scoreSet = true;
        }
      }
      if( !scoreSet ){
        score = 0;
      }
      Trace("sg-cconj") << "     confirmed = " << d_subs_confirmCount << ", #witnesses range = " << d_subs_confirmWitnessRange.size() << "." << std::endl;
      for( std::map< TNode, std::vector< TNode > >::iterator it = d_subs_confirmWitnessDomain.begin(); it != d_subs_confirmWitnessDomain.end(); ++it ){
        Trace("sg-cconj") << "     #witnesses for " << it->first << " : " << it->second.size() << std::endl;
      }
    }else{
      score = 1;
    }

    Trace("sg-cconj") << "  -> SUCCESS." << std::endl;
    Trace("sg-cconj") << "     score : " << score << std::endl;

    return score;
  }
}

bool ConjectureGenerator::notifySubstitution( TNode glhs, std::map< TNode, TNode >& subs, TNode rhs ) {
  if( Trace.isOn("sg-cconj-debug") ){
    Trace("sg-cconj-debug") << "Ground eqc for LHS : " << glhs << ", based on substituion: " << std::endl;
    for( std::map< TNode, TNode >::iterator it = subs.begin(); it != subs.end(); ++it ){
      Assert(getRepresentative(it->second) == it->second);
      Trace("sg-cconj-debug") << "  " << it->first << " -> " << it->second << std::endl;
    }
  }
  Trace("sg-cconj-debug") << "Evaluate RHS : : " << rhs << std::endl;
  //get the representative of rhs with substitution subs
  TNode grhs = getTermDatabase()->getEntailedTerm( rhs, subs, true );
  Trace("sg-cconj-debug") << "...done evaluating term, got : " << grhs << std::endl;
  if( !grhs.isNull() ){
    if( glhs!=grhs ){
      Trace("sg-cconj-debug") << "Ground eqc for RHS : " << grhs << std::endl;
      //check based on ground terms
      std::map< TNode, Node >::iterator itl = d_ground_eqc_map.find( glhs );
      if( itl!=d_ground_eqc_map.end() ){
        std::map< TNode, Node >::iterator itr = d_ground_eqc_map.find( grhs );
        if( itr!=d_ground_eqc_map.end() ){
          Trace("sg-cconj-debug") << "We have ground terms " << itl->second << " and " << itr->second << "." << std::endl;
          if( itl->second.isConst() && itr->second.isConst() ){
            Trace("sg-cconj-debug") << "...disequal constants." << std::endl;
            Trace("sg-cconj-witness") << "  Witness of falsification : " << itl->second << " != " << itr->second << ", substutition is : " << std::endl;
            for( std::map< TNode, TNode >::iterator it = subs.begin(); it != subs.end(); ++it ){
              Trace("sg-cconj-witness") << "    " << it->first << " -> " << it->second << std::endl;
            }
            return false;
          }
        }
      }
    }
    Trace("sg-cconj-debug") << "RHS is identical." << std::endl;
    bool isGroundSubs = true;
    for( std::map< TNode, TNode >::iterator it = subs.begin(); it != subs.end(); ++it ){
      std::map< TNode, Node >::iterator git = d_ground_eqc_map.find( it->second );
      if( git==d_ground_eqc_map.end() ){
        isGroundSubs = false;
        break;
      }
    }
    if( isGroundSubs ){
      if( glhs==grhs ){
        Trace("sg-cconj-witness") << "  Witnessed " << glhs << " == " << grhs << ", substutition is : " << std::endl;
        for( std::map< TNode, TNode >::iterator it = subs.begin(); it != subs.end(); ++it ){
          Trace("sg-cconj-witness") << "    " << it->first << " -> " << it->second << std::endl;
          if( std::find( d_subs_confirmWitnessDomain[it->first].begin(), d_subs_confirmWitnessDomain[it->first].end(), it->second )==d_subs_confirmWitnessDomain[it->first].end() ){
            d_subs_confirmWitnessDomain[it->first].push_back( it->second );
          }
        }
        d_subs_confirmCount++;
        if( std::find( d_subs_confirmWitnessRange.begin(), d_subs_confirmWitnessRange.end(), glhs )==d_subs_confirmWitnessRange.end() ){
          d_subs_confirmWitnessRange.push_back( glhs );
        }
      }else{
        if( optFilterUnknown() ){
          Trace("sg-cconj-debug") << "...ground substitution giving terms that are neither equal nor disequal." << std::endl;
          return false;
        }
      }
    }
  }else{
    Trace("sg-cconj-debug") << "(could not ground eqc for RHS)." << std::endl;
  }
  return true;
}






void TermGenerator::reset( TermGenEnv * s, TypeNode tn ) {
  Assert(d_children.empty());
  d_typ = tn;
  d_status = 0;
  d_status_num = 0;
  d_children.clear();
  Trace("sg-gen-tg-debug2") << "...add to context " << this << std::endl;
  d_id = s->d_tg_id;
  s->changeContext( true );
}

bool TermGenerator::getNextTerm( TermGenEnv * s, unsigned depth ) {
  if( Trace.isOn("sg-gen-tg-debug2") ){
    Trace("sg-gen-tg-debug2") << this << " getNextTerm depth " << depth << " : status = " << d_status << ", num = " << d_status_num;
    if( d_status==5 ){
      TNode f = s->getTgFunc( d_typ, d_status_num );
      Trace("sg-gen-tg-debug2") << ", f = " << f;
      Trace("sg-gen-tg-debug2") << ", #args = " << s->d_func_args[f].size();
      Trace("sg-gen-tg-debug2") << ", childNum = " << d_status_child_num;
      Trace("sg-gen-tg-debug2") << ", #children = " << d_children.size();
    }
    Trace("sg-gen-tg-debug2") << std::endl;
  }

  if( d_status==0 ){
    d_status++;
    if( !d_typ.isNull() ){
      if( s->allowVar( d_typ ) ){
        //allocate variable
        d_status_num = s->d_var_id[d_typ];
        s->addVar( d_typ );
        Trace("sg-gen-tg-debug2") << this << " ...return unique var #" << d_status_num << std::endl;
        return s->considerCurrentTerm() ? true : getNextTerm( s, depth );
      }else{
        //check allocating new variable
        d_status++;
        d_status_num = -1;
        if( s->d_gen_relevant_terms ){
          s->d_tg_gdepth++;
        }
        return getNextTerm( s, depth );
      }
    }else{
      d_status = 4;
      d_status_num = -1;
      return getNextTerm( s, depth );
    }
  }else if( d_status==2 ){
    //cleanup previous information
    //if( d_status_num>=0 ){
    //  s->d_var_eq_tg[d_status_num].pop_back();
    //}
    //check if there is another variable
    if( (d_status_num+1)<(int)s->getNumTgVars( d_typ ) ){
      d_status_num++;
      //we have equated two variables
      //s->d_var_eq_tg[d_status_num].push_back( d_id );
      Trace("sg-gen-tg-debug2") << this << "...consider other var #" << d_status_num << std::endl;
      return s->considerCurrentTerm() ? true : getNextTerm( s, depth );
    }else{
      if( s->d_gen_relevant_terms ){
        s->d_tg_gdepth--;
      }
      d_status++;
      return getNextTerm( s, depth );
    }
  }else if( d_status==4 ){
    d_status++;
    if( depth>0 && (d_status_num+1)<(int)s->getNumTgFuncs( d_typ ) ){
      d_status_num++;
      d_status_child_num = 0;
      Trace("sg-gen-tg-debug2") << this << "...consider function " << s->getTgFunc( d_typ, d_status_num ) << std::endl;
      s->d_tg_gdepth++;
      if( !s->considerCurrentTerm() ){
        s->d_tg_gdepth--;
        //don't consider this function
        d_status--;
      }else{
        //we have decided on a function application
      }
      return getNextTerm( s, depth );
    }else{
      //do not choose function applications at depth 0
      d_status++;
      return getNextTerm( s, depth );
    }
  }else if( d_status==5 ){
    //iterating over arguments
    TNode f = s->getTgFunc( d_typ, d_status_num );
    if( d_status_child_num<0 ){
      //no more arguments
      s->d_tg_gdepth--;
      d_status--;
      return getNextTerm( s, depth );
    }else if( d_status_child_num==(int)s->d_func_args[f].size() ){
      d_status_child_num--;
      return s->considerCurrentTermCanon( d_id ) ? true : getNextTerm( s, depth );
      //return true;
    }else{
      Assert(d_status_child_num < (int)s->d_func_args[f].size());
      if( d_status_child_num==(int)d_children.size() ){
        d_children.push_back( s->d_tg_id );
        Assert(s->d_tg_alloc.find(s->d_tg_id) == s->d_tg_alloc.end());
        s->d_tg_alloc[d_children[d_status_child_num]].reset( s, s->d_func_args[f][d_status_child_num] );
        return getNextTerm( s, depth );
      }else{
        Assert(d_status_child_num + 1 == (int)d_children.size());
        if( s->d_tg_alloc[d_children[d_status_child_num]].getNextTerm( s, depth-1 ) ){
          d_status_child_num++;
          return getNextTerm( s, depth );
        }else{
          Trace("sg-gen-tg-debug2")
              << "...remove child from context " << std::endl;
          s->changeContext(false);
          d_children.pop_back();
          d_status_child_num--;
          return getNextTerm( s, depth );
        }
      }
    }
  }else if( d_status==1 || d_status==3 ){
    if( d_status==1 ){
      s->removeVar( d_typ );
      Assert(d_status_num == (int)s->d_var_id[d_typ]);
      //check if there is only one feasible equivalence class.  if so, don't make pattern any more specific.
      //unsigned i = s->d_ccand_eqc[0].size()-1;
      //if( s->d_ccand_eqc[0][i].size()==1 && s->d_ccand_eqc[1][i].empty() ){
      //  d_status = 6;
      //  return getNextTerm( s, depth );
      //}
      s->d_tg_gdepth++;
    }
    d_status++;
    d_status_num = -1;
    return getNextTerm( s, depth );
  }else{
    Assert(d_children.empty());
    return false;
  }
}

void TermGenerator::resetMatching( TermGenEnv * s, TNode eqc, unsigned mode ) {
  d_match_status = 0;
  d_match_status_child_num = 0;
  d_match_children.clear();
  d_match_children_end.clear();
  d_match_mode = mode;
  //if this term generalizes, it must generalize a non-ground term
  //if( (d_match_mode & ( 1 << 2 ))!=0 && s->isGroundEqc( eqc ) && d_status==5 ){
  //  d_match_status = -1;
  //}
}

bool TermGenerator::getNextMatch( TermGenEnv * s, TNode eqc, std::map< TypeNode, std::map< unsigned, TNode > >& subs, std::map< TNode, bool >& rev_subs ) {
  if( d_match_status<0 ){
    return false;
  }
  if( Trace.isOn("sg-gen-tg-match") ){
    Trace("sg-gen-tg-match") << "Matching ";
    debugPrint( s, "sg-gen-tg-match", "sg-gen-tg-match" );
    Trace("sg-gen-tg-match") << " with eqc e" << s->d_cg->d_em[eqc] << "..." << std::endl;
    Trace("sg-gen-tg-match") << "   mstatus = " << d_match_status;
    if( d_status==5 ){
      TNode f = s->getTgFunc( d_typ, d_status_num );
      Trace("sg-gen-tg-debug2") << ", f = " << f;
      Trace("sg-gen-tg-debug2") << ", #args = " << s->d_func_args[f].size();
      Trace("sg-gen-tg-debug2") << ", mchildNum = " << d_match_status_child_num;
      Trace("sg-gen-tg-debug2") << ", #mchildren = " << d_match_children.size();
    }
    Trace("sg-gen-tg-debug2") << ", current substitution : {";
    for( std::map< TypeNode, std::map< unsigned, TNode > >::iterator itt = subs.begin(); itt != subs.end(); ++itt ){
      for( std::map< unsigned, TNode >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
        Trace("sg-gen-tg-debug2")  << " " << it->first << " -> e" << s->d_cg->d_em[it->second];
      }
    }
    Trace("sg-gen-tg-debug2") << " } " << std::endl;
  }
  if( d_status==1 ){
    //a variable
    if( d_match_status==0 ){
      d_match_status++;
      if( (d_match_mode & ( 1 << 1 ))!=0 ){
        //only ground terms
        if( !s->isGroundEqc( eqc ) ){
          return false;
        }
      }else if( (d_match_mode & ( 1 << 2 ))!=0 ){
        //only non-ground terms
        //if( s->isGroundEqc( eqc ) ){
        //  return false;
        //}
      }
      //store the match : restricted if match_mode.0 = 1
      if( (d_match_mode & ( 1 << 0 ))!=0 ){
        std::map< TNode, bool >::iterator it = rev_subs.find( eqc );
        if( it==rev_subs.end() ){
          rev_subs[eqc] = true;
        }else{
          return false;
        }
      }
      Assert(subs[d_typ].find(d_status_num) == subs[d_typ].end());
      subs[d_typ][d_status_num] = eqc;
      return true;
    }else{
      //clean up
      subs[d_typ].erase( d_status_num );
      if( (d_match_mode & ( 1 << 0 ))!=0 ){
        rev_subs.erase( eqc );
      }
      return false;
    }
  }else if( d_status==2 ){
    if( d_match_status==0 ){
      d_match_status++;
      Assert(d_status_num < (int)s->getNumTgVars(d_typ));
      std::map< unsigned, TNode >::iterator it = subs[d_typ].find( d_status_num );
      Assert(it != subs[d_typ].end());
      return it->second==eqc;
    }else{
      return false;
    }
  }else if( d_status==5 ){
    //Assert( d_match_children.size()<=d_children.size() );
    //enumerating over f-applications in eqc
    if( d_match_status_child_num<0 ){
      return false;
    }else if( d_match_status==0 ){
      //set up next binding
      if( d_match_status_child_num==(int)d_match_children.size() ){
        if( d_match_status_child_num==0 ){
          //initial binding
          TNode f = s->getTgFunc( d_typ, d_status_num );
          Assert(!eqc.isNull());
          TNodeTrie* tat = s->getTermDatabase()->getTermArgTrie(eqc, f);
          if( tat ){
            d_match_children.push_back( tat->d_data.begin() );
            d_match_children_end.push_back( tat->d_data.end() );
          }else{
            d_match_status++;
            d_match_status_child_num--;
            return getNextMatch( s, eqc, subs, rev_subs );
          }
        }else{
          d_match_children.push_back( d_match_children[d_match_status_child_num-1]->second.d_data.begin() );
          d_match_children_end.push_back( d_match_children[d_match_status_child_num-1]->second.d_data.end() );
        }
      }
      d_match_status++;
      Assert(d_match_status_child_num + 1 == (int)d_match_children.size());
      if( d_match_children[d_match_status_child_num]==d_match_children_end[d_match_status_child_num] ){
        //no more arguments to bind
        d_match_children.pop_back();
        d_match_children_end.pop_back();
        d_match_status_child_num--;
        return getNextMatch( s, eqc, subs, rev_subs );
      }else{
        if( d_match_status_child_num==(int)d_children.size() ){
          //successfully matched all children
          d_match_children.pop_back();
          d_match_children_end.pop_back();
          d_match_status_child_num--;
          return true;//return d_match_children[d_match_status]!=d_match_children_end[d_match_status];
        }else{
          //do next binding
          s->d_tg_alloc[d_children[d_match_status_child_num]].resetMatching( s, d_match_children[d_match_status_child_num]->first, d_match_mode );
          return getNextMatch( s, eqc, subs, rev_subs );
        }
      }
    }else{
      Assert(d_match_status == 1);
      Assert(d_match_status_child_num + 1 == (int)d_match_children.size());
      Assert(d_match_children[d_match_status_child_num]
             != d_match_children_end[d_match_status_child_num]);
      d_match_status--;
      if( s->d_tg_alloc[d_children[d_match_status_child_num]].getNextMatch( s, d_match_children[d_match_status_child_num]->first, subs, rev_subs ) ){
        d_match_status_child_num++;
        return getNextMatch( s, eqc, subs, rev_subs );
      }else{
        //iterate
        d_match_children[d_match_status_child_num]++;
        return getNextMatch( s, eqc, subs, rev_subs );
      }
    }
  }
  Assert(false);
  return false;
}

unsigned TermGenerator::getDepth( TermGenEnv * s ) {
  if( d_status==5 ){
    unsigned maxd = 0;
    for( unsigned i=0; i<d_children.size(); i++ ){
      unsigned d = s->d_tg_alloc[d_children[i]].getDepth( s );
      if( d>maxd ){
        maxd = d;
      }
    }
    return 1+maxd;
  }else{
    return 0;
  }
}

unsigned TermGenerator::calculateGeneralizationDepth( TermGenEnv * s, std::map< TypeNode, std::vector< int > >& fvs ) {
  if( d_status==5 ){
    unsigned sum = 1;
    for( unsigned i=0; i<d_children.size(); i++ ){
      sum += s->d_tg_alloc[d_children[i]].calculateGeneralizationDepth( s, fvs );
    }
    return sum;
  }else{
    Assert(d_status == 2 || d_status == 1);
    std::map< TypeNode, std::vector< int > >::iterator it = fvs.find( d_typ );
    if( it!=fvs.end() ){
      if( std::find( it->second.begin(), it->second.end(), d_status_num )!=it->second.end() ){
        return 1;
      }
    }
    fvs[d_typ].push_back( d_status_num );
    return 0;
  }
}

unsigned TermGenerator::getGeneralizationDepth( TermGenEnv * s ) {
  //if( s->d_gen_relevant_terms ){
  //  return s->d_tg_gdepth;
  //}else{
    std::map< TypeNode, std::vector< int > > fvs;
    return calculateGeneralizationDepth( s, fvs );
  //}
}

Node TermGenerator::getTerm( TermGenEnv * s ) {
  if( d_status==1 || d_status==2 ){
    Assert(!d_typ.isNull());
    return s->getFreeVar( d_typ, d_status_num );
  }else if( d_status==5 ){
    Node f = s->getTgFunc( d_typ, d_status_num );
    if( d_children.size()==s->d_func_args[f].size() ){
      std::vector< Node > children;
      if( s->d_tg_func_param[f] ){
        children.push_back( f );
      }
      for( unsigned i=0; i<d_children.size(); i++ ){
        Node nc = s->d_tg_alloc[d_children[i]].getTerm( s );
        if( nc.isNull() ){
          return Node::null();
        }else{
          //Assert( nc.getType()==s->d_func_args[f][i] );
          children.push_back( nc );
        }
      }
      return NodeManager::currentNM()->mkNode( s->d_func_kind[f], children );
    }
  }else{
    Assert(false);
  }
  return Node::null();
}

void TermGenerator::debugPrint( TermGenEnv * s, const char * c, const char * cd ) {
  Trace(cd) << "[*" << d_id << "," << d_status << "]:";
  if( d_status==1 || d_status==2 ){
    Trace(c) << s->getFreeVar( d_typ, d_status_num );
  }else if( d_status==5 ){
    TNode f = s->getTgFunc( d_typ, d_status_num );
    Trace(c) << "(" << f;
    for( unsigned i=0; i<d_children.size(); i++ ){
      Trace(c) << " ";
       s->d_tg_alloc[d_children[i]].debugPrint( s, c, cd );
    }
    if( d_children.size()<s->d_func_args[f].size() ){
      Trace(c) << " ...";
    }
    Trace(c) << ")";
  }else{
    Trace(c) << "???";
  }
}

void TermGenEnv::collectSignatureInformation() {
  d_typ_tg_funcs.clear();
  d_funcs.clear();
  d_func_kind.clear();
  d_func_args.clear();
  TypeNode tnull;
  for( std::map< Node, std::vector< Node > >::iterator it = getTermDatabase()->d_op_map.begin(); it != getTermDatabase()->d_op_map.end(); ++it ){
    if( !it->second.empty() ){
      Node nn = it->second[0];
      Trace("sg-rel-sig-debug") << "Check in signature : " << nn << std::endl;
      if( d_cg->isHandledTerm( nn ) && nn.getKind()!=APPLY_SELECTOR_TOTAL && !nn.getType().isBoolean() ){
        bool do_enum = true;
        //check if we have enumerated ground terms
        if( nn.getKind()==APPLY_UF ){
          Trace("sg-rel-sig-debug") << "Check enumeration..." << std::endl;
          if( !d_cg->hasEnumeratedUf( nn ) ){
            do_enum = false;
          }
        }
        if( do_enum ){
          Trace("sg-rel-sig-debug") << "Set enumeration..." << std::endl;
          d_funcs.push_back( it->first );
          for( unsigned i=0; i<nn.getNumChildren(); i++ ){
            d_func_args[it->first].push_back( nn[i].getType() );
          }
          d_func_kind[it->first] = nn.getKind();
          d_typ_tg_funcs[tnull].push_back( it->first );
          d_typ_tg_funcs[nn.getType()].push_back( it->first );
          d_tg_func_param[it->first] = ( nn.getMetaKind() == kind::metakind::PARAMETERIZED );
          Trace("sg-rel-sig") << "Will enumerate function applications of : " << it->first << ", #args = " << d_func_args[it->first].size() << ", kind = " << nn.getKind() << std::endl;
          //getTermDatabase()->computeUfEqcTerms( it->first );
        }
      }
      Trace("sg-rel-sig-debug") << "Done check in signature : " << nn << std::endl;
    }
  }
  //shuffle functions
  for (std::map<TypeNode, std::vector<TNode> >::iterator it =
           d_typ_tg_funcs.begin();
       it != d_typ_tg_funcs.end();
       ++it)
  {
    std::shuffle(it->second.begin(), it->second.end(), Random::getRandom());
    if (it->first.isNull())
    {
      Trace("sg-gen-tg-debug") << "In this order : ";
      for (unsigned i = 0; i < it->second.size(); i++)
      {
        Trace("sg-gen-tg-debug") << it->second[i] << " ";
      }
      Trace("sg-gen-tg-debug") << std::endl;
    }
  }
}

void TermGenEnv::reset( unsigned depth, bool genRelevant, TypeNode tn ) {
  Assert(d_tg_alloc.empty());
  d_tg_alloc.clear();

  if( genRelevant ){
    for( unsigned i=0; i<2; i++ ){
      d_ccand_eqc[i].clear();
      d_ccand_eqc[i].push_back( d_relevant_eqc[i] );
    }
  }

  d_tg_id = 0;
  d_tg_gdepth = 0;
  d_tg_gdepth_limit = depth;
  d_gen_relevant_terms = genRelevant;
  d_tg_alloc[0].reset( this, tn );
}

bool TermGenEnv::getNextTerm() {
  if( d_tg_alloc[0].getNextTerm( this, d_tg_gdepth_limit ) ){
    Assert((int)d_tg_alloc[0].getGeneralizationDepth(this)
           <= d_tg_gdepth_limit);
    if( (int)d_tg_alloc[0].getGeneralizationDepth( this )!=d_tg_gdepth_limit ){
      return getNextTerm();
    }else{
      return true;
    }
  }
  Trace("sg-gen-tg-debug2") << "...remove from context " << std::endl;
  changeContext(false);
  return false;
}

//reset matching
void TermGenEnv::resetMatching( TNode eqc, unsigned mode ) {
  d_tg_alloc[0].resetMatching( this, eqc, mode );
}

//get next match
bool TermGenEnv::getNextMatch( TNode eqc, std::map< TypeNode, std::map< unsigned, TNode > >& subs, std::map< TNode, bool >& rev_subs ) {
  return d_tg_alloc[0].getNextMatch( this, eqc, subs, rev_subs );
}

//get term
Node TermGenEnv::getTerm() {
  return d_tg_alloc[0].getTerm( this );
}

void TermGenEnv::debugPrint( const char * c, const char * cd ) {
  d_tg_alloc[0].debugPrint( this, c, cd );
}

unsigned TermGenEnv::getNumTgVars( TypeNode tn ) {
  return d_var_id[tn];
}

bool TermGenEnv::allowVar( TypeNode tn ) {
  std::map< TypeNode, unsigned >::iterator it = d_var_limit.find( tn );
  if( it==d_var_limit.end() ){
    return true;
  }else{
    return d_var_id[tn]<it->second;
  }
}

void TermGenEnv::addVar( TypeNode tn ) {
  d_var_id[tn]++;
}

void TermGenEnv::removeVar( TypeNode tn ) {
  d_var_id[tn]--;
  //d_var_eq_tg.pop_back();
  //d_var_tg.pop_back();
}

unsigned TermGenEnv::getNumTgFuncs( TypeNode tn ) {
  return d_typ_tg_funcs[tn].size();
}

TNode TermGenEnv::getTgFunc( TypeNode tn, unsigned i ) {
  return d_typ_tg_funcs[tn][i];
}

Node TermGenEnv::getFreeVar( TypeNode tn, unsigned i ) {
  return d_cg->getFreeVar( tn, i );
}

bool TermGenEnv::considerCurrentTerm() {
  Assert(!d_tg_alloc.empty());

  //if generalization depth is too large, don't consider it
  unsigned i = d_tg_alloc.size();
  Trace("sg-gen-tg-debug") << "Consider term ";
  d_tg_alloc[0].debugPrint( this, "sg-gen-tg-debug", "sg-gen-tg-debug" );
  Trace("sg-gen-tg-debug") << "?  curr term size = " << d_tg_alloc.size() << ", last status = " << d_tg_alloc[i-1].d_status;
  Trace("sg-gen-tg-debug") << std::endl;

  if( d_tg_gdepth_limit>=0 && d_tg_alloc[0].getGeneralizationDepth( this )>(unsigned)d_tg_gdepth_limit ){
    Trace("sg-gen-consider-term") << "-> generalization depth of ";
    d_tg_alloc[0].debugPrint( this, "sg-gen-consider-term", "sg-gen-tg-debug" );
    Trace("sg-gen-consider-term") << " is too high " << d_tg_gdepth << " " << d_tg_alloc[0].getGeneralizationDepth( this ) << ", do not consider." << std::endl;
    return false;
  }

  //----optimizations
  /*
  if( d_tg_alloc[i-1].d_status==1 ){
  }else if( d_tg_alloc[i-1].d_status==2 ){
  }else if( d_tg_alloc[i-1].d_status==5 ){
  }else{
    Trace("sg-gen-tg-debug") << "Bad tg: " << &d_tg_alloc[i-1] << std::endl;
    Assert( false );
  }
  */
  //if equated two variables, first check if context-independent TODO
  //----end optimizations


  //check based on which candidate equivalence classes match
  if( d_gen_relevant_terms ){
    Trace("sg-gen-tg-debug") << "Filter based on relevant ground EQC";
    Trace("sg-gen-tg-debug") << ", #eqc to try = " << d_ccand_eqc[0][i-1].size() << "/" << d_ccand_eqc[1][i-1].size() << std::endl;

    Assert(d_ccand_eqc[0].size() >= 2);
    Assert(d_ccand_eqc[0].size() == d_ccand_eqc[1].size());
    Assert(d_ccand_eqc[0].size() == d_tg_id + 1);
    Assert(d_tg_id == d_tg_alloc.size());
    for( unsigned r=0; r<2; r++ ){
      d_ccand_eqc[r][i].clear();
    }

    //re-check feasibility of EQC
    for( unsigned r=0; r<2; r++ ){
      for( unsigned j=0; j<d_ccand_eqc[r][i-1].size(); j++ ){
        std::map< TypeNode, std::map< unsigned, TNode > > subs;
        std::map< TNode, bool > rev_subs;
        unsigned mode;
        if( r==0 ){
          mode = d_cg->optReqDistinctVarPatterns() ? ( 1 << 0 ) : 0;
          mode = mode | (1 << 2 );
        }else{
          mode =  1 << 1;
        }
        d_tg_alloc[0].resetMatching( this, d_ccand_eqc[r][i-1][j], mode );
        if( d_tg_alloc[0].getNextMatch( this, d_ccand_eqc[r][i-1][j], subs, rev_subs ) ){
          d_ccand_eqc[r][i].push_back( d_ccand_eqc[r][i-1][j] );
        }
      }
    }
    for( unsigned r=0; r<2; r++ ){
      Trace("sg-gen-tg-debug") << "Current eqc of type " << r << " : ";
      for( unsigned j=0; j<d_ccand_eqc[r][i].size(); j++ ){
        Trace("sg-gen-tg-debug") << "e" << d_cg->d_em[d_ccand_eqc[r][i][j]] << " ";
      }
      Trace("sg-gen-tg-debug") << std::endl;
    }
    if( options::conjectureFilterActiveTerms() && d_ccand_eqc[0][i].empty() ){
      Trace("sg-gen-consider-term") << "Do not consider term of form ";
      d_tg_alloc[0].debugPrint( this, "sg-gen-consider-term", "sg-gen-consider-term-debug" );
      Trace("sg-gen-consider-term") << " since no relevant EQC matches it." << std::endl;
      return false;
    }
    if( options::conjectureFilterModel() && d_ccand_eqc[1][i].empty() ){
      Trace("sg-gen-consider-term") << "Do not consider term of form ";
      d_tg_alloc[0].debugPrint( this, "sg-gen-consider-term", "sg-gen-consider-term-debug" );
      Trace("sg-gen-consider-term") << " since no ground EQC matches it." << std::endl;
      return false;
    }
  }
  Trace("sg-gen-tg-debug") << "Will consider term ";
  d_tg_alloc[0].debugPrint( this, "sg-gen-tg-debug", "sg-gen-tg-debug" );
  Trace("sg-gen-tg-debug") << std::endl;
  Trace("sg-gen-consider-term-debug") << std::endl;
  return true;
}

void TermGenEnv::changeContext( bool add ) {
  if( add ){
    for( unsigned r=0; r<2; r++ ){
      d_ccand_eqc[r].push_back( std::vector< TNode >() );
    }
    d_tg_id++;
  }else{
    for( unsigned r=0; r<2; r++ ){
      d_ccand_eqc[r].pop_back();
    }
    d_tg_id--;
    Assert(d_tg_alloc.find(d_tg_id) != d_tg_alloc.end());
    d_tg_alloc.erase( d_tg_id );
  }
}

bool TermGenEnv::considerCurrentTermCanon( unsigned tg_id ){
  Assert(tg_id < d_tg_alloc.size());
  if( options::conjectureFilterCanonical() ){
    //check based on a canonicity of the term (if there is one)
    Trace("sg-gen-tg-debug") << "Consider term canon ";
    d_tg_alloc[0].debugPrint( this, "sg-gen-tg-debug", "sg-gen-tg-debug" );
    Trace("sg-gen-tg-debug") << ", tg is [" << tg_id << "]..." << std::endl;

    Node ln = d_tg_alloc[tg_id].getTerm( this );
    Trace("sg-gen-tg-debug") << "Term is " << ln << std::endl;
    return d_cg->considerTermCanon( ln, d_gen_relevant_terms );
  }
  return true;
}

bool TermGenEnv::isRelevantFunc( Node f ) {
  return std::find( d_funcs.begin(), d_funcs.end(), f )!=d_funcs.end();
}

bool TermGenEnv::isRelevantTerm( Node t ) {
  if( t.getKind()!=BOUND_VARIABLE ){
    if( t.getKind()!=EQUAL ){
      if( t.hasOperator() ){
        TNode op = t.getOperator();
        if( !isRelevantFunc( op ) ){
          return false;
        }
      }else{
        return false;
      }
    }
    for( unsigned i=0; i<t.getNumChildren(); i++ ){
      if( !isRelevantTerm( t[i] ) ){
        return false;
      }
    }
  }
  return true;
}

TermDb * TermGenEnv::getTermDatabase() {
  return d_cg->getTermDatabase();
}
Node TermGenEnv::getGroundEqc( TNode r ) {
  return d_cg->getGroundEqc( r );
}
bool TermGenEnv::isGroundEqc( TNode r ){
  return d_cg->isGroundEqc( r );
}
bool TermGenEnv::isGroundTerm( TNode n ){
  return d_cg->isGroundTerm( n );
}


void SubstitutionIndex::addSubstitution( TNode eqc, std::vector< TNode >& vars, std::vector< TNode >& terms, unsigned i ) {
  if( i==vars.size() ){
    d_var = eqc;
  }else{
    Assert(d_var.isNull() || d_var == vars[i]);
    d_var = vars[i];
    d_children[terms[i]].addSubstitution( eqc, vars, terms, i+1 );
  }
}

bool SubstitutionIndex::notifySubstitutions( ConjectureGenerator * s, std::map< TNode, TNode >& subs, TNode rhs, unsigned numVars, unsigned i ) {
  if( i==numVars ){
    Assert(d_children.empty());
    return s->notifySubstitution( d_var, subs, rhs );
  }else{
    Assert(i == 0 || !d_children.empty());
    for( std::map< TNode, SubstitutionIndex >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
      Trace("sg-cconj-debug2") << "Try " << d_var << " -> " << it->first << " (" << i << "/" << numVars << ")" << std::endl;
      subs[d_var] = it->first;
      if( !it->second.notifySubstitutions( s, subs, rhs, numVars, i+1 ) ){
        return false;
      }
    }
    return true;
  }
}


void TheoremIndex::addTheorem( std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs ){
  if( lhs_v.empty() ){
    if( std::find( d_terms.begin(), d_terms.end(), rhs )==d_terms.end() ){
      d_terms.push_back( rhs );
    }
  }else{
    unsigned index = lhs_v.size()-1;
    if( lhs_arg[index]==lhs_v[index].getNumChildren() ){
      lhs_v.pop_back();
      lhs_arg.pop_back();
      addTheorem( lhs_v, lhs_arg, rhs );
    }else{
      lhs_arg[index]++;
      addTheoremNode( lhs_v[index][lhs_arg[index]-1], lhs_v, lhs_arg, rhs );
    }
  }
}

void TheoremIndex::addTheoremNode( TNode curr, std::vector< TNode >& lhs_v, std::vector< unsigned >& lhs_arg, TNode rhs ){
  Trace("thm-db-debug") << "Adding conjecture for subterm " << curr << "..." << std::endl;
  if( curr.hasOperator() ){
    lhs_v.push_back( curr );
    lhs_arg.push_back( 0 );
    d_children[curr.getOperator()].addTheorem( lhs_v, lhs_arg, rhs );
  }else{
    Assert(curr.getKind() == kind::BOUND_VARIABLE);
    TypeNode tn = curr.getType();
    Assert(d_var[tn].isNull() || d_var[tn] == curr);
    d_var[tn] = curr;
    d_children[curr].addTheorem( lhs_v, lhs_arg, rhs );
  }
}

void TheoremIndex::getEquivalentTerms( std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                                       std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                                       std::vector< Node >& terms ) {
  Trace("thm-db-debug") << "Get equivalent terms " << n_v.size() << " " << n_arg.size() << std::endl;
  if( n_v.empty() ){
    Trace("thm-db-debug") << "Number of terms : " << d_terms.size() << std::endl;
    //apply substutitions to RHS's
    for( unsigned i=0; i<d_terms.size(); i++ ){
      Node n = d_terms[i].substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
      terms.push_back( n );
    }
  }else{
    unsigned index = n_v.size()-1;
    if( n_arg[index]==n_v[index].getNumChildren() ){
      n_v.pop_back();
      n_arg.pop_back();
      getEquivalentTerms( n_v, n_arg, smap, vars, subs, terms );
    }else{
      n_arg[index]++;
      getEquivalentTermsNode( n_v[index][n_arg[index]-1], n_v, n_arg, smap, vars, subs, terms );
    }
  }
}

void TheoremIndex::getEquivalentTermsNode( Node curr, std::vector< TNode >& n_v, std::vector< unsigned >& n_arg,
                                           std::map< TNode, TNode >& smap, std::vector< TNode >& vars, std::vector< TNode >& subs,
                                           std::vector< Node >& terms ) {
  Trace("thm-db-debug") << "Get equivalent based on subterm " << curr << "..." << std::endl;
  if( curr.hasOperator() ){
    Trace("thm-db-debug") << "Check based on operator..." << std::endl;
    std::map< TNode, TheoremIndex >::iterator it = d_children.find( curr.getOperator() );
    if( it!=d_children.end() ){
      n_v.push_back( curr );
      n_arg.push_back( 0 );
      it->second.getEquivalentTerms( n_v, n_arg, smap, vars, subs, terms );
    }
    Trace("thm-db-debug") << "...done check based on operator" << std::endl;
  }
  TypeNode tn = curr.getType();
  std::map< TypeNode, TNode >::iterator itt = d_var.find( tn );
  if( itt!=d_var.end() ){
    Trace("thm-db-debug") << "Check for substitution with " << itt->second << "..." << std::endl;
    Assert(curr.getType() == itt->second.getType());
    //add to substitution if possible
    bool success = false;
    std::map< TNode, TNode >::iterator it = smap.find( itt->second );
    if( it==smap.end() ){
      smap[itt->second] = curr;
      vars.push_back( itt->second );
      subs.push_back( curr );
      success = true;
    }else if( it->second==curr ){
      success = true;
    }else{
      //also check modulo equality (in universal equality engine)
    }
    Trace("thm-db-debug") << "...check for substitution with " << itt->second << ", success = " << success << "." << std::endl;
    if( success ){
      d_children[itt->second].getEquivalentTerms( n_v, n_arg, smap, vars, subs, terms );
    }
  }
}

void TheoremIndex::debugPrint( const char * c, unsigned ind ) {
  for( std::map< TNode, TheoremIndex >::iterator it = d_children.begin(); it != d_children.end(); ++it ){
    for( unsigned i=0; i<ind; i++ ){ Trace(c) << "  "; }
    Trace(c) << it->first << std::endl;
    it->second.debugPrint( c, ind+1 );
  }
  if( !d_terms.empty() ){
    for( unsigned i=0; i<ind; i++ ){ Trace(c) << "  "; }
    Trace(c) << "{";
    for( unsigned i=0; i<d_terms.size(); i++ ){
      Trace(c) << " " << d_terms[i];
    }
    Trace(c) << " }" << std::endl;
  }
  //if( !d_var.isNull() ){
  //  for( unsigned i=0; i<ind; i++ ){ Trace(c) << "  "; }
  //  Trace(c) << "var:" << d_var << std::endl;
  //}
}

bool ConjectureGenerator::optReqDistinctVarPatterns() { return false; }
bool ConjectureGenerator::optFilterUnknown() { return true; }  //may change
int ConjectureGenerator::optFilterScoreThreshold() { return 1; }
unsigned ConjectureGenerator::optFullCheckFrequency() { return 1; }

bool ConjectureGenerator::optStatsOnly() { return false; }

}
