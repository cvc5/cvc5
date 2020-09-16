/*********************                                                        */
/*! \file candidate_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of theory uf candidate generator class
 **/

#include "theory/quantifiers/ematching/candidate_generator.h"
#include "expr/dtype.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

bool CandidateGenerator::isLegalCandidate( Node n ){
  return d_qe->getTermDatabase()->isTermActive( n ) && ( !options::cegqi() || !quantifiers::TermUtil::hasInstConstAttr(n) );
}

CandidateGeneratorQE::CandidateGeneratorQE(QuantifiersEngine* qe, Node pat)
    : CandidateGenerator(qe),
      d_term_iter(-1),
      d_term_iter_limit(0),
      d_mode(cand_term_none)
{
  d_op = qe->getTermDatabase()->getMatchOperator( pat );
  Assert(!d_op.isNull());
}

void CandidateGeneratorQE::resetInstantiationRound(){
  d_term_iter_limit = d_qe->getTermDatabase()->getNumGroundTerms( d_op );
}

void CandidateGeneratorQE::reset( Node eqc ){
  d_term_iter = 0;
  if( eqc.isNull() ){
    d_mode = cand_term_db;
  }else{
    if( isExcludedEqc( eqc ) ){
      d_mode = cand_term_none;
    }else{
      eq::EqualityEngine* ee = d_qe->getEqualityQuery()->getEngine();
      if( ee->hasTerm( eqc ) ){
        TNodeTrie* tat = d_qe->getTermDatabase()->getTermArgTrie(eqc, d_op);
        if( tat ){
          //create an equivalence class iterator in eq class eqc
          Node rep = ee->getRepresentative( eqc );
          d_eqc_iter = eq::EqClassIterator( rep, ee );
          d_mode = cand_term_eqc;
        }else{
          d_mode = cand_term_none;
        }   
      }else{
        //the only match is this term itself
        d_eqc = eqc;
        d_mode = cand_term_ident;
      }
    }
  }
}
bool CandidateGeneratorQE::isLegalOpCandidate( Node n ) {
  if( n.hasOperator() ){
    if( isLegalCandidate( n ) ){
      return d_qe->getTermDatabase()->getMatchOperator( n )==d_op;
    }
  }
  return false;
}

Node CandidateGeneratorQE::getNextCandidate(){
  if( d_mode==cand_term_db ){
    Debug("cand-gen-qe") << "...get next candidate in tbd" << std::endl;
    //get next candidate term in the uf term database
    while( d_term_iter<d_term_iter_limit ){
      Node n = d_qe->getTermDatabase()->getGroundTerm( d_op, d_term_iter );
      d_term_iter++;
      if( isLegalCandidate( n ) ){
        if( d_qe->getTermDatabase()->hasTermCurrent( n ) ){
          if( d_exclude_eqc.empty() ){
            return n;
          }else{
            Node r = d_qe->getEqualityQuery()->getRepresentative( n );
            if( d_exclude_eqc.find( r )==d_exclude_eqc.end() ){
              Debug("cand-gen-qe") << "...returning " << n << std::endl;
              return n;
            }
          }
        }
      }
    }
  }else if( d_mode==cand_term_eqc ){
    Debug("cand-gen-qe") << "...get next candidate in eqc" << std::endl;
    while( !d_eqc_iter.isFinished() ){
      Node n = *d_eqc_iter;
      ++d_eqc_iter;
      if( isLegalOpCandidate( n ) ){
        Debug("cand-gen-qe") << "...returning " << n << std::endl;
        return n;
      }
    }
  }else if( d_mode==cand_term_ident ){
    Debug("cand-gen-qe") << "...get next candidate identity" << std::endl;
    if (!d_eqc.isNull())
    {
      Node n = d_eqc;
      d_eqc = Node::null();
      if( isLegalOpCandidate( n ) ){
        return n;
      }
    }
  }
  return Node::null();
}

CandidateGeneratorQELitDeq::CandidateGeneratorQELitDeq( QuantifiersEngine* qe, Node mpat ) :
CandidateGenerator( qe ), d_match_pattern( mpat ){
  Assert(d_match_pattern.getKind() == EQUAL);
  d_match_pattern_type = d_match_pattern[0].getType();
}

void CandidateGeneratorQELitDeq::reset( Node eqc ){
  Node false_term = d_qe->getEqualityQuery()->getEngine()->getRepresentative( NodeManager::currentNM()->mkConst<bool>(false) );
  d_eqc_false = eq::EqClassIterator( false_term, d_qe->getEqualityQuery()->getEngine() );
}

Node CandidateGeneratorQELitDeq::getNextCandidate(){
  //get next candidate term in equivalence class
  while( !d_eqc_false.isFinished() ){
    Node n = (*d_eqc_false);
    ++d_eqc_false;
    if( n.getKind()==d_match_pattern.getKind() ){
      if (n[0].getType().isComparableTo(d_match_pattern_type)
          && isLegalCandidate(n))
      {
        //found an iff or equality, try to match it
        //DO_THIS: cache to avoid redundancies?
        //DO_THIS: do we need to try the symmetric equality for n?  or will it also exist in the eq class of false?
        return n;
      }
    }
  }
  return Node::null();
}


CandidateGeneratorQEAll::CandidateGeneratorQEAll( QuantifiersEngine* qe, Node mpat ) :
  CandidateGenerator( qe ), d_match_pattern( mpat ){
  d_match_pattern_type = mpat.getType();
  Assert(mpat.getKind() == INST_CONSTANT);
  d_f = quantifiers::TermUtil::getInstConstAttr( mpat );
  d_index = mpat.getAttribute(InstVarNumAttribute());
  d_firstTime = false;
}

void CandidateGeneratorQEAll::reset( Node eqc ) {
  d_eq = eq::EqClassesIterator( d_qe->getEqualityQuery()->getEngine() );
  d_firstTime = true;
}

Node CandidateGeneratorQEAll::getNextCandidate() {
  quantifiers::TermDb* tdb = d_qe->getTermDatabase();
  while( !d_eq.isFinished() ){
    TNode n = (*d_eq);
    ++d_eq;
    if( n.getType().isComparableTo( d_match_pattern_type ) ){
      TNode nh = tdb->getEligibleTermInEqc(n);
      if( !nh.isNull() ){
        if( options::instMaxLevel()!=-1 || options::lteRestrictInstClosure() ){
          nh = d_qe->getInternalRepresentative( nh, d_f, d_index );
          //don't consider this if already the instantiation is ineligible
          if (!nh.isNull() && !tdb->isTermEligibleForInstantiation(nh, d_f))
          {
            nh = Node::null();
          }
        }
        if( !nh.isNull() ){
          d_firstTime = false;
          //an equivalence class with the same type as the pattern, return it
          return nh;
        }
      }
    }
  }
  if( d_firstTime ){
    //must return something
    d_firstTime = false;
    return d_qe->getInstantiate()->getTermForType(d_match_pattern_type);
  }
  return Node::null();
}

CandidateGeneratorConsExpand::CandidateGeneratorConsExpand(
    QuantifiersEngine* qe, Node mpat)
    : CandidateGeneratorQE(qe, mpat)
{
  Assert(mpat.getKind() == APPLY_CONSTRUCTOR);
  d_mpat_type = mpat.getType();
}

void CandidateGeneratorConsExpand::reset(Node eqc)
{
  d_term_iter = 0;
  if (eqc.isNull())
  {
    d_mode = cand_term_db;
  }
  else
  {
    d_eqc = eqc;
    d_mode = cand_term_ident;
    Assert(d_eqc.getType() == d_mpat_type);
  }
}

Node CandidateGeneratorConsExpand::getNextCandidate()
{
  // get the next term from the base class
  Node curr = CandidateGeneratorQE::getNextCandidate();
  if (curr.isNull() || (curr.hasOperator() && curr.getOperator() == d_op))
  {
    return curr;
  }
  // expand it
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> children;
  const DType& dt = d_mpat_type.getDType();
  Assert(dt.getNumConstructors() == 1);
  children.push_back(d_op);
  for (unsigned i = 0, nargs = dt[0].getNumArgs(); i < nargs; i++)
  {
    Node sel = nm->mkNode(
        APPLY_SELECTOR_TOTAL, dt[0].getSelectorInternal(d_mpat_type, i), curr);
    children.push_back(sel);
  }
  return nm->mkNode(APPLY_CONSTRUCTOR, children);
}

bool CandidateGeneratorConsExpand::isLegalOpCandidate(Node n)
{
  return isLegalCandidate(n);
}
