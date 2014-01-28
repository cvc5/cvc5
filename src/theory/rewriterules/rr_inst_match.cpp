/*********************                                                        */
/*! \file rr_inst_match.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of inst match class
 **/

#include "theory/quantifiers/inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/rewriterules/rr_inst_match.h"
#include "theory/rewriterules/rr_trigger.h"
#include "theory/rewriterules/rr_inst_match_impl.h"
#include "theory/rewriterules/rr_candidate_generator.h"
#include "theory/quantifiers/candidate_generator.h"
#include "theory/rewriterules/efficient_e_matching.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::rrinst;
using namespace CVC4::theory::uf::rrinst;
using namespace CVC4::theory::eq::rrinst;

namespace CVC4{
namespace theory{
namespace rrinst{




InstMatch::InstMatch() {
}

InstMatch::InstMatch( InstMatch* m ) {
  d_map = m->d_map;
}

bool InstMatch::setMatch( EqualityQuery* q, TNode v, TNode m, bool & set ){
  std::map< Node, Node >::iterator vn = d_map.find( v );
  if( !m.isNull() && !m.getType().isSubtypeOf( v.getType() ) ){
    set = false;
    return false;
  }else if( vn==d_map.end() || vn->second.isNull() ){
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
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[it->first] = it->second;
      }
    }
  }
  return true;
}

bool InstMatch::merge( EqualityQuery* q, InstMatch& m ){
  for( std::map< Node, Node >::iterator it = m.d_map.begin(); it != m.d_map.end(); ++it ){
    if( !it->second.isNull() ){
      std::map< Node, Node >::iterator itf = d_map.find( it->first );
      if( itf==d_map.end() || itf->second.isNull() ){
        d_map[ it->first ] = it->second;
      }else{
        if( !q->areEqual( it->second, itf->second ) ){
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
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node ic = qe->getTermDatabase()->getInstantiationConstant( f, i );
    if( d_map.find( ic )==d_map.end() ){
      d_map[ ic ] = qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
    }
  }
}

//void InstMatch::makeInternalRepresentative( QuantifiersEngine* qe ){
//  EqualityQueryQuantifiersEngine* eqqe = (EqualityQueryQuantifiersEngine*)qe->getEqualityQuery();
//  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
//    d_map[ it->first ] = eqqe->getInternalRepresentative( it->second );
//  }
//}

void InstMatch::makeRepresentative( QuantifiersEngine* qe ){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    if( qe->getEqualityQuery()->getEngine()->hasTerm( it->second ) ){
      d_map[ it->first ] = qe->getEqualityQuery()->getEngine()->getRepresentative( it->second );
    }
  }
}

void InstMatch::applyRewrite(){
  for( std::map< Node, Node >::iterator it = d_map.begin(); it != d_map.end(); ++it ){
    it->second = Rewriter::rewrite(it->second);
  }
}

/** get value */
Node InstMatch::getValue( Node var ) const{
  std::map< Node, Node >::const_iterator it = d_map.find( var );
  if( it!=d_map.end() ){
    return it->second;
  }else{
    return Node::null();
  }
}

Node InstMatch::get( QuantifiersEngine* qe, Node f, int i ) {
  return get( qe->getTermDatabase()->getInstantiationConstant( f, i ) );
}

void InstMatch::set(TNode var, TNode n){
  Assert( !var.isNull() );
  if (Trace.isOn("inst-match-warn")) {
    // For a strange use in inst_match.cpp InstMatchGeneratorSimple::addInstantiations
    if( !n.isNull() && !n.getType().isSubtypeOf( var.getType() ) ){
      Trace("inst-match-warn") << quantifiers::TermDb::getInstConstAttr(var) << std::endl;
      Trace("inst-match-warn") << var << " " << var.getType() << " " << n << " " << n.getType() << std::endl ;
    }
  }
  Assert( n.isNull() || n.getType().isSubtypeOf( var.getType() ) );
  d_map[var] = n;
}

void InstMatch::set( QuantifiersEngine* qe, Node f, int i, TNode n ) {
  set( qe->getTermDatabase()->getInstantiationConstant( f, i ), n );
}






typedef CVC4::theory::rrinst::InstMatch InstMatch;
typedef CVC4::theory::inst::CandidateGeneratorQueue CandidateGeneratorQueue;

template<bool modEq>
class InstMatchTrie2Pairs
{
  typename std::vector< std::vector < typename InstMatchTrie2Gen<modEq>::Tree > > d_data;
  InstMatchTrie2Gen<modEq> d_backtrack;
public:
  InstMatchTrie2Pairs(context::Context* c,  QuantifiersEngine* q, size_t n):
  d_backtrack(c,q) {
    // resize to a triangle
    //
    // |     *
    // |   * *
    // | * * *
    // | -----> i
    d_data.resize(n);
    for(size_t i=0; i < n; ++i){
      d_data[i].resize(i+1,typename InstMatchTrie2Gen<modEq>::Tree(0));
    }
  };
  InstMatchTrie2Pairs(const InstMatchTrie2Pairs &) CVC4_UNDEFINED;
  const InstMatchTrie2Pairs & operator =(const InstMatchTrie2Pairs & e) CVC4_UNDEFINED;
  /** add match m in the trie,
      return true if it was never seen */
  inline bool addInstMatch( size_t i, size_t j, InstMatch& m){
    size_t k = std::min(i,j);
    size_t l = std::max(i,j);
    return d_backtrack.addInstMatch(m,&(d_data[l][k]));
  };
  inline bool addInstMatch( size_t i, InstMatch& m){
    return d_backtrack.addInstMatch(m,&(d_data[i][i]));
  };

};


// Currently the implementation doesn't take into account that
// variable should have the same value given.
// TODO use the d_children way perhaps
// TODO replace by a real dictionnary
// We should create a real substitution? slower more precise
// We don't do that often
bool nonunifiable( TNode t0, TNode pat, const std::vector<Node> & vars){
  if(pat.isNull()) return true;

  typedef std::vector<std::pair<TNode,TNode> > tstack;
  tstack stack(1,std::make_pair(t0,pat)); // t * pat

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
};

/** New things */
class DumbMatcher: public Matcher{
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
};

class DumbPatMatcher: public PatMatcher{
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return false;
  }
};


/* The order of the matching is:
   reset arg1, nextMatch arg1, reset arg2, nextMatch arg2, ... */
ApplyMatcher::ApplyMatcher( Node pat, QuantifiersEngine* qe): d_pattern(pat){

  //set-up d_variables, d_constants, d_childrens
  for( size_t i=0; i< d_pattern.getNumChildren(); ++i ){
    //EqualityQuery* q = qe->getEqualityQuery(d_pattern[i].getType());
    EqualityQuery* q = qe->getEqualityQuery();
    Assert( q != NULL );
    if( quantifiers::TermDb::hasInstConstAttr(d_pattern[i]) ){
      if( d_pattern[i].getKind()==INST_CONSTANT ){
        //It's a variable
        d_variables.push_back(make_triple((TNode)d_pattern[i],i,q));
      }else{
        //It's neither a constant argument neither a variable
        //we create the matcher for the subpattern
        d_childrens.push_back(make_triple(mkMatcher((TNode)d_pattern[i], qe),i,q));
      };
    }else{
      // It's a constant
      d_constants.push_back(make_triple((TNode)d_pattern[i],i,q));
    }
  }
}

void ApplyMatcher::resetInstantiationRound( QuantifiersEngine* qe ){
  for( size_t i=0; i< d_childrens.size(); i++ ){
    d_childrens[i].first->resetInstantiationRound( qe );
  }
}

bool ApplyMatcher::reset(TNode t, InstMatch & m, QuantifiersEngine* qe){
  Debug("matching") << "Matching " << t << " against pattern " << d_pattern << " ("
                    << m.size() << ")"  << std::endl;

  //if t is null
  Assert( !t.isNull() );
  Assert( !quantifiers::TermDb::hasInstConstAttr(t) );
  Assert( t.getKind()==d_pattern.getKind() );
  Assert( (t.getKind()!=APPLY_UF && t.getKind()!=APPLY_CONSTRUCTOR)
          || t.getOperator()==d_pattern.getOperator() );

  typedef std::vector< triple<TNode,size_t,EqualityQuery*> >::iterator iterator;
  for(iterator i = d_constants.begin(), end = d_constants.end();
      i != end; ++i){
    if( !i->third->areEqual( i->first, t[i->second] ) ){
      Debug("matching-fail") << "Match fail arg: " << i->first << " and " << t[i->second] << std::endl;
      //setMatchFail( qe, d_pattern[i], t[i] );
      //ground arguments are not equal
      return false;
    }
  }

  d_binded.clear();
  bool set;
  for(iterator i = d_variables.begin(), end = d_variables.end();
      i != end; ++i){
    if( !m.setMatch( i->third, i->first, t[i->second], set) ){
      //match is in conflict
      Debug("matching-debug") << "Match in conflict " << t[i->second] << " and "
                              << i->first << " because "
                              << m.get(i->first)
                              << std::endl;
      Debug("matching-fail") << "Match fail: " << m.get(i->first) << " and " << t[i->second] << std::endl;
      //setMatchFail( qe, partial[0].d_map[d_pattern[i]], t[i] );
      m.erase(d_binded.begin(), d_binded.end());
      return false;
    }else{
      if(set){ //The variable has just been set
        d_binded.push_back(i->first);
      }
    }
  }

  //now, fit children into match
  //we will be requesting candidates for matching terms for each child
  d_reps.clear();
  for( size_t i=0; i< d_childrens.size(); i++ ){
    Debug("matching-debug") << "Take the representative of " << t[ d_childrens[i].second ] << std::endl;
    Assert( d_childrens[i].third->hasTerm(t[ d_childrens[i].second ]) );
    Node rep = d_childrens[i].third->getRepresentative( t[ d_childrens[i].second ] );
    d_reps.push_back( rep );
  }

  if(d_childrens.size() == 0) return true;
  else return getNextMatch(m, qe, true);
}

bool ApplyMatcher::getNextMatch(InstMatch& m, QuantifiersEngine* qe, bool reset){
  Assert(d_childrens.size() > 0);
  const size_t max = d_childrens.size() - 1;
  size_t index = reset ? 0 : max;
  Assert(d_childrens.size() == d_reps.size());
  while(true){
    if(reset ?
       d_childrens[index].first->reset( d_reps[index], m, qe ) :
       d_childrens[index].first->getNextMatch( m, qe )){
      if(index==max) return true;
      ++index;
      reset=true;
    }else{
      if(index==0){
        m.erase(d_binded.begin(), d_binded.end());
        return false;
      }
      --index;
      reset=false;
    };
  }
}

bool ApplyMatcher::getNextMatch(InstMatch& m, QuantifiersEngine* qe){
  if(d_childrens.size() == 0){
    m.erase(d_binded.begin(), d_binded.end());
    return false;
  } else return getNextMatch(m, qe, false);
}

/** Proxy that call the sub-matcher on the result return by the given candidate generator */
template <class CG, class M>
class CandidateGeneratorMatcher: public Matcher{
  /** candidate generator */
  CG d_cg;
  /** the sub-matcher */
  M d_m;
public:
  CandidateGeneratorMatcher(CG cg, M m): d_cg(cg), d_m(m)
  {/* last is Null */};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cg.resetInstantiationRound();
    d_m.resetInstantiationRound(qe);
  };
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe ){
    d_cg.reset(n);
    return findMatch(m,qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    // The sub-matcher has another match
    return d_m.getNextMatch(m, qe) || findMatch(m,qe);
  }
private:
  bool findMatch( InstMatch& m, QuantifiersEngine* qe ){
    // Otherwise try to find a new candidate that has at least one match
    while(true){
      TNode n = d_cg.getNextCandidate();//kept somewhere Term-db
      Debug("matching") << "GenCand " << n << " (" << this << ")" << std::endl;
      if(n.isNull()) return false;
      if(d_m.reset(n,m,qe)) return true;
    };
  }
};

/** Proxy that call the sub-matcher on the result return by the given candidate generator */
template<class M>
class PatOfMatcher: public PatMatcher{
  M d_m;
public:
  inline PatOfMatcher(M m): d_m(m){}
  void resetInstantiationRound(QuantifiersEngine* qe){
    d_m.resetInstantiationRound(qe);
  }
  bool reset(InstMatch& m, QuantifiersEngine* qe){
    return d_m.reset(Node::null(),m,qe);
  };
  bool getNextMatch(InstMatch& m, QuantifiersEngine* qe){
    return d_m.getNextMatch(m,qe);
  };
};

class ArithMatcher: public Matcher{
private:
  /** for arithmetic matching */
  std::map< Node, Node > d_arith_coeffs;
  /** get the match against ground term or formula t.
      d_match_mattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  /** the variable that are set by this matcher */
  std::vector< TNode > d_binded; /* TNode because the variables are already in d_arith_coeffs */
  Node d_pattern; //for debugging
public:
  ArithMatcher(Node pat, QuantifiersEngine* qe);
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe );
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe );
};

/** Match just a variable */
class VarMatcher: public Matcher{
  Node d_var;
  bool d_binded; /* True if the reset bind the variable to some value */
  EqualityQuery* d_q;
public:
  VarMatcher(Node var, QuantifiersEngine* qe): d_var(var), d_binded(false){
    //d_q = qe->getEqualityQuery(var.getType());
    d_q = qe->getEqualityQuery();
  }
  void resetInstantiationRound( QuantifiersEngine* qe ){};
  bool reset( TNode n, InstMatch& m, QuantifiersEngine* qe ){
    if(!m.setMatch( d_q, d_var, n, d_binded )){
      //match is in conflict
      Debug("matching-fail") << "Match fail: " << m.get(d_var)
                             << " and " << n << std::endl;
      return false;
    } else return true;
  };
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    //match is in conflict
    if (d_binded) m.erase(d_var);
    return false;
  }
};

template <class M, class Test >
class TestMatcher: public Matcher{
  M d_m;
  Test d_test;
public:
  inline TestMatcher(M m, Test test): d_m(m), d_test(test){}
  inline void resetInstantiationRound(QuantifiersEngine* qe){
    d_m.resetInstantiationRound(qe);
  }
  inline bool reset(TNode n, InstMatch& m, QuantifiersEngine* qe){
    return d_test(n) && d_m.reset(n, m, qe);
  }
  inline bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_m.getNextMatch(m, qe);
  }
};

class LegalOpTest/*: public unary_function<TNode,bool>*/ {
  Node d_op;
public:
  inline LegalOpTest(Node op): d_op(op){}
  inline bool operator() (TNode n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      // ( // n.getKind()==SELECT || n.getKind()==STORE ||
      //  n.getKind()==APPLY_UF || n.getKind()==APPLY_CONSTRUCTOR) &&
      n.hasOperator() &&
      n.getOperator()==d_op;
  };
};

class LegalKindTest/* : public unary_function<TNode,bool>*/ {
  Kind d_kind;
public:
  inline LegalKindTest(Kind kind): d_kind(kind){}
  inline bool operator() (TNode n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      n.getKind()==d_kind;
  };
};

class LegalTypeTest/* : public unary_function<TNode,bool>*/ {
  TypeNode d_type;
public:
  inline LegalTypeTest(TypeNode type): d_type(type){}
  inline bool operator() (TNode n) {
    return
      CandidateGenerator::isLegalCandidate(n) &&
      n.getType()==d_type;
  };
};

class LegalTest/* : public unary_function<TNode,bool>*/ {
public:
  inline bool operator() (TNode n) {
    return CandidateGenerator::isLegalCandidate(n);
  };
};

size_t numFreeVar(TNode t){
  size_t n = 0;
  for( size_t i=0, size =t.getNumChildren(); i < size; ++i ){
    if( quantifiers::TermDb::hasInstConstAttr(t[i]) ){
      if( t[i].getKind()==INST_CONSTANT ){
        //variable
        ++n;
      }else{
        //neither variable nor constant
        n += numFreeVar(t[i]);
      }
    }
  }
  return n;
}

class OpMatcher: public Matcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalOpTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClass, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::APPLY_UF );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalOpTest(pat.getOperator()));
    /** Iter on the equivalence class of the given term */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF *>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ));
    eq::EqualityEngine* ee = static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
    CandidateGeneratorTheoryEeClass cdtUfEq(ee);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
  size_t d_num_var;
  Node d_pat;
public:
  OpMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),d_num_var(numFreeVar(pat)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( TNode t, InstMatch& m, QuantifiersEngine* qe ){
    // size_t m_size = m.d_map.size();
    // if(m_size == d_num_var){
    //   uf::EqualityEngine<uf::TheoryUF::NotifyClass>* ee = (static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF )))->getEqualityEngine();
    //   std::cout << "!";
    //   return ee->areEqual(m.subst(d_pat),t);
    // }else{
    // std::cout << m.d_map.size() << std::endl;
    return d_cgm.reset(t, m, qe);
    // }
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

class DatatypesMatcher: public Matcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalOpTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClass, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::APPLY_CONSTRUCTOR,
            "For datatypes only constructor are accepted in pattern" );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalOpTest(pat.getOperator()));
    /** Iter on the equivalence class of the given term */
    datatypes::TheoryDatatypes* dt = static_cast<datatypes::TheoryDatatypes *>(qe->getTheoryEngine()->theoryOf( theory::THEORY_DATATYPES ));
    eq::EqualityEngine* ee = static_cast<eq::EqualityEngine*>(dt->getEqualityEngine());
    CandidateGeneratorTheoryEeClass cdtDtEq(ee);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtDtEq,am2);
    return am1;
  }
  Node d_pat;
public:
  DatatypesMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( TNode t, InstMatch& m, QuantifiersEngine* qe ){
    Debug("matching") << "datatypes: " << t << " matches " << d_pat << std::endl;
    return d_cgm.reset(t, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

class ArrayMatcher: public Matcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalKindTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClass, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::SELECT || pat.getKind() == kind::STORE );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3, LegalKindTest(pat.getKind()));
    /** Iter on the equivalence class of the given term */
    arrays::TheoryArrays* ar = static_cast<arrays::TheoryArrays *>(qe->getTheoryEngine()->theoryOf( theory::THEORY_ARRAY ));
    eq::EqualityEngine* ee =
      static_cast<eq::EqualityEngine*>(ar->getEqualityEngine());
    CandidateGeneratorTheoryEeClass cdtUfEq(ee);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
  size_t d_num_var;
  Node d_pat;
public:
  ArrayMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),d_num_var(numFreeVar(pat)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( TNode t, InstMatch& m, QuantifiersEngine* qe ){
    // size_t m_size = m.d_map.size();
    // if(m_size == d_num_var){
    //   uf::EqualityEngine<uf::TheoryUF::NotifyClass>* ee = (static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF )))->getEqualityEngine();
    //   std::cout << "!";
    //   return ee->areEqual(m.subst(d_pat),t);
    // }else{
    // std::cout << m.d_map.size() << std::endl;
    return d_cgm.reset(t, m, qe);
    // }
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

class AllOpMatcher: public PatMatcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfOp, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.hasOperator() );
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalTest());
    /** Iter on the equivalence class of the given term */
    TermDb* tdb = qe->getTermDatabase();
    Node op = tdb->getOperator( pat );
    CandidateGeneratorTheoryUfOp cdtUfEq(op,tdb);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
  size_t d_num_var;
  Node d_pat;
public:
  AllOpMatcher( TNode pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)), d_num_var(numFreeVar(pat)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    //    std::cout << m.d_map.size() << "/" << d_num_var << std::endl;
    return d_cgm.reset(Node::null(), m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

template <bool classes> /** true classes | false class */
class GenericCandidateGeneratorClasses: public CandidateGenerator{
private:
  CandidateGenerator* d_cg;
  QuantifiersEngine* d_qe;

public:
  void mkCandidateGenerator(){
    if(classes)
      d_cg = new GenericCandidateGeneratorClasses(d_qe);
    else
      d_cg = new GenericCandidateGeneratorClass(d_qe);
  }

  GenericCandidateGeneratorClasses(QuantifiersEngine* qe):
    d_qe(qe) {
    mkCandidateGenerator();
  }
  ~GenericCandidateGeneratorClasses(){
    delete(d_cg);
  }
  const GenericCandidateGeneratorClasses & operator =(const GenericCandidateGeneratorClasses & m){
    mkCandidateGenerator();
    return m;
  };
  GenericCandidateGeneratorClasses(const GenericCandidateGeneratorClasses & m):
  d_qe(m.d_qe){
    mkCandidateGenerator();
  }
  void resetInstantiationRound(){
    d_cg->resetInstantiationRound();
  };
  void reset( TNode eqc ){
    Assert( !classes || eqc.isNull() );
    d_cg->reset(eqc);
  }; //* the argument is not used
  TNode getNextCandidate(){
    return d_cg->getNextCandidate();
  };
}; /* MetaCandidateGeneratorClasses */


class GenericMatcher: public Matcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalOpTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< GenericCandidateGeneratorClasses<false>, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalOpTest(pat.getOperator()));
    /** Iter on the equivalence class of the given term */
    GenericCandidateGeneratorClasses<false> cdtG(qe);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtG,am2);
    return am1;
  }
  Node d_pat;
public:
  GenericMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( TNode t, InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(t, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};


class GenericPatMatcher: public PatMatcher{
  /* The matcher */
  typedef ApplyMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalOpTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< GenericCandidateGeneratorClasses<true>, AuxMatcher2> AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    /** In reverse order of matcher sequence */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good operator */
    AuxMatcher2 am2(am3,LegalOpTest(pat.getOperator()));
    /** Iter on the equivalence class of the given term */
    GenericCandidateGeneratorClasses<true> cdtG(qe);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtG,am2);
    return am1;
  }
  Node d_pat;
public:
  GenericPatMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),
    d_pat(pat) {}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(Node::null(), m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

class MetaCandidateGeneratorClasses: public CandidateGenerator{
private:
  CandidateGenerator* d_cg;
  TypeNode d_ty;
  TheoryEngine* d_te;

public:
  CandidateGenerator* mkCandidateGenerator(TypeNode ty, TheoryEngine* te){
    Debug("inst-match-gen") << "MetaCandidateGenerator for type: " << ty
                            << " Theory : " << Theory::theoryOf(ty) << std::endl;
    if( Theory::theoryOf(ty) == theory::THEORY_DATATYPES ){
      // datatypes::TheoryDatatypes* dt = static_cast<datatypes::TheoryDatatypes *>(te->theoryOf( theory::THEORY_DATATYPES ));
      // return new datatypes::rrinst::CandidateGeneratorTheoryClasses(dt);
      Unimplemented("MetaCandidateGeneratorClasses for THEORY_DATATYPES");
    }else if ( Theory::theoryOf(ty) == theory::THEORY_ARRAY ){
      arrays::TheoryArrays* ar = static_cast<arrays::TheoryArrays *>(te->theoryOf( theory::THEORY_ARRAY ));
      eq::EqualityEngine* ee =
        static_cast<eq::EqualityEngine*>(ar->getEqualityEngine());
      return new CandidateGeneratorTheoryEeClasses(ee);
    } else {
      uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(te->theoryOf( theory::THEORY_UF ));
      eq::EqualityEngine* ee =
        static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
      return new CandidateGeneratorTheoryEeClasses(ee);
    }
  }
  MetaCandidateGeneratorClasses(TypeNode ty, TheoryEngine* te):
    d_ty(ty), d_te(te) {
    d_cg = mkCandidateGenerator(ty,te);
  }
  ~MetaCandidateGeneratorClasses(){
    delete(d_cg);
  }
  const MetaCandidateGeneratorClasses & operator =(const MetaCandidateGeneratorClasses & m){
    d_cg = mkCandidateGenerator(m.d_ty, m.d_te);
    return m;
  };
  MetaCandidateGeneratorClasses(const MetaCandidateGeneratorClasses & m):
  d_ty(m.d_ty), d_te(m.d_te){
    d_cg = mkCandidateGenerator(m.d_ty, m.d_te);
  }
  void resetInstantiationRound(){
    d_cg->resetInstantiationRound();
  };
  void reset( TNode eqc ){
    d_cg->reset(eqc);
  }; //* the argument is not used
  TNode getNextCandidate(){
    return d_cg->getNextCandidate();
  };
}; /* MetaCandidateGeneratorClasses */

/** Match just a variable */
class AllVarMatcher: public PatMatcher{
private:
  /* generator */
  typedef VarMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalTypeTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< MetaCandidateGeneratorClasses, AuxMatcher2 > AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(TNode pat, QuantifiersEngine* qe){
    Assert( pat.getKind()==INST_CONSTANT );
    TypeNode ty = pat.getType();
    Debug("inst-match-gen") << "create AllVarMatcher for type: " << ty << std::endl;
    /** In reverse order of matcher sequence */
    /** Distribute it to all the pattern */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good type */
    AuxMatcher2 am2(am3,LegalTypeTest(ty));
    /** Generate one term by eq classes */
    MetaCandidateGeneratorClasses mcdt(ty,qe->getTheoryEngine());
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(mcdt,am2);
    return am1;
  }
public:
  AllVarMatcher( TNode pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)){}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(Node::null(), m, qe); //cdtUfEq doesn't use it's argument for reset
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

/** Match all the pattern with the same term */
class SplitMatcher: public Matcher{
private:
  const size_t size;
  ApplyMatcher d_m; /** Use ApplyMatcher by creating a fake application */
public:
  SplitMatcher(std::vector< Node > pats, QuantifiersEngine* qe):
    size(pats.size()),
    d_m(NodeManager::currentNM()->mkNode(kind::INST_PATTERN,pats), qe) {}
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_m.resetInstantiationRound(qe);
  };
  bool reset( TNode ex, InstMatch& m, QuantifiersEngine* qe ){
    NodeBuilder<> n(kind::INST_PATTERN);
    for(size_t i = 0; i < size; ++i) n << ex;
    Node nn = n;
    return d_m.reset(nn,m,qe);
  };
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return getNextMatch(m, qe);
  }
};


/** Match uf term in a fixed equivalence class */
class UfCstEqMatcher: public PatMatcher{
private:
  /* equivalence class to match */
  Node d_cst;
  /* generator */
  OpMatcher d_cgm;
public:
  UfCstEqMatcher( Node pat, Node cst, QuantifiersEngine* qe ):
    d_cst(cst),
    d_cgm(OpMatcher(pat,qe)) {};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(d_cst, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

/** Match equalities */
class UfEqMatcher: public PatMatcher{
private:
  /* generator */
  typedef SplitMatcher AuxMatcher3;
  typedef TestMatcher< AuxMatcher3, LegalTypeTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClasses, AuxMatcher2 > AuxMatcher1;
  AuxMatcher1 d_cgm;
  static inline AuxMatcher1 createCgm(std::vector<Node> & pat, QuantifiersEngine* qe){
    Assert( pat.size() > 0);
    TypeNode ty = pat[0].getType();
    for(size_t i = 1; i < pat.size(); ++i){
      Assert(pat[i].getType() == ty);
    }
    /** In reverse order of matcher sequence */
    /** Distribute it to all the pattern */
    AuxMatcher3 am3(pat,qe);
    /** Keep only the one that have the good type */
    AuxMatcher2 am2(am3,LegalTypeTest(ty));
    /** Generate one term by eq classes */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ));
    eq::EqualityEngine* ee =
      static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
    CandidateGeneratorTheoryEeClasses cdtUfEq(ee);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  UfEqMatcher( std::vector<Node> & pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)){}

  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(Node::null(), m, qe); //cdtUfEq doesn't use it's argument for reset
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};


/** Match dis-equalities */
class UfDeqMatcher: public PatMatcher{
private:
  /* generator */
  typedef ApplyMatcher AuxMatcher3;

  class EqTest/* : public unary_function<Node,bool>*/ {
    TypeNode d_type;
  public:
    inline EqTest(TypeNode type): d_type(type){};
    inline bool operator() (Node n) {
      return
        CandidateGenerator::isLegalCandidate(n) &&
        n.getKind() == kind::EQUAL &&
        n[0].getType()==d_type;
    };
  };
  typedef TestMatcher< AuxMatcher3, EqTest > AuxMatcher2;
  typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClass, AuxMatcher2 > AuxMatcher1;
  AuxMatcher1 d_cgm;
  Node false_term;
  static inline AuxMatcher1 createCgm(Node pat, QuantifiersEngine* qe){
    Assert( pat.getKind() == kind::NOT);
    TNode eq = pat[0];
    Assert( eq.getKind() == kind::EQUAL);
    TypeNode ty = eq[0].getType();
    /** In reverse order of matcher sequence */
    /** Distribute it to all the pattern */
    AuxMatcher3 am3(eq,qe);
    /** Keep only the one that have the good type */
    AuxMatcher2 am2(am3,EqTest(ty));
    /** Will generate all the terms of the eq class of false */
    uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ));
    eq::EqualityEngine* ee =
      static_cast<eq::EqualityEngine*>(uf->getEqualityEngine());
    CandidateGeneratorTheoryEeClass cdtUfEq(ee);
    /* Create a matcher from the candidate generator */
    AuxMatcher1 am1(cdtUfEq,am2);
    return am1;
  }
public:
  UfDeqMatcher( Node pat, QuantifiersEngine* qe ):
    d_cgm(createCgm(pat, qe)),
    false_term((static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF )))->getEqualityEngine()->
                getRepresentative(NodeManager::currentNM()->mkConst<bool>(false) )){};
  void resetInstantiationRound( QuantifiersEngine* qe ){
    d_cgm.resetInstantiationRound(qe);
  };
  bool reset( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.reset(false_term, m, qe);
  }
  bool getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
    return d_cgm.getNextMatch(m, qe);
  }
};

Matcher* mkMatcher( Node pat, QuantifiersEngine* qe ){
  Debug("inst-match-gen") << "mkMatcher: Pattern term is " << pat << std::endl;

  // if( pat.getKind() == kind::APPLY_UF){
  //   return new OpMatcher(pat, qe);
  // } else if( pat.getKind() == kind::APPLY_CONSTRUCTOR ){
  //   return new DatatypesMatcher(pat, qe);
  // } else if( pat.getKind() == kind::SELECT || pat.getKind() == kind::STORE ){
  //   return new ArrayMatcher(pat, qe);
  if( pat.getKind() == kind::APPLY_UF ||
      pat.getKind() == kind::APPLY_CONSTRUCTOR ||
      pat.getKind() == kind::SELECT || pat.getKind() == kind::STORE ){
    return new GenericMatcher(pat, qe);
  } else { /* Arithmetic? */
    /** TODO: something simpler to see if the pattern is a good
        arithmetic pattern */
    std::map< Node, Node > d_arith_coeffs;
    if( !Trigger::getPatternArithmetic( quantifiers::TermDb::getInstConstAttr(pat), pat, d_arith_coeffs ) ){
      Message() << "(?) Unknown matching pattern is " << pat << std::endl;
      Unimplemented("pattern not implemented");
      return new DumbMatcher();
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << pat << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
      ArithMatcher am3 (pat, qe);
      TestMatcher<ArithMatcher, LegalTypeTest>
        am2(am3,LegalTypeTest(pat.getType()));
      /* generator */
      uf::TheoryUF* uf = static_cast<uf::TheoryUF*>(qe->getTheoryEngine()->theoryOf( theory::THEORY_UF ));
      eq::EqualityEngine* ee =
        static_cast<eq::EqualityEngine*> (uf->getEqualityEngine());
      CandidateGeneratorTheoryEeClass cdtUfEq(ee);
      return new CandidateGeneratorMatcher< CandidateGeneratorTheoryEeClass,
        TestMatcher<ArithMatcher, LegalTypeTest> > (cdtUfEq,am2);
    }
  }
};

PatMatcher* mkPattern( Node pat, QuantifiersEngine* qe ){
  Debug("inst-match-gen") << "Pattern term is " << pat << std::endl;
  Assert( quantifiers::TermDb::hasInstConstAttr(pat) );

  if( pat.getKind()==kind::NOT && pat[0].getKind() == kind::EQUAL){
    /* Difference */
    return new UfDeqMatcher(pat, qe);
  } else if (pat.getKind() == kind::EQUAL){
    if( !quantifiers::TermDb::hasInstConstAttr(pat[0])){
        Assert(quantifiers::TermDb::hasInstConstAttr(pat[1]));
        return new UfCstEqMatcher(pat[1], pat[0], qe);
    }else if( !quantifiers::TermDb::hasInstConstAttr(pat[1] )){
      Assert(quantifiers::TermDb::hasInstConstAttr(pat[0]));
      return new UfCstEqMatcher(pat[0], pat[1], qe);
    }else{
      std::vector< Node > pats(pat.begin(),pat.end());
      return new UfEqMatcher(pats,qe);
    }
  } else if( Trigger::isAtomicTrigger( pat ) ){
    return new AllOpMatcher(pat, qe);
    // return new GenericPatMatcher(pat, qe);
  } else if( pat.getKind()==INST_CONSTANT ){
    // just a variable
    return new AllVarMatcher(pat, qe);
  } else { /* Arithmetic? */
    /** TODO: something simpler to see if the pattern is a good
        arithmetic pattern */
    std::map< Node, Node > d_arith_coeffs;
    if( !Trigger::getPatternArithmetic( quantifiers::TermDb::getInstConstAttr(pat), pat, d_arith_coeffs ) ){
      Debug("inst-match-gen") << "(?) Unknown matching pattern is " << pat << std::endl;
      Message() << "(?) Unknown matching pattern is " << pat << std::endl;
      return new DumbPatMatcher();
    }else{
      Debug("matching-arith") << "Generated arithmetic pattern for " << pat << ": " << std::endl;
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
      }
      ArithMatcher am3 (pat, qe);
      TestMatcher<ArithMatcher, LegalTest>
        am2(am3,LegalTest());
      /* generator */
      TermDb* tdb = qe->getTermDatabase();
      CandidateGeneratorTheoryUfType cdtUfEq(pat.getType(),tdb);
      typedef CandidateGeneratorMatcher< CandidateGeneratorTheoryUfType,
                                          TestMatcher<ArithMatcher, LegalTest> > AuxMatcher1;
      return new PatOfMatcher<AuxMatcher1>(AuxMatcher1(cdtUfEq,am2));
    }
  }
};

ArithMatcher::ArithMatcher(Node pat, QuantifiersEngine* qe): d_pattern(pat){

  if(Trigger::getPatternArithmetic(quantifiers::TermDb::getInstConstAttr(pat), pat, d_arith_coeffs ) )
    {
    Debug("inst-match-gen") << "(?) Unknown matching pattern is " << d_pattern << std::endl;
    Assert(false);
  }else{
    Debug("matching-arith") << "Generated arithmetic pattern for " << d_pattern << ": " << std::endl;
    for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
      Debug("matching-arith") << "   " << it->first << " -> " << it->second << std::endl;
    }
  }

};

bool ArithMatcher::reset( TNode t, InstMatch& m, QuantifiersEngine* qe ){
  Debug("matching-arith") << "Matching " << t << " " << d_pattern << std::endl;
  d_binded.clear();
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
      d_binded.push_back(ic);
      //set the rest to zeros
      for( std::map< Node, Node >::iterator it = d_arith_coeffs.begin(); it != d_arith_coeffs.end(); ++it ){
        if( !it->first.isNull() ){
          if( m.find( it->first )==m.end() ){
            m.set( it->first, NodeManager::currentNM()->mkConst( Rational(0) ));
            d_binded.push_back(ic);
          }
        }
      }
      Debug("matching-arith") << "Setting " << ic << " to " << tm << std::endl;
      return true;
    }else{
      m.erase(d_binded.begin(), d_binded.end());
      return false;
    }
  }else{
    m.erase(d_binded.begin(), d_binded.end());
    return false;
  }
};

bool ArithMatcher::getNextMatch( InstMatch& m, QuantifiersEngine* qe ){
  m.erase(d_binded.begin(), d_binded.end());
  return false;
};


class MultiPatsMatcher: public PatsMatcher{
private:
  bool d_reset_done;
  std::vector< PatMatcher* > d_patterns;
  InstMatch d_im;
  bool reset( QuantifiersEngine* qe ){
    d_im.clear();
    d_reset_done = true;

    return getNextMatch(qe,true);
  };

  bool getNextMatch(QuantifiersEngine* qe, bool reset){
    const size_t max = d_patterns.size() - 1;
    size_t index = reset ? 0 : max;
    while(true){
      Debug("matching") << "MultiPatsMatcher::index " << index << "/"
                        << max << (reset ? " reset_phase" : "") << std::endl;
      if(reset ?
         d_patterns[index]->reset( d_im, qe ) :
         d_patterns[index]->getNextMatch( d_im, qe )){
        if(index==max) return true;
        ++index;
        reset=true;
      }else{
        if(index==0) return false;
        --index;
        reset=false;
      };
    }
  }

public:
  MultiPatsMatcher(std::vector< Node > & pats, QuantifiersEngine* qe):
    d_reset_done(false){
    Assert(pats.size() > 0);
    for( size_t i=0; i< pats.size(); i++ ){
      d_patterns.push_back(mkPattern(pats[i],qe));
    };
  };
  void resetInstantiationRound( QuantifiersEngine* qe ){
    for( size_t i=0; i< d_patterns.size(); i++ ){
      d_patterns[i]->resetInstantiationRound( qe );
    };
    d_reset_done = false;
    d_im.clear();
  };
  bool getNextMatch( QuantifiersEngine* qe ){
    Assert(d_patterns.size()>0);
    if(d_reset_done) return getNextMatch(qe,false);
    else return reset(qe);
  }
  const InstMatch& getInstMatch(){return d_im;};

  int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe);
};

enum EffiStep{
  ES_STOP,
  ES_GET_MONO_CANDIDATE,
  ES_GET_MULTI_CANDIDATE,
  ES_RESET1,
  ES_RESET2,
  ES_NEXT1,
  ES_NEXT2,
  ES_RESET_OTHER,
  ES_NEXT_OTHER,
};
static inline std::ostream& operator<<(std::ostream& out, const EffiStep& step) {
  switch(step){
  case ES_STOP: out << "STOP"; break;
  case ES_GET_MONO_CANDIDATE: out << "GET_MONO_CANDIDATE"; break;
  case ES_GET_MULTI_CANDIDATE: out << "GET_MULTI_CANDIDATE"; break;
  case ES_RESET1: out << "RESET1"; break;
  case ES_RESET2: out << "RESET2"; break;
  case ES_NEXT1: out << "NEXT1"; break;
  case ES_NEXT2: out << "NEXT2"; break;
  case ES_RESET_OTHER: out << "RESET_OTHER"; break;
  case ES_NEXT_OTHER: out << "NEXT_OTHER"; break;
  }
  return out;
}


int MultiPatsMatcher::addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe){
  //now, try to add instantiation for each match produced
  int addedLemmas = 0;
  resetInstantiationRound( qe );
  d_im.add( baseMatch );
  while( getNextMatch( qe ) ){
    InstMatch im_copy = getInstMatch();
    std::vector< Node > terms;
    for( unsigned i=0; i<quant[0].getNumChildren(); i++ ){
      terms.push_back( im_copy.get( qe, quant, i ) );
    }

    //m.makeInternal( d_quantEngine->getEqualityQuery() );
    if( qe->addInstantiation( quant, terms ) ){
      addedLemmas++;
    }
  }
  //return number of lemmas added
  return addedLemmas;
}

PatsMatcher* mkPatterns( std::vector< Node > pat, QuantifiersEngine* qe ){
  return new MultiPatsMatcher( pat, qe);
}

class MultiEfficientPatsMatcher: public PatsMatcher{
private:
  bool d_phase_mono;
  bool d_phase_new_term;
  std::vector< PatMatcher* > d_patterns;
  std::vector< Matcher* > d_direct_patterns;
  InstMatch d_im;
  EfficientHandler d_eh;
  EfficientHandler::MultiCandidate d_mc;
  InstMatchTrie2Pairs<true> d_cache;
  std::vector<Node> d_pats;
  // bool indexDone( size_t i){
  //   return i == d_c.first.second ||
  //     ( i == d_c.second.second && d_c.second.first.empty());
  // }



  static const EffiStep ES_START = ES_GET_MONO_CANDIDATE;
  EffiStep d_step;

  //return true if it becomes bigger than d_patterns.size() - 1
  bool incrIndex(size_t & index){
    if(index == d_patterns.size() - 1) return true;
    ++index;
    if(index == d_mc.first.second
       || (!d_phase_mono && index == d_mc.second.second))
      return incrIndex(index);
    else return false;
  }

  //return true if it becomes smaller than 0
  bool decrIndex(size_t & index){
    if(index == 0) return true;
    --index;
    if(index == d_mc.first.second
       || (!d_phase_mono && index == d_mc.second.second))
      return decrIndex(index);
    else return false;
  }

  bool resetOther( QuantifiersEngine* qe ){
    return getNextMatchOther(qe,true);
  };


  bool getNextMatchOther(QuantifiersEngine* qe, bool reset){
    size_t index = reset ? 0 : d_patterns.size();
    if(!reset && decrIndex(index)) return false;
    if( reset &&
        (index == d_mc.first.second
         || (!d_phase_mono && index == d_mc.second.second))
        && incrIndex(index)) return true;
    while(true){
      Debug("matching") << "MultiEfficientPatsMatcher::index " << index << "/"
                        << d_patterns.size() - 1 << std::endl;
      if(reset ?
         d_patterns[index]->reset( d_im, qe ) :
         d_patterns[index]->getNextMatch( d_im, qe )){
        if(incrIndex(index)) return true;
        reset=true;
      }else{
        if(decrIndex(index)) return false;
        reset=false;
      };
    }
  }

  inline EffiStep TestMonoCache(QuantifiersEngine* qe){
    if( //!d_phase_new_term ||
       d_pats.size() == 1) return ES_RESET_OTHER;
    if(d_cache.addInstMatch(d_mc.first.second,d_im)){
      Debug("inst-match::cache") << "Cache miss" << d_im << std::endl;
      ++qe->d_statistics.d_mono_candidates_cache_miss;
      return ES_RESET_OTHER;
    } else {
      Debug("inst-match::cache") << "Cache hit" << d_im << std::endl;
      ++qe->d_statistics.d_mono_candidates_cache_hit;
      return ES_NEXT1;
    }
    // ++qe->d_statistics.d_mono_candidates_cache_miss;
    // return ES_RESET_OTHER;
  }

  inline EffiStep TestMultiCache(QuantifiersEngine* qe){
    if(d_cache.addInstMatch(d_mc.first.second,d_mc.second.second,d_im)){
      ++qe->d_statistics.d_multi_candidates_cache_miss;
      return ES_RESET_OTHER;
    } else {
      ++qe->d_statistics.d_multi_candidates_cache_hit;
      return ES_NEXT2;
    }
  }


public:

  bool getNextMatch( QuantifiersEngine* qe ){
    Assert( d_step == ES_START || d_step == ES_NEXT_OTHER || d_step == ES_STOP );
    while(true){
      Debug("matching") << "d_step=" << d_step << " "
                        << "d_im=" << d_im << std::endl;
      switch(d_step){
      case ES_GET_MONO_CANDIDATE:
        Assert(d_im.empty());
        if(d_phase_new_term ? d_eh.getNextMonoCandidate(d_mc.first) : d_eh.getNextMonoCandidateNewTerm(d_mc.first)){
          if(d_phase_new_term) ++qe->d_statistics.d_num_mono_candidates_new_term;
          else ++qe->d_statistics.d_num_mono_candidates;
          d_phase_mono = true;
          d_step = ES_RESET1;
        } else if (!d_phase_new_term){
          d_phase_new_term = true;
          d_step = ES_GET_MONO_CANDIDATE;
        } else {
          d_phase_new_term = false;
          d_step = ES_GET_MULTI_CANDIDATE;
        }
        break;
      case ES_GET_MULTI_CANDIDATE:
        Assert(d_im.empty());
        if(d_eh.getNextMultiCandidate(d_mc)){
          ++qe->d_statistics.d_num_multi_candidates;
          d_phase_mono = false;
          d_step = ES_RESET1;
        } else d_step = ES_STOP;
        break;
      case ES_RESET1:
        if(d_direct_patterns[d_mc.first.second]->reset(d_mc.first.first,d_im,qe))
          d_step = d_phase_mono ? TestMonoCache(qe) : ES_RESET2;
        else d_step = d_phase_mono ? ES_GET_MONO_CANDIDATE : ES_GET_MULTI_CANDIDATE;
        break;
      case ES_RESET2:
        Assert(!d_phase_mono);
        if(d_direct_patterns[d_mc.second.second]->reset(d_mc.second.first,d_im,qe))
          d_step = TestMultiCache(qe);
        else d_step = ES_NEXT1;
        break;
      case ES_NEXT1:
        if(d_direct_patterns[d_mc.first.second]->getNextMatch(d_im,qe))
          d_step = d_phase_mono ? TestMonoCache(qe) : ES_RESET2;
        else d_step = d_phase_mono ? ES_GET_MONO_CANDIDATE : ES_GET_MULTI_CANDIDATE;
        break;
      case ES_NEXT2:
        if(d_direct_patterns[d_mc.second.second]->getNextMatch(d_im,qe))
          d_step = TestMultiCache(qe);
        else d_step = ES_NEXT1;
        break;
      case ES_RESET_OTHER:
        if(resetOther(qe)){
          d_step = ES_NEXT_OTHER;
          return true;
        } else d_step = d_phase_mono ? ES_NEXT1 : ES_NEXT2;
        break;
      case ES_NEXT_OTHER:
        {
          if(!getNextMatchOther(qe,false)){
            d_step = d_phase_mono ? ES_NEXT1 : ES_NEXT2;
          }else{
            d_step = ES_NEXT_OTHER;
            return true;
          }
        }
        break;
      case ES_STOP:
        Assert(d_im.empty());
        return false;
      }
    }
  }

  MultiEfficientPatsMatcher(std::vector< Node > & pats, QuantifiersEngine* qe):
    d_eh(qe->getTheoryEngine()->getSatContext()),
    d_cache(qe->getTheoryEngine()->getSatContext(),qe,pats.size()),
    d_pats(pats), d_step(ES_START) {
    Assert(pats.size() > 0);
    for( size_t i=0; i< pats.size(); i++ ){
      d_patterns.push_back(mkPattern(pats[i],qe));
      if(pats[i].getKind()==kind::INST_CONSTANT){
        d_direct_patterns.push_back(new VarMatcher(pats[i],qe));
      } else if( pats[i].getKind() == kind::NOT && pats[i][0].getKind() == kind::EQUAL){
        d_direct_patterns.push_back(new ApplyMatcher(pats[i][0],qe));
      } else {
        d_direct_patterns.push_back(new ApplyMatcher(pats[i],qe));
      }
    };
    EfficientEMatcher* eem = qe->getEfficientEMatcher();
    eem->registerEfficientHandler(d_eh, pats);
  };
  void resetInstantiationRound( QuantifiersEngine* qe ){
    Assert(d_step == ES_START || d_step == ES_STOP);
    for( size_t i=0; i< d_patterns.size(); i++ ){
      d_patterns[i]->resetInstantiationRound( qe );
      d_direct_patterns[i]->resetInstantiationRound( qe );
    };
    d_step = ES_START;
    d_phase_new_term = false;
    Assert(d_im.empty());
  };

  const InstMatch& getInstMatch(){return d_im;};

  int addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe);
};

int MultiEfficientPatsMatcher::addInstantiations( InstMatch& baseMatch, Node quant, QuantifiersEngine* qe){
  //now, try to add instantiation for each match produced
  int addedLemmas = 0;
  Assert(baseMatch.empty());
  resetInstantiationRound( qe );
  while( getNextMatch( qe ) ){
    InstMatch im_copy = getInstMatch();
    std::vector< Node > terms;
    for( unsigned i=0; i<quant[0].getNumChildren(); i++ ){
      terms.push_back( im_copy.get( qe, quant, i ) );
    }

    //m.makeInternal( d_quantEngine->getEqualityQuery() );
    if( qe->addInstantiation( quant, terms ) ){
      addedLemmas++;
    }
  }
  //return number of lemmas added
  return addedLemmas;
};

PatsMatcher* mkPatternsEfficient( std::vector< Node > pat, QuantifiersEngine* qe ){
  return new MultiEfficientPatsMatcher( pat, qe);
}

} /* CVC4::theory::rrinst */
} /* CVC4::theory */
} /* CVC4 */
