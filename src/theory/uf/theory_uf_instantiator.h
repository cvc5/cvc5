/*********************                                                        */
/*! \file theory_uf_instantiator.h
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
 ** \brief Theory uf instantiator
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_INSTANTIATOR_H
#define __CVC4__THEORY_UF_INSTANTIATOR_H

#include "theory/uf/inst_strategy.h"

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdchunk_list.h"

#include "util/statistics_registry.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/trigger.h"
#include "util/ntuple.h"
#include "context/cdqueue.h"

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class TermDb;
}

namespace uf {

class InstantiatorTheoryUf;
class HandlerPcDispatcher;
class HandlerPpDispatcher;

typedef std::set<Node> SetNode;

template<class T>
class CleanUpPointer{
public:
  inline void operator()(T** e){
    delete(*e);
  };
};

class EfficientHandler{
public:
  typedef std::pair< Node, size_t > MonoCandidate;
  typedef std::pair< MonoCandidate, MonoCandidate > MultiCandidate;
  typedef std::pair< SetNode, size_t > MonoCandidates;
  typedef std::pair< MonoCandidates, MonoCandidates > MultiCandidates;
private:
  /* Queue of candidates */
  typedef context::CDQueue< MonoCandidates *, CleanUpPointer<MonoCandidates> > MonoCandidatesQueue;
  typedef context::CDQueue< MultiCandidates *, CleanUpPointer<MultiCandidates> > MultiCandidatesQueue;
  MonoCandidatesQueue d_monoCandidates;
  typedef uf::SetNode::iterator SetNodeIter;
  context::CDO<SetNodeIter> d_si;
  context::CDO<bool> d_mono_not_first;

  MonoCandidatesQueue d_monoCandidatesNewTerm;
  context::CDO<SetNodeIter> d_si_new_term;
  context::CDO<bool> d_mono_not_first_new_term;


  MultiCandidatesQueue d_multiCandidates;
  context::CDO<SetNodeIter> d_si1;
  context::CDO<SetNodeIter> d_si2;
  context::CDO<bool> d_multi_not_first;


  friend class InstantiatorTheoryUf;
  friend class HandlerPcDispatcher;
  friend class HandlerPpDispatcher;
  friend class HandlerNewTermDispatcher;
protected:
  void addMonoCandidate(SetNode & s, size_t index){
    Assert(!s.empty());
    d_monoCandidates.push(new MonoCandidates(s,index));
  }
  void addMonoCandidateNewTerm(SetNode & s, size_t index){
    Assert(!s.empty());
    d_monoCandidatesNewTerm.push(new MonoCandidates(s,index));
  }
  void addMultiCandidate(SetNode & s1, size_t index1, SetNode & s2, size_t index2){
    Assert(!s1.empty() && !s2.empty());
    d_multiCandidates.push(new MultiCandidates(MonoCandidates(s1,index1),
                                               MonoCandidates(s2,index2)));
  }
public:
  EfficientHandler(context::Context * c):
    //false for d_mono_not_first beacause its the default constructor
    d_monoCandidates(c), d_si(c), d_mono_not_first(c,false),
    d_monoCandidatesNewTerm(c), d_si_new_term(c),
    d_mono_not_first_new_term(c,false),
    d_multiCandidates(c) , d_si1(c), d_si2(c), d_multi_not_first(c,false) {};

  bool getNextMonoCandidate(MonoCandidate & candidate){
    if(d_monoCandidates.empty()) return false;
    const MonoCandidates * front = d_monoCandidates.front();
    SetNodeIter si_tmp;
    if(!d_mono_not_first){
      Assert(front->first.begin() != front->first.end());
      d_mono_not_first = true;
      si_tmp=front->first.begin();
    }else{
      si_tmp = d_si;
      ++si_tmp;
    };
    if(si_tmp != front->first.end()){
      candidate.first = (*si_tmp);
      candidate.second = front->second;
      d_si = si_tmp;
      Debug("efficienthandler") << "Mono produces " << candidate.first << " for " << candidate.second << std::endl;
      return true;
    };
    d_monoCandidates.pop();
    d_mono_not_first = false;
    return getNextMonoCandidate(candidate);
  };

  bool getNextMonoCandidateNewTerm(MonoCandidate & candidate){
    if(d_monoCandidatesNewTerm.empty()) return false;
    const MonoCandidates * front = d_monoCandidatesNewTerm.front();
    SetNodeIter si_tmp;
    if(!d_mono_not_first_new_term){
      Assert(front->first.begin() != front->first.end());
      d_mono_not_first_new_term = true;
      si_tmp=front->first.begin();
    }else{
      si_tmp = d_si_new_term;
      ++si_tmp;
    };
    if(si_tmp != front->first.end()){
      candidate.first = (*si_tmp);
      candidate.second = front->second;
      d_si_new_term = si_tmp;
      Debug("efficienthandler") << "Mono produces " << candidate.first << " for " << candidate.second << std::endl;
      return true;
    };
    d_monoCandidatesNewTerm.pop();
    d_mono_not_first_new_term = false;
    return getNextMonoCandidateNewTerm(candidate);
  };

  bool getNextMultiCandidate(MultiCandidate & candidate){
    if(d_multiCandidates.empty()) return false;
    const MultiCandidates* front = d_multiCandidates.front();
    SetNodeIter si1_tmp;
    SetNodeIter si2_tmp;
    if(!d_multi_not_first){
      Assert(front->first.first.begin() != front->first.first.end());
      Assert(front->second.first.begin() != front->second.first.end());
      si1_tmp = front->first.first.begin();
      si2_tmp = front->second.first.begin();
    }else{
      si1_tmp = d_si1;
      si2_tmp = d_si2;
      ++si2_tmp;
    };
    if(si2_tmp != front->second.first.end()){
      candidate.first.first = *si1_tmp;
      candidate.first.second = front->first.second;
      candidate.second.first = *si2_tmp;
      candidate.second.second = front->second.second;
      if(!d_multi_not_first){d_si1 = si1_tmp; d_multi_not_first = true; };
      d_si2 = si2_tmp;
      Debug("efficienthandler") << "Multi1 produces "
                                << candidate.first.first << " for "
                                << candidate.first.second << " and "
                                << candidate.second.first << " for "
                                << candidate.second.second << " and "
                                << std::endl;
      return true;
    }; // end of the second set
    si2_tmp = front->second.first.begin();
    ++si1_tmp;
    if(si1_tmp != front->first.first.end()){
      candidate.first.first = *si1_tmp;
      candidate.first.second = front->first.second;
      candidate.second.first = *si2_tmp;
      candidate.second.second = front->second.second;
      d_si1 = si1_tmp;
      d_si2 = si2_tmp;
      Debug("efficienthandler") << "Multi2 produces "
                                << candidate.first.first << " for "
                                << candidate.first.second << " and "
                                << candidate.second.first << " for "
                                << candidate.second.second << " and "
                                << std::endl;
      return true;
    }; // end of the first set
    d_multiCandidates.pop();
    d_multi_not_first = false;
    return getNextMultiCandidate(candidate);
  }
};

class PcDispatcher{
public:
  virtual ~PcDispatcher(){};
  /* Send the node to the dispatcher */
  virtual void send(SetNode & s) = 0;
};


class HandlerPcDispatcher: public PcDispatcher{
  EfficientHandler* d_handler;
  size_t d_index;
public:
  HandlerPcDispatcher(EfficientHandler* handler, size_t index):
    d_handler(handler), d_index(index) {};
  void send(SetNode & s){
    d_handler->addMonoCandidate(s,d_index);
  }
};


/** All the dispatcher that correspond to this node */
class NodePcDispatcher: public PcDispatcher{
#ifdef CVC4_DEBUG
public:
  Node pat;
#endif/* CVC4_DEBUG*/
private:
  std::vector<HandlerPcDispatcher> d_dis;
public:
  void send(SetNode & s){
    Assert(!s.empty());
    for(std::vector<HandlerPcDispatcher>::iterator i = d_dis.begin(), end = d_dis.end();
        i != end; ++i){
      (*i).send(s);
    }
  }
  void addPcDispatcher(EfficientHandler* handler, size_t index){
    d_dis.push_back(HandlerPcDispatcher(handler,index));
  }
};


class HandlerNewTermDispatcher: public PcDispatcher{
  EfficientHandler* d_handler;
  size_t d_index;
public:
  HandlerNewTermDispatcher(EfficientHandler* handler, size_t index):
    d_handler(handler), d_index(index) {};
  void send(SetNode & s){
    d_handler->addMonoCandidateNewTerm(s,d_index);
  }
};

/** All the dispatcher that correspond to this node */
class NodeNewTermDispatcher: public PcDispatcher{
#ifdef CVC4_DEBUG
public:
  Node pat;
#endif/* CVC4_DEBUG*/
private:
  std::vector<HandlerNewTermDispatcher> d_dis;
public:
  void send(SetNode & s){
    Assert(!s.empty());
    for(std::vector<HandlerNewTermDispatcher>::iterator i = d_dis.begin(), end = d_dis.end();
        i != end; ++i){
      (*i).send(s);
    }
  }
  void addNewTermDispatcher(EfficientHandler* handler, size_t index){
    d_dis.push_back(HandlerNewTermDispatcher(handler,index));
  }
};

class PpDispatcher{
public:
  virtual ~PpDispatcher(){};
  /* Send the node to the dispatcher */
  virtual void send(SetNode & s1, SetNode & s2, SetNode & sinter) = 0;
};


class HandlerPpDispatcher: public PpDispatcher{
  EfficientHandler* d_handler;
  size_t d_index1;
  size_t d_index2;
public:
  HandlerPpDispatcher(EfficientHandler* handler, size_t index1, size_t index2):
    d_handler(handler), d_index1(index1), d_index2(index2) {};
  void send(SetNode & s1, SetNode & s2, SetNode & sinter){
    if(d_index1 == d_index2){
      if(!sinter.empty())
        d_handler->addMonoCandidate(sinter,d_index1);
    }else{
      d_handler->addMultiCandidate(s1,d_index1,s2,d_index2);
    }
  }
};


/** All the dispatcher that correspond to this node */
class NodePpDispatcher: public PpDispatcher{
#ifdef CVC4_DEBUG
public:
  Node pat1;
  Node pat2;
#endif/* CVC4_DEBUG */
private:
  std::vector<HandlerPpDispatcher> d_dis;
  void send(SetNode & s1, SetNode & s2, SetNode & inter){
    for(std::vector<HandlerPpDispatcher>::iterator i = d_dis.begin(), end = d_dis.end();
        i != end; ++i){
      (*i).send(s1,s2,inter);
    }
  }
public:
  void send(SetNode & s1, SetNode & s2){
    // can be done in HandlerPpDispatcher lazily
    Assert(!s1.empty() && !s2.empty());
    SetNode inter;
    std::set_intersection( s1.begin(), s1.end(), s2.begin(), s2.end(),
                           std::inserter( inter, inter.begin() ) );
    send(s1,s2,inter);
  }
  void addPpDispatcher(EfficientHandler* handler, size_t index1, size_t index2){
    d_dis.push_back(HandlerPpDispatcher(handler,index1,index2));
  }
};

//equivalence class info
class EqClassInfo
{
public:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDChunkList<Node> NodeList;
public:
  //a list of operators that occur as top symbols in this equivalence class
  //  Efficient E-Matching for SMT Solvers: "funs"
  BoolMap d_funs;
  //a list of operators f for which a term of the form f( ... t ... ) exists
  //  Efficient E-Matching for SMT Solvers: "pfuns"
  BoolMap d_pfuns;
  //a list of equivalence classes that are disequal
  BoolMap d_disequal;
public:
  EqClassInfo( context::Context* c );
  ~EqClassInfo(){}
  //set member
  void setMember( Node n, quantifiers::TermDb* db );
  //has function "funs"
  bool hasFunction( Node op );
  //has parent "pfuns"
  bool hasParent( Node op );
  //merge with another eq class info
  void merge( EqClassInfo* eci );
};

class InstantiatorTheoryUf : public Instantiator{
  friend class ::CVC4::theory::inst::InstMatchGenerator;
  friend class ::CVC4::theory::quantifiers::TermDb;
protected:
  typedef context::CDHashMap<Node, bool, NodeHashFunction> BoolMap;
  typedef context::CDHashMap<Node, int, NodeHashFunction> IntMap;
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeLists;
  /** map to representatives used */
  std::map< Node, Node > d_ground_reps;
protected:
  /** instantiation strategies */
  InstStrategyUserPatterns* d_isup;
public:
  InstantiatorTheoryUf(context::Context* c, CVC4::theory::QuantifiersEngine* qe, Theory* th);
  ~InstantiatorTheoryUf() {
    for(std::map< Node, std::pair<NodePcDispatcher*, NodePpDispatcher*> >::iterator
          i = d_pat_cand_gens.begin(), end = d_pat_cand_gens.end();
        i != end; i++){
      delete(i->second.first);
      delete(i->second.second);
    }
  }
  /** assertNode method */
  void assertNode( Node assertion );
  /** Pre-register a term.  Done one time for a Node, ever. */
  void preRegisterTerm( Node t );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryUf"); }
  /** debug print */
  void debugPrint( const char* c );
  /** add user pattern */
  void addUserPattern( Node f, Node pat );
private:
  /** reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** calculate matches for quantifier f at effort */
  int process( Node f, Theory::Effort effort, int e );
public:
  /** statistics class */
  class Statistics {
  public:
    //IntStat d_instantiations;
    IntStat d_instantiations_ce_solved;
    IntStat d_instantiations_e_induced;
    IntStat d_instantiations_user_pattern;
    IntStat d_instantiations_guess;
    IntStat d_instantiations_auto_gen;
    IntStat d_instantiations_auto_gen_min;
    IntStat d_splits;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
public:
  /** the base match */
  std::map< Node, InstMatch > d_baseMatch;
private:
  //for each equivalence class
  std::map< Node, EqClassInfo* > d_eqc_ops;
public:
  /** general queries about equality */
  bool hasTerm( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
  Node getRepresentative( Node a );
  Node getInternalRepresentative( Node a );
  eq::EqualityEngine* getEqualityEngine();
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  /** general creators of candidate generators */
  rrinst::CandidateGenerator* getRRCanGenClasses();
  rrinst::CandidateGenerator* getRRCanGenClass();
  /** new node */
  void newEqClass( TNode n );
  /** merge */
  void merge( TNode a, TNode b );
  /** assert terms are disequal */
  void assertDisequal( TNode a, TNode b, TNode reason );
  /** get equivalence class info */
  EqClassInfo* getEquivalenceClassInfo( Node n );
  EqClassInfo* getOrCreateEquivalenceClassInfo( Node n );
  typedef std::vector< std::pair< Node, int > > Ips;
  typedef std::map< Node, std::vector< std::pair< Node, Ips > > > PpIpsMap;
  typedef std::map< Node, std::vector< triple< size_t, Node, Ips > > > MultiPpIpsMap;

private:
  /** Parent/Child Pairs (for efficient E-matching)
      So, for example, if we have the pattern f( g( x ) ), then d_pc_pairs[g][f][f( g( x ) )] = { f.0 }.
  */
  std::map< Node, std::map< Node, std::vector< std::pair< NodePcDispatcher*, Ips > > > > d_pc_pairs;
  /** Parent/Parent Pairs (for efficient E-matching) */
  std::map< Node, std::map< Node, std::vector< triple< NodePpDispatcher*, Ips, Ips > > > > d_pp_pairs;
  /** Constants/Child Pairs
      So, for example, if we have the pattern f( x ) = c, then d_pc_pairs[f][c] = ..., pcdispatcher, ...
  */
  //TODO constant in pattern can use the same thing just add an Ips
  std::map< Node, std::map< Node, NodePcDispatcher* > > d_cc_pairs;
  /** list of all candidate generators for each operator */
  std::map< Node, NodeNewTermDispatcher > d_cand_gens;
  /** list of all candidate generators for each type */
  std::map< TypeNode, NodeNewTermDispatcher > d_cand_gen_types;
  /** map from patterns to candidate generators */
  std::map< Node, std::pair<NodePcDispatcher*, NodePpDispatcher*> > d_pat_cand_gens;
  /** helper functions */
  void registerPatternElementPairs2( Node pat, Ips& ips,
                                     PpIpsMap & pp_ips_map, NodePcDispatcher* npc);
  void registerPatternElementPairs( Node pat, PpIpsMap & pp_ips_map,
                                    NodePcDispatcher* npc, NodePpDispatcher* npp);
  /** find the pp-pair between pattern inside multi-pattern*/
  void combineMultiPpIpsMap(PpIpsMap & pp_ips_map, MultiPpIpsMap & multi_pp_ips_map,
                            EfficientHandler& eh, size_t index2,
                            const std::vector<Node> & pats); //pats for debug
  /** compute candidates for pc pairs */
  void computeCandidatesPcPairs( Node a, EqClassInfo*, Node b, EqClassInfo* );
  /** compute candidates for pp pairs */
  void computeCandidatesPpPairs( Node a, EqClassInfo*, Node b, EqClassInfo* );
  /** compute candidates for cc pairs */
  void computeCandidatesConstants( Node a, EqClassInfo*, Node b, EqClassInfo* );
  /** collect terms based on inverted path string */
  void collectTermsIps( Ips& ips, SetNode& terms, int index);
  bool collectParentsTermsIps( Node n, Node f, int arg, SetNode& terms, bool addRep, bool modEq = true );
public:
  void collectTermsIps( Ips& ips, SetNode& terms);
  /** Register candidate generator cg for pattern pat. (for use with efficient e-matching)
      This request will ensure that calls will be made to cg->addCandidate( n ) for all
      ground terms n that are relevant for matching with pat.
  */
private:
  /** triggers */
  std::map< Node, std::vector< inst::Trigger* > > d_op_triggers;
public:
  /** register trigger (for eager quantifier instantiation) */
  void registerTrigger( inst::Trigger* tr, Node op );
  void registerEfficientHandler( EfficientHandler& eh, const std::vector<Node> & pat );
public:
  void newTerms(SetNode& s);
public:
  /** output eq class */
  void outputEqClass( const char* c, Node n );
  /** output inverted path string */
  void outputIps( const char* c, Ips& ips );
};/* class InstantiatorTheoryUf */

/** equality query object using instantiator theory uf */
class EqualityQueryInstantiatorTheoryUf : public EqualityQuery
{
private:
  /** pointer to instantiator uf class */
  InstantiatorTheoryUf* d_ith;
public:
  EqualityQueryInstantiatorTheoryUf( InstantiatorTheoryUf* ith ) : d_ith( ith ){}
  ~EqualityQueryInstantiatorTheoryUf(){}
  /** general queries about equality */
  bool hasTerm( Node a ) { return d_ith->hasTerm( a ); }
  Node getRepresentative( Node a ) { return d_ith->getRepresentative( a ); }
  bool areEqual( Node a, Node b ) { return d_ith->areEqual( a, b ); }
  bool areDisequal( Node a, Node b ) { return d_ith->areDisequal( a, b ); }
  Node getInternalRepresentative( Node a ) { return d_ith->getInternalRepresentative( a ); }
  eq::EqualityEngine* getEngine() { return d_ith->getEqualityEngine(); }
  void getEquivalenceClass( Node a, std::vector< Node >& eqc ) { d_ith->getEquivalenceClass( a, eqc ); }
}; /* EqualityQueryInstantiatorTheoryUf */

}
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY_UF_INSTANTIATOR_H */
