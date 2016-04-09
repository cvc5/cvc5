/*********************                                                        */
/*! \file inst_propagator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Propagate mechanism for instantiations
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_INST_PROPAGATOR_H
#define __CVC4__QUANTIFIERS_INST_PROPAGATOR_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers_engine.h"
#include "theory/quantifiers/term_database.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class EqualityQueryInstProp : public EqualityQuery {
private:
  /** pointer to quantifiers engine */
  QuantifiersEngine* d_qe;
public:
  EqualityQueryInstProp( QuantifiersEngine* qe );
  ~EqualityQueryInstProp(){};
  /** reset */
  bool reset( Theory::Effort e );
  /** identify */
  std::string identify() const { return "EqualityQueryInstProp"; }
  /** extends engine */
  bool extendsEngine() { return true; }
  /** contains term */
  bool hasTerm( Node a );
  /** get the representative of the equivalence class of a */
  Node getRepresentative( Node a );
  /** returns true if a and b are equal in the current context */
  bool areEqual( Node a, Node b );
  /** returns true is a and b are disequal in the current context */
  bool areDisequal( Node a, Node b );
  /** get the equality engine associated with this query */
  eq::EqualityEngine* getEngine();
  /** get the equivalence class of a */
  void getEquivalenceClass( Node a, std::vector< Node >& eqc );
  /** get congruent term */
  TNode getCongruentTerm( Node f, std::vector< TNode >& args );
public:
  /** get the representative of the equivalence class of a, with explanation */
  Node getRepresentativeExp( Node a, std::vector< Node >& exp );
  /** returns true if a and b are equal in the current context */
  bool areEqualExp( Node a, Node b, std::vector< Node >& exp );
  /** returns true is a and b are disequal in the current context */
  bool areDisequalExp( Node a, Node b, std::vector< Node >& exp );
private:
  /** term index */
  std::map< Node, TermArgTrie > d_func_map_trie;
  /** union find for terms beyond what is stored in equality engine */
  std::map< Node, Node > d_uf;
  std::map< Node, std::vector< Node > > d_uf_exp;
  Node getUfRepresentative( Node a, std::vector< Node >& exp );
  /** disequality list, stores explanations */
  std::map< Node, std::map< Node, Node > > d_diseq_list;
  /** add arg */
  void addArgument( std::vector< TNode >& args, std::vector< TNode >& props, Node n, bool is_prop, bool pol );
public:
  enum {
    STATUS_MERGED_KNOWN,
    STATUS_MERGED_UNKNOWN,
    STATUS_NONE,
  };
  /** set equal */
  int setEqual( Node& a, Node& b, std::vector< Node >& reason );
  Node d_true;
  Node d_false;
public:
  //for explanations
  static void merge_exp( std::vector< Node >& v, std::vector< Node >& v_to_merge, int up_to_size = -1 );

  Node evaluateTermExp( TNode n, std::vector< Node >& exp, std::map< TNode, Node >& visited, bool hasPol, bool pol,
                        std::map< Node, bool >& watch_list_out, std::vector< TNode >& props );
  static bool isLiteral( Node n );
};

class InstPropagator : public QuantifiersUtil {
private:
  /** pointer to quantifiers engine */
  QuantifiersEngine* d_qe;
  /** notify class */
  class InstantiationNotifyInstPropagator : public InstantiationNotify {
    InstPropagator& d_ip;
  public:
    InstantiationNotifyInstPropagator(InstPropagator& ip): d_ip(ip) {}
    virtual void notifyInstantiation( unsigned quant_e, Node q, Node lem, std::vector< Node >& terms, Node body ) { d_ip.notifyInstantiation( quant_e, q, lem, terms, body ); }
  };
  InstantiationNotifyInstPropagator d_notify;
  /** notify instantiation method */
  void notifyInstantiation( unsigned quant_e, Node q, Node lem, std::vector< Node >& terms, Node body );
  /** equality query */
  EqualityQueryInstProp d_qy;
  class InstInfo {
  public:
    bool d_active;
    Node d_q;
    Node d_lem;
    std::vector< Node > d_terms;
    // the current entailed body
    Node d_curr;
    //explanation for current entailed body
    std::vector< Node > d_curr_exp;
    void init( Node q, Node lem, std::vector< Node >& terms, Node body );
  };
  /** instantiation count/info */
  unsigned d_icount;
  std::map< unsigned, InstInfo > d_ii;
  std::map< TNode, unsigned > d_conc_to_id[2];
  /** are we in conflict */
  bool d_conflict;
  /** watch list */
  std::map< Node, std::map< unsigned, bool > > d_watch_list;
  /** update list */
  std::vector< unsigned > d_update_list;
  /** relevant instances */
  std::map< unsigned, bool > d_relevant_inst;
private:
  bool update( unsigned id, InstInfo& i, bool firstTime = false );
  void propagate( Node a, Node b, bool pol, std::vector< Node >& exp );
  void conflict( std::vector< Node >& exp );
  bool cacheConclusion( unsigned id, Node body, int prop_index = 0 );
  void addRelevantInstances( std::vector< Node >& exp, const char * c );

  void debugPrintExplanation( std::vector< Node >& exp, const char * c );
public:
  InstPropagator( QuantifiersEngine* qe );
  ~InstPropagator(){}
  /** reset */
  bool reset( Theory::Effort e );
  /** identify */
  std::string identify() const { return "InstPropagator"; }
  /** get the notify mechanism */
  InstantiationNotify* getInstantiationNotify() { return &d_notify; }
};

}
}
}

#endif
