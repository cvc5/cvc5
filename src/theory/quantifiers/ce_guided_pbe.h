/*********************                                                        */
/*! \file ce_guided_pbe.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_PBE_H
#define __CVC4__THEORY__QUANTIFIERS__CE_GUIDED_PBE_H

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegConjecture;
class CegConjecturePbe;
class CegEntailmentInfer;

class CegConjecturePbe {
private:
  QuantifiersEngine* d_qe;
  quantifiers::TermDbSygus * d_tds;
  CegConjecture* d_parent;

  std::map< Node, bool > d_examples_invalid;
  std::map< Node, bool > d_examples_out_invalid;
  std::map< Node, std::vector< std::vector< Node > > > d_examples;
  std::map< Node, std::vector< Node > > d_examples_out;
  std::map< Node, std::vector< Node > > d_examples_term;
  
  void collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol );
  bool d_is_pbe;
public:  
  Node d_true;
  Node d_false;
  enum {
    enum_io,
    enum_ite_condition,
    enum_concat_term,
    enum_any,
  };
  enum {
    strat_ITE,
    strat_CONCAT,
    strat_ID,
  };
public:
  CegConjecturePbe( QuantifiersEngine * qe, CegConjecture * p );
  ~CegConjecturePbe();

  void initialize( Node n, std::vector< Node >& candidates, std::vector< Node >& lemmas );
  bool getPbeExamples( Node v, std::vector< std::vector< Node > >& exs, 
                       std::vector< Node >& exos, std::vector< Node >& exts);
  bool isPbe() { return d_is_pbe; }
private:  // for registration
  void collectEnumeratorTypes( Node c, TypeNode tn, unsigned enum_role );
  void registerEnumerator( Node et, Node c, TypeNode tn, unsigned enum_role, bool inSearch );
  void staticLearnRedundantOps( Node c, std::vector< Node >& lemmas );
  void staticLearnRedundantOps( Node c, Node e, std::map< Node, bool >& visited, std::vector< Node >& redundant, 
                                std::vector< Node >& lemmas, int ind );

  /** register candidate conditional */
  bool inferTemplate( unsigned k, Node n, std::map< Node, unsigned >& templ_var_index, std::map< unsigned, unsigned >& templ_injection );  
  /** get guard status */
  int getGuardStatus( Node g );
public:
  class IndexFilter {
  public:
    IndexFilter(){}
    void mk( std::vector< Node >& vals, bool pol = true );
    std::map< unsigned, unsigned > d_next;
    unsigned start();
    unsigned next( unsigned i );
    void clear() { d_next.clear(); }
    bool isEq( std::vector< Node >& vs, Node v );
  };
private:
  // subsumption trie
  class SubsumeTrie {
  private:
    Node addTermInternal( CegConjecturePbe * pbe, Node t, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, bool spol, IndexFilter * f, 
                          unsigned index, int status, bool checkExistsOnly, bool checkSubsume );
  public:
    SubsumeTrie(){}
    Node d_term;
    std::map< Node, SubsumeTrie > d_children;
    // adds term to the trie, removes based on subsumption
    Node addTerm( CegConjecturePbe * pbe, Node t, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // adds condition to the trie (does not do subsumption)
    Node addCond( CegConjecturePbe * pbe, Node c, std::vector< Node >& vals, bool pol, IndexFilter * f = NULL );
    // returns the set of terms that are subsets of vals
    void getSubsumed( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // returns the set of terms that are supersets of vals
    void getSubsumedBy( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed_by, IndexFilter * f = NULL );
  private:
    void getLeavesInternal( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f, 
                            unsigned index, int status );
  public:
    // v[-1,1,0] -> children always false, always true, both
    void getLeaves( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f = NULL );
  public:
    bool isEmpty() { return d_term.isNull() && d_children.empty(); }
    void clear() {
      d_term = Node::null();
      d_children.clear(); 
    }
  };

  class EnumInfo {
  private:
    /** an OR of all in d_enum_res */
    //std::vector< Node > d_enum_total;
    //bool d_enum_total_true;
    Node d_enum_solved;
  public:
    EnumInfo() : d_role( enum_io ){}
    Node d_parent_candidate;
    
    // for template
    Node d_template;
    Node d_template_arg;
    
    // TODO : make private
    unsigned d_role;
    
    Node d_active_guard;
    std::vector< Node > d_enum_slave;
    /** values we have enumerated */
    std::vector< Node > d_enum_vals;
    /** this either stores the values of f( I ) for inputs 
        or the value of f( I ) = O if d_role==enum_io
    */
    std::vector< std::vector< Node > > d_enum_vals_res;
    std::vector< Node > d_enum_subsume;
    std::map< Node, unsigned > d_enum_val_to_index;
    SubsumeTrie d_term_trie;
  public:
    bool isTemplated() { return !d_template.isNull(); }
    void addEnumValue( CegConjecturePbe * pbe, Node v, std::vector< Node >& results );
    void setSolved( Node slv );
    bool isSolved() { return !d_enum_solved.isNull(); }
    Node getSolved() { return d_enum_solved; }
  };
  std::map< Node, EnumInfo > d_einfo;
private:
  class CandidateInfo;
  class EnumTypeInfoStrat {
  public:
    unsigned d_this;
    /** conditional solutions */
    std::vector< TypeNode > d_csol_cts;
    std::vector< Node > d_cenum;
  };
  class EnumTypeInfo {
  public:
    EnumTypeInfo() : d_parent( NULL ){}
    CandidateInfo * d_parent;
    // role -> _
    std::map< unsigned, Node > d_enum;
    TypeNode d_this_type;
    // strategies for enum_io role
    std::map< Node, EnumTypeInfoStrat > d_strat;
    bool isSolved( CegConjecturePbe * pbe );
  };
  class CandidateInfo {
  public:
    CandidateInfo() : d_check_sol( false ), d_cond_count( 0 ){}
    Node d_this_candidate;
    TypeNode d_root;
    std::map< TypeNode, EnumTypeInfo > d_tinfo;
    std::vector< Node > d_esym_list;
    // role -> sygus type -> enumerator
    std::map< TypeNode, Node > d_search_enum;
    bool d_check_sol;
    unsigned d_cond_count;
    Node d_solution;
    void initialize( Node c );
    void initializeType( TypeNode tn );
    Node getRootEnumerator();
    bool isNonTrivial();
  };
  //  candidate -> sygus type -> info
  std::map< Node, CandidateInfo > d_cinfo;

  /** add enumerated value */
  void addEnumeratedValue( Node x, Node v, std::vector< Node >& lems );
  bool getExplanationForEnumeratorExclude( Node c, Node x, Node v, std::vector< Node >& results, EnumInfo& ei, std::vector< Node >& exp );
  
private:  
  // filtering verion
  /*
  class FilterSubsumeTrie {
  public:
    SubsumeTrie d_trie;
    IndexFilter d_filter;
    Node addTerm( Node t, std::vector< bool >& vals, std::vector< Node >& subsumed, bool checkExistsOnly = false ){
      return d_trie.addTerm( t, vals, subsumed, &d_filter, d_filter.start(), checkExistsOnly );
    }
  };
  */
  class UnifContext {
  public:
    UnifContext() : d_has_string_pos(0) {}
    //IndexFilter d_filter;
    // the value of the context conditional
    std::vector< Node > d_vals;
    // update the examples
    bool updateContext( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol );
    // the position in the strings
    std::vector< unsigned > d_str_pos;
    // 0 : pos not modified, 1 : pos indicates suffix incremented, -1 : pos indicates prefix incremented
    int d_has_string_pos;
    // update the string examples
    bool updateStringPosition( CegConjecturePbe * pbe, std::vector< unsigned >& pos );
    // is return value modified 
    bool isReturnValueModified();
    class UEnumInfo {
    public:
      UEnumInfo() : d_status(-1){}
      int d_status;
      // enum val -> polarity -> solved
      std::map< Node, std::map< unsigned, Node > > d_look_ahead_sols;
    };
    // enumerator -> info
    std::map< Node, UEnumInfo > d_uinfo;
    void initialize( CegConjecturePbe * pbe, Node c );
    void getCurrentStrings( CegConjecturePbe * pbe, std::vector< Node >& vals, std::vector< CVC4::String >& ex_vals );
    bool getStringIncrement( CegConjecturePbe * pbe, bool isPrefix, std::vector< CVC4::String >& ex_vals, 
                             std::vector< Node >& vals, std::vector< unsigned >& inc, unsigned& tot );
    bool isStringSolved( CegConjecturePbe * pbe, std::vector< CVC4::String >& ex_vals, std::vector< Node >& vals );
  };
  /** construct solution */
  Node constructSolution( Node c );
  Node constructSolution( Node c, Node e, UnifContext& x, int ind );
  Node constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  Node constructBestStringSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  Node constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x );
  Node constructBestConditional( std::vector< Node >& conds, UnifContext& x );
  Node constructBestStringToConcat( std::vector< Node > strs,
                                    std::map< Node, unsigned > total_inc, 
                                    std::map< Node, std::vector< unsigned > > incr,
                                    UnifContext& x );
  void getStringIncrement( bool isPrefix, Node c, Node v,                                     
                           std::map< Node, unsigned > total_inc, 
                           std::map< Node, std::vector< unsigned > > incr );
public:
  void registerCandidates( std::vector< Node >& candidates ); 
  void getCandidateList( std::vector< Node >& candidates, std::vector< Node >& clist );
  // lems and candidate values are outputs  
  bool constructCandidates( std::vector< Node >& enums, std::vector< Node >& enum_values, 
                            std::vector< Node >& candidates, std::vector< Node >& candidate_values, 
                            std::vector< Node >& lems );
};


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
