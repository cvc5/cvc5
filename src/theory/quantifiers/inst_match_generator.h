/*********************                                                        */
/*! \file inst_match_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inst match generator class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H
#define __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H

#include "theory/quantifiers/inst_match.h"
#include <map>

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
namespace quantifiers{
  class TermArgTrie;
}

namespace inst {

class Trigger;

/** IMGenerator class
* Virtual base class for generating InstMatch objects, which correspond to quantifier instantiations.
*
* Some functions below take as argument a pointer to the current quantifiers engine, 
* which is used for making various queries about what terms and equalities exist in the current context.
*
* Some functions below take a point to a parent Trigger object, which is used to post-process and finalize
* the instantiations we make with calls to qe->addInstantiation(...).
*/
class IMGenerator {
public:
  virtual ~IMGenerator() {}
  /** Reset instantiation round. 
  *
  * Called once at beginning of an instantiation round. 
  */
  virtual void resetInstantiationRound( QuantifiersEngine* qe ) = 0;
  /** Reset.
  *
  * eqc is the equivalence class to search in (any if eqc=null).
  *
  * Returns true if it is possible that this generator can produce instantiations.
  */
  virtual bool reset( Node eqc, QuantifiersEngine* qe ) = 0;
  /** Get the next match.
  *
  * Must call reset( eqc ) before this function. 
  *
  * q is the quantified formula we are adding instantiations for
  * m is the InstMatch object we are generating
  *
  * Returns a positive value if we successfully generate a match m.
  */
  virtual int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) = 0;
  /** add instantiations
  *
  * This add all available instantiations for q based on the current context. It typically is
  * implemented as a fixed point of getNextMatch above.
  *
  * baseMatch is a mapping of default values that should be used for variables that are not bound by this (not frequently used).
  */
  virtual int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ) = 0;
  /** active add flag
  *
  *  
  *
  */
  virtual void setActiveAdd( bool val ) {}
  /** get active score 
  *
  * A heuristic value indicating how active this generator is.
  */
  virtual int getActiveScore( QuantifiersEngine * qe ) { return 0; }
protected:
  /** send instantiation 
  *
  * This is called for each instantiation generator 
  */
  bool sendInstantiation( Trigger * tparent, InstMatch& m );
};/* class IMGenerator */

class CandidateGenerator;

/** InstMatchGenerator class
*
* This is the default generator class for non-simple single triggers, that is,
* triggers composed of a single term with nested term applications.
* For example, { f( y, f( x, a ) ) } and { f( g( x ), a ) } are non-simple triggers.
*
* Handling non-simple triggers is done by constructing a linked list of InstMatchGenerator classes
* (see mkInstMatchGenerator).
*
* For non-simple triggers, CVC4 employs techniques that ensure that the number of instantiations 
* is worst-case polynomial wrt the number of ground terms.
* Consider the axiom/pattern/context :
*
*          axiom : forall x1 x2 x3 x4. F[ x1...x4 ]
*
*        trigger : P( f( x1 ), f( x2 ), f( x3 ), f( x4 ) )
*
* ground context : ~P( a, a, a, a ), a = f( c_1 ) = ... = f( c_100 )
*
* If E-matching were applied exhaustively, then x1, x2, x3, x4 would be instantiated with all combinations of c_1, ... c_100, giving 100^4 instantiations.
*
* Instead, we enforce that at most 1 instantiation is produced for a ( pattern, ground term ) pair per round. Meaning, only one instantiation is generated
* when matching P( a, a, a, a ) and P( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ).
*
* A number of special cases of triggers are covered by this generator (see implementation of initialize), including :
*   Literal triggers, e.g. x >= a, ~x = y
*   Purified triggers, e.g. selector triggers head( x ), and simple invertible triggers e.g. x+1
*   Variable triggers, e.g. x
*
* All triggers above can be in the context of an equality, e.g.
* { f( y, f( x, a ) ) = b } is a trigger that matches f( y, f( x, a ) ) to ground terms in the equivalence class of b.
* { ~f( y, f( x, a ) ) = b } is a trigger that matches f( y, f( x, a ) ) to any ground terms not in the equivalence class of b.
*/
class InstMatchGenerator : public IMGenerator {
protected:
  bool d_needsReset;
  /** candidate generator */
  CandidateGenerator* d_cg;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  std::vector< int > d_children_index;
  /** the next generator in order */
  InstMatchGenerator* d_next;
  /** eq class */
  Node d_eq_class;
  Node d_eq_class_rel;
  /** variable numbers */
  std::map< int, int > d_var_num;
  /** excluded matches */
  std::map< Node, bool > d_curr_exclude_match;
  /** first candidate */
  Node d_curr_first_candidate;
  /** indepdendent generate (failures should be cached) */
  bool d_independent_gen;
  /** initialize pattern */
  void initialize( Node q, QuantifiersEngine* qe, std::vector< InstMatchGenerator * > & gens, 
                   Trigger * tparent );
  /** children types 0 : variable, 1 : child term, -1 : ground term */
  std::vector< int > d_children_types;
  /** continue */
  int continueNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
public:
  enum {
    //options for producing matches
    MATCH_GEN_DEFAULT = 0,
    //others (internally used)
    MATCH_GEN_INTERNAL_ERROR,
  };
  /** get the match against ground term or formula t.
      d_match_pattern and t should have the same shape.
      only valid for use where !d_match_pattern.isNull().
  */
  int getMatch( Node q, Node t, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );

  /** constructors */
  InstMatchGenerator( Node pat );
  InstMatchGenerator();
  /** destructor */
  virtual ~InstMatchGenerator() throw();
  /** The pattern we are producing matches for.
      If null, this is a multi trigger that is merging matches from d_children.
  */
  Node d_pattern;
  /** match pattern */
  Node d_match_pattern;
  /** match pattern type */
  TypeNode d_match_pattern_type;
  /** match pattern op */
  Node d_match_pattern_op;
  /** what matched */
  Node d_curr_matched;
public:
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );

  bool d_active_add;
  void setActiveAdd( bool val );
  int getActiveScore( QuantifiersEngine * qe );
  void excludeMatch( Node n ) { d_curr_exclude_match[n] = true; }
  void setIndependent() { d_independent_gen = true; }

  static InstMatchGenerator* mkInstMatchGenerator( Node q, Node pat, QuantifiersEngine* qe, Trigger * tparent );
  static InstMatchGenerator* mkInstMatchGeneratorMulti( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, 
                                                        Trigger * tparent );
  static InstMatchGenerator* mkInstMatchGenerator( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, 
                                                   std::map< Node, InstMatchGenerator * >& pat_map_init, 
                                                   Trigger * tparent );
};/* class InstMatchGenerator */

//match generator for boolean term ITEs
class VarMatchGeneratorBooleanTerm : public InstMatchGenerator {
public:
  VarMatchGeneratorBooleanTerm( Node var, Node comp );
  virtual ~VarMatchGeneratorBooleanTerm() throw() {}
  Node d_comp;
  bool d_rm_prev;
  /** reset instantiation round (call this at beginning of instantiation round) */
  void resetInstantiationRound( QuantifiersEngine* qe ){}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ){ 
    d_eq_class = eqc; 
    return true;
  }
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations directly */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ){ return 0; }
};

//match generator for purified terms (matched term is substituted into d_subs)
class VarMatchGeneratorTermSubs : public InstMatchGenerator {
public:
  VarMatchGeneratorTermSubs( Node var, Node subs );
  virtual ~VarMatchGeneratorTermSubs() throw() {}
  TNode d_var;
  TypeNode d_var_type;
  Node d_subs;
  bool d_rm_prev;
  /** reset instantiation round (call this at beginning of instantiation round) */
  void resetInstantiationRound( QuantifiersEngine* qe ){}
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ){ 
    d_eq_class = eqc; 
    return true;
  }
  /** get the next match.  must call reset( eqc ) before this function. */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
  /** add instantiations directly */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent ) { return 0; }
};


/** InstMatchGeneratorMultiLinear class 
*
* This is the default implementation of multi-triggers.
*
* CVC4 employs techniques that ensure that the number of instantiations 
* is worst-case polynomial wrt the number of ground terms, where this class lifts this policy
* to multi-triggers. In particular consider
*
*  multi-trigger : { f( x1 ), f( x2 ), f( x3 ), f( x4 ) }
*
* For this multi-trigger, we insist that for each i=1...4, and each ground term t, there is at most 1 instantiation added as a result of matching 
* ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ) against ground terms of the form ( s_1, s_2, s_3, s_4 ) where t = s_i.
* Meaning I could add instantiations for the multi-trigger ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ) based on matching pairwise against:
* ( f( c_i11 ), f( c_i21 ), f( c_i31 ), f( c_i41 ) )
* ( f( c_i12 ), f( c_i22 ), f( c_i32 ), f( c_i42 ) )
* ( f( c_i13 ), f( c_i23 ), f( c_i33 ), f( c_i43 ) )
* Where we require c_i{jk} != c_i{jl} for each i=1...4, k != l.
*
* In other words, we disallow adding an instantiation based on matching against both
* ( f( c_1 ), f( c_2 ), f( c_4 ), f( c_6 ) ) and
* ( f( c_1 ), f( c_3 ), f( c_5 ), f( c_7 ) )
* against ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ), since f( c_1 ) is matched against f( x1 ) twice.
*
*/
class InstMatchGeneratorMultiLinear : public InstMatchGenerator {
private:
  int resetChildren( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMultiLinear( Node q, std::vector< Node >& pats, QuantifiersEngine* qe );
  /** destructor */
  virtual ~InstMatchGeneratorMultiLinear() throw();
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function.*/
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent );
};/* class InstMatchGeneratorMulti */


/** InstMatchGeneratorMulti
*
* This is an earlier implementation of multi-triggers.
* This generator takes the product of instantiations found by single trigger matching, and does 
* not have the guarantee that the number of instantiations is polynomial wrt the number of ground terms.
*/
class InstMatchGeneratorMulti : public IMGenerator {
private:
  /** indexed trie */
  typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
  /** process new match */
  void processNewMatch( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int fromChildIndex, int& addedLemmas );
  /** process new instantiations */
  void processNewInstantiations( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int& addedLemmas, InstMatchTrie* tr,
                                 std::vector< IndexedTrie >& unique_var_tries,
                                 int trieIndex, int childIndex, int endChildIndex, bool modEq );
  /** process new instantiations 2 */
  void processNewInstantiations2( QuantifiersEngine* qe, Trigger * tparent, InstMatch& m, int& addedLemmas,
                                  std::vector< IndexedTrie >& unique_var_tries,
                                  int uvtIndex, InstMatchTrie* tr = NULL, int trieIndex = 0 );
private:
  /** var contains (variable indices) for each pattern node */
  std::map< Node, std::vector< int > > d_var_contains;
  /** variable indices contained to pattern nodes */
  std::map< int, std::vector< Node > > d_var_to_node;
  /** quantifier to use */
  Node d_f;
  /** policy to use for matching */
  int d_matchPolicy;
  /** children generators */
  std::vector< InstMatchGenerator* > d_children;
  /** order */
  std::map< unsigned, InstMatchTrie::ImtIndexOrder* > d_imtio;
  /** inst match tries for each child */
  std::vector< InstMatchTrieOrdered > d_children_trie;
  /** calculate matches */
  void calculateMatches( QuantifiersEngine* qe );
public:
  /** constructors */
  InstMatchGeneratorMulti( Node q, std::vector< Node >& pats, QuantifiersEngine* qe, Trigger * tparent );
  /** destructor */
  virtual ~InstMatchGeneratorMulti() throw();
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe );
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) { return -1; }
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );
};/* class InstMatchGeneratorMulti */

/** InstMatchGeneratorSimple class
*
* This is the default generator class for simple single triggers.
* For example, { f( x, a ) }, { f( x, x ) } and { f( x, y ) } are simple triggers.
*
* Notice that simple triggers also can have an attached polarity.
* For example, { f( x, y ) = a } and { ~f( a, x ) = b } are simple triggers.
*
* The implementation traverses the term indices in TermDatabase for adding instantiations,
* which is more efficient than the techniques required for handling non-simple triggers.
*
* In contrast to other instantiation generators, it does not call sendInstantiation and instead
* calls qe->addInstantiation(...) directly. This is done for performance reasons.
*/
class InstMatchGeneratorSimple : public IMGenerator {
private:
  /** quantifier for match term */
  Node d_f;
  /** match term */
  Node d_match_pattern;
  /** equivalence class */
  bool d_pol;
  Node d_eqc;
  /** match pattern arg types */
  std::vector< TypeNode > d_match_pattern_arg_types;
  /** operator */
  Node d_op;
  /** to indicies */
  std::map< int, int > d_var_num;
  /** add instantiations */
  void addInstantiations( InstMatch& m, QuantifiersEngine* qe, 
                          int& addedLemmas, int argIndex, quantifiers::TermArgTrie* tat );
public:
  /** constructors */
  InstMatchGeneratorSimple( Node q, Node pat, QuantifiersEngine* qe );
  /** destructor */
  ~InstMatchGeneratorSimple() throw() {}
  /** reset instantiation round (call this whenever equivalence classes have changed) */
  void resetInstantiationRound( QuantifiersEngine* qe );
  /** reset, eqc is the equivalence class to search in (any if eqc=null) */
  bool reset( Node eqc, QuantifiersEngine* qe ) { return true; }
  /** get the next match.  must call reset( eqc ) before this function. (not implemented) */
  int getNextMatch( Node q, InstMatch& m, QuantifiersEngine* qe, Trigger * tparent ) { return -1; }
  /** add instantiations */
  int addInstantiations( Node q, InstMatch& baseMatch, QuantifiersEngine* qe, Trigger * tparent );
  /** get active score */
  int getActiveScore( QuantifiersEngine * qe );
};/* class InstMatchGeneratorSimple */

}
}
}

#endif
