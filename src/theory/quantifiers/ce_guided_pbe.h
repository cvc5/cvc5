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

/** CegConjecturePbe
*
* This class implements optimizations that target synthesis conjectures
* that are in Programming-By-Examples (PBE) form.
*
* [EX#1] An example of a synthesis conjecture in PBE form is :
* exists f. forall x.
* ( x = 0 => f( x ) = 2 ) ^ ( x = 5 => f( x ) = 7 ) ^ ( x = 6 => f( x ) = 8 )
*
* We say that the above conjecture has I/O examples (0)->2, (5)->7, (6)->8.
*
* Internally, this class does the following for SyGuS inputs:
*
* (1) Infers whether the input conjecture is in PBE form or not.
* (2) Based on this information and on the syntactic restrictions, it
*     devises a strategy for enumerating terms and construction solutions,
*     which is inspired by Alur et al. "Scaling Enumerative Program Synthesis
*     via Divide and Conquer" TACAS 2017. In particular, it may consider
*     strategies for constructing decision trees when the grammar permits ITEs
*     and a strategy for divide-and-conquer string synthesis when the grammar
*     permits string concatenation. This is stored in a set of data structures
*     within d_cinfo.
* (3) It makes (possibly multiple) calls to
*     TermDatabaseSygus::registerMeasuredTerm(...) based
*     on the strategy, which inform the rest of the system to enumerate values
*     of particular types in the grammar through use of fresh variables which
*     we call "enumerators".
*
* Points (1)-(3) happen within a call to CegConjecturePbe::initialize(...).
*
* Notice that each enumerator is associated with a single
* function-to-synthesize,
* but a function-to-sythesize may be mapped to multiple enumerators.
* Some public functions of this class expect an enumerator as input, which we
* map to a function-to-synthesize via TermDatabaseSygus::getSynthFunFor(e).
*
* An enumerator is initially "active" but may become inactive if the enumeration
* exhausts all possible values in the datatype corresponding to syntactic
* restrictions
* for it. The search may continue unless all enumerators become inactive.
*
* (4) During search, the extension of quantifier-free datatypes procedure for
*     SyGuS datatypes may ask this class whether current candidates can be
*     discarded based on
*     inferring when two candidate solutions are equivalent up to examples.
*     For example, the candidate solutions:
*     f = \x ite( x<0, x+1, x ) and f = \x x
*     are equivalent up to examples on the above conjecture, since they have the
*     same value on the points x = 0,5,6. Hence, we need only consider one of
*     them. The interface for querying this is
* CegConjecturePbe::addSearchVal(...).
*     For details, see Reynolds et al. SYNT 2017.
*
* (5) When the extension of quantifier-free datatypes procedure for SyGuS
*     datatypes terminates with a model, the parent of this class calls
*     CegConjecturePbe::getCandidateList(...), where this class returns the list
*     of active enumerators.
* (6) The parent class subsequently calls
*     CegConjecturePbe::constructValues(...), which
*     informs this class that new values have been enumerated for active
*     enumerators, as indicated by the current model. This call also requests
*     that based on these
*     newly enumerated values, whether this class is now able to construct a
*     solution based on the high-level strategy (stored in d_c_info).
*
* This class is not designed to work in incremental mode, since there is no way
* to
* specify incremental problems in SyguS.
*
*/
class CegConjecturePbe {
 public:
  CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p);
  ~CegConjecturePbe();

  /** initialize this class
  *
  * n is the "base instantiation" of the deep-embedding version of
  *   the synthesis conjecture under "candidates".
  *   (see CegConjecture::d_base_inst)
  *
  * This function may add lemmas to the vector lemmas corresponding
  * to initial lemmas regarding static analysis of enumerators it
  * introduced. For example, we may say that the top-level symbol
  * of an enumerator is not ITE if it is being used to construct
  * return values for decision trees.
  */
  void initialize(Node n,
                  std::vector<Node>& candidates,
                  std::vector<Node>& lemmas);
  /** get candidate list
  * Adds all active enumerators associated with functions-to-synthesize in
  * candidates to clist.
  */
  void getCandidateList(std::vector<Node>& candidates,
                        std::vector<Node>& clist);
  /** construct candidates
  * (1) Indicates that the list of enumerators in "enums" currently have model
  *     values "enum_values".
  * (2) Asks whether based on these new enumerated values, we can construct a
  *     solution for
  *     the functions-to-synthesize in "candidates". If so, this function
  *     returns "true" and
  *     adds solutions for candidates into "candidate_values".
  * During this class, this class may add auxiliary lemmas to "lems", which the
  * caller should send on the output channel via lemma(...).
  */
  bool constructCandidates(std::vector<Node>& enums,
                           std::vector<Node>& enum_values,
                           std::vector<Node>& candidates,
                           std::vector<Node>& candidate_values,
                           std::vector<Node>& lems);
  /** is PBE enabled for any enumerator? */
  bool isPbe() { return d_is_pbe; }
  /** is the enumerator e associated with I/O example pairs? */
  bool hasExamples(Node e);
  /** get number of I/O example pairs for enumerator e */
  unsigned getNumExamples(Node e);
  /** get the input arguments for i^th I/O example for e, which is added to the
   * vector ex */
  void getExample(Node e, unsigned i, std::vector<Node>& ex);
  /** get the output value of the i^th I/O example for enumerator e */
  Node getExampleOut(Node e, unsigned i);

  /** add the search val
  * This function is called by the extension of quantifier-free datatypes
  * procedure for SyGuS datatypes when we are considering a value of
  * enumerator e of sygus type tn whose analog in the signature of builtin
  * theory is bvr.
  *
  * For example, bvr = x + 1 when e is the datatype value Plus( x(), One() ) and
  * tn is a sygus datatype that encodes a subsignature of the integers.
  *
  * This returns either:
  * - A SyGuS term whose analog is equivalent to bvr up to examples, in the
  *   above example,
  *   it may return a term t of the form Plus( One(), x() ), such that this
  *   function was previously called with t as input.
  * - e, indicating that no previous terms are equivalent to e up to examples.
  */
  Node addSearchVal(TypeNode tn, Node e, Node bvr);
  /** evaluate builtin
  * This returns the evaluation of bn on the i^th example for the
  * function-to-synthesis
  * associated with enumerator e. If there are not at least i examples, it
  * returns the rewritten form of bn.
  * For example, if bn = x+5, e is an enumerator for f in the above example
  * [EX#1], then
  *   evaluateBuiltin( tn, bn, e, 0 ) = 7
  *   evaluateBuiltin( tn, bn, e, 1 ) = 9
  *   evaluateBuiltin( tn, bn, e, 2 ) = 10
  */
  Node evaluateBuiltin(TypeNode tn, Node bn, Node e, unsigned i);

 private:
  /** quantifiers engine associated with this class */
  QuantifiersEngine* d_qe;
  /** sygus term database of d_qe */
  quantifiers::TermDbSygus * d_tds;
  /** true and false nodes */
  Node d_true;
  Node d_false;
  /** parent conjecture
  * This is the data structure that contains global information about the
  * conjecture.
  */
  CegConjecture* d_parent;
  /** is this a PBE conjecture for any function? */
  bool d_is_pbe;
  /** for each candidate variable f (a function-to-synthesize), whether the
  * conjecture is purely PBE for that variable
  * In other words, all occurrences of f are guarded by equalities that
  * constraint its arguments to constants.
  */
  std::map< Node, bool > d_examples_invalid;
  /** for each candidate variable (function-to-synthesize), whether the
  * conjecture is purely PBE for that variable.
  * An example of a conjecture for which d_examples_invalid is false but
  * d_examples_out_invalid is true is:
  *   exists f. forall x. ( x = 0 => f( x ) > 2 )
  * another example is:
  *   exists f. forall x. ( ( x = 0 => f( x ) = 2 ) V ( x = 3 => f( x ) = 3 ) )
  * since the formula is not a conjunction (the example values are not
  * entailed).
  * However, the domain of f in both cases is finite, which can be used for
  * search space pruning.
  */
  std::map< Node, bool > d_examples_out_invalid;
  /** for each candidate variable (function-to-synthesize), input of I/O
   * examples */
  std::map< Node, std::vector< std::vector< Node > > > d_examples;
  /** for each candidate variable (function-to-synthesize), output of I/O
   * examples */
  std::map< Node, std::vector< Node > > d_examples_out;
  /** the list of example terms
   * For the example [EX#1] above, this is f( 0 ), f( 5 ), f( 6 )
   */
  std::map< Node, std::vector< Node > > d_examples_term;
  /** collect the PBE examples in n
  * This is called on the input conjecture, and will populate the above vectors.
  *   hasPol/pol denote the polarity of n in the conjecture.
  */
  void collectExamples( Node n, std::map< Node, bool >& visited, bool hasPol, bool pol );

  //--------------------------------- PBE search values
  /** this class is an index of candidate solutions for PBE synthesis */
  class PbeTrie {
   public:
    PbeTrie() {}
    ~PbeTrie() {}
    Node d_lazy_child;
    std::map<Node, PbeTrie> d_children;
    void clear() { d_children.clear(); }
    Node addPbeExample(TypeNode etn, Node e, Node b, CegConjecturePbe* cpbe,
                       unsigned index, unsigned ntotal);

   private:
    Node addPbeExampleEval(TypeNode etn, Node e, Node b, std::vector<Node>& ex,
                           CegConjecturePbe* cpbe, unsigned index,
                           unsigned ntotal);
  };
  /** trie of candidate solutions tried
  * This stores information for each (enumerator, type),
  * where type is a type in the grammar of the space of solutions for a subterm
  * of e. This is used for symmetry breaking in quantifier-free reasoning
  * about SyGuS datatypes.
  */
  std::map<Node, std::map<TypeNode, PbeTrie> > d_pbe_trie;
  //--------------------------------- end PBE search values

  // -------------------------------- decision tree learning
  // index filter
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
  // subsumption trie
  class SubsumeTrie {
  public:
    SubsumeTrie(){}
    // adds term to the trie, removes based on subsumption
    Node addTerm( CegConjecturePbe * pbe, Node t, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // adds condition to the trie (does not do subsumption)
    Node addCond( CegConjecturePbe * pbe, Node c, std::vector< Node >& vals, bool pol, IndexFilter * f = NULL );
    // returns the set of terms that are subsets of vals
    void getSubsumed( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed, IndexFilter * f = NULL );
    // returns the set of terms that are supersets of vals
    void getSubsumedBy( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::vector< Node >& subsumed_by, IndexFilter * f = NULL );
    // v[-1,1,0] -> children always false, always true, both
    void getLeaves( CegConjecturePbe * pbe, std::vector< Node >& vals, bool pol, std::map< int, std::vector< Node > >& v, IndexFilter * f = NULL );
    /** is this trie empty? */
    bool isEmpty() { return d_term.isNull() && d_children.empty(); }
    /** clear this trie */
    void clear() {
      d_term = Node::null();
      d_children.clear(); 
    }

   private:
    /** the term at this node */
    Node d_term;
    /** the children nodes of this trie */
    std::map<Node, SubsumeTrie> d_children;
    /** helper function for above functions */
    Node addTermInternal(CegConjecturePbe* pbe,
                         Node t,
                         std::vector<Node>& vals,
                         bool pol,
                         std::vector<Node>& subsumed,
                         bool spol,
                         IndexFilter* f,
                         unsigned index,
                         int status,
                         bool checkExistsOnly,
                         bool checkSubsume);
    /** helper function for above functions */
    void getLeavesInternal(CegConjecturePbe* pbe,
                           std::vector<Node>& vals,
                           bool pol,
                           std::map<int, std::vector<Node> >& v,
                           IndexFilter* f,
                           unsigned index,
                           int status);
  };
  // -------------------------------- end decision tree learning

  //------------------------------ representation of a enumeration strategy

  /** roles for enumerators */
  enum {
    enum_io,
    enum_ite_condition,
    enum_concat_term,
    enum_any,
  };
  /** print the role with Trace c. */
  static void print_role(const char* c, unsigned r);
  /** strategies for SyGuS datatype types */
  enum
  {
    strat_ITE,
    strat_CONCAT,
    strat_ID,
  };
  /** print the strategy with Trace c. */
  static void print_strat(const char* c, unsigned s);

  /** information about an enumerator */
  class EnumInfo {
  public:
    EnumInfo() : d_role( enum_io ){}
    /** initialize this class
    * c is the parent function-to-synthesize
    * role is the "role" the enumerator plays in the high-level strategy,
    *   which is one of enum_* above.
    */
    void initialize(Node c, unsigned role)
    {
      d_parent_candidate = c;
      d_role = role;
    }
    bool isTemplated() { return !d_template.isNull(); }
    void addEnumValue(CegConjecturePbe* pbe,
                      Node v,
                      std::vector<Node>& results);
    void setSolved(Node slv);
    bool isSolved() { return !d_enum_solved.isNull(); }
    Node getSolved() { return d_enum_solved; }
    unsigned getRole() { return d_role; }
    Node d_parent_candidate;
    // for template
    Node d_template;
    Node d_template_arg;
    
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

   private:
    /** whether an enumerated value for this conjecture has solved the entire
     * conjecture */
    Node d_enum_solved;
    /** the role of this enumerator (one of enum_* above). */
    unsigned d_role;
  };
  /** maps enumerators to the information above */
  std::map< Node, EnumInfo > d_einfo;

  class CandidateInfo;
  /** represents a strategy for a SyGuS datatype type */
  class EnumTypeInfoStrat {
  public:
    unsigned d_this;
    /** conditional solutions */
    std::vector< TypeNode > d_csol_cts;
    std::vector< Node > d_cenum;
  };

  /** stores enumerators and strategies for a SyGuS datatype type */
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

  /** stores strategy and enumeration information for a function-to-synthesize
   */
  class CandidateInfo {
  public:
    CandidateInfo() : d_check_sol( false ), d_cond_count( 0 ){}
    Node d_this_candidate;
    /** root SyGuS datatype for the function-to-synthesize,
    * which encodes the overall syntactic restrictions on the space
    * of solutions.
    */
    TypeNode d_root;
    /** Information for each SyGuS datatype type occurring in a field of d_root
     */
    std::map< TypeNode, EnumTypeInfo > d_tinfo;
    /** list of all enumerators for the function-to-synthesize */
    std::vector< Node > d_esym_list;
    /** maps sygus datatypes to their enumerator */
    std::map< TypeNode, Node > d_search_enum;
    bool d_check_sol;
    unsigned d_cond_count;
    Node d_solution;
    void initialize( Node c );
    void initializeType( TypeNode tn );
    Node getRootEnumerator();
    bool isNonTrivial();
  };
  /** maps a function-to-synthesize to the above information */
  std::map< Node, CandidateInfo > d_cinfo;

  //------------------------------ representation of an enumeration strategy
  /** add enumerated value */
  void addEnumeratedValue( Node x, Node v, std::vector< Node >& lems );
  bool getExplanationForEnumeratorExclude( Node c, Node x, Node v, std::vector< Node >& results, EnumInfo& ei, std::vector< Node >& exp );

  //------------------------------ strategy registration
  void collectEnumeratorTypes(Node c, TypeNode tn, unsigned enum_role);
  void registerEnumerator(
      Node et, Node c, TypeNode tn, unsigned enum_role, bool inSearch);
  void staticLearnRedundantOps(Node c, std::vector<Node>& lemmas);
  void staticLearnRedundantOps(Node c,
                               Node e,
                               std::map<Node, bool>& visited,
                               std::vector<Node>& redundant,
                               std::vector<Node>& lemmas,
                               int ind);

  /** register candidate conditional */
  bool inferTemplate(unsigned k,
                     Node n,
                     std::map<Node, unsigned>& templ_var_index,
                     std::map<unsigned, unsigned>& templ_injection);
  //------------------------------ end strategy registration

  //------------------------------ constructing solutions
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
  /** helper function for construct solution.
  * Construct a solution based on enumerator e for function-to-synthesize c,
  * in context x, where ind is the term depth of the context.
  */
  Node constructSolution( Node c, Node e, UnifContext& x, int ind );
  /** Heuristically choose the best solved term from solved in context x,
   * currently return the first. */
  Node constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  /** Heuristically choose the best solved string term  from solved in context
   * x, currently  return the first. */
  Node constructBestStringSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  /** heuristically choose the best solved conditional term  from solved in
   * context x, currently random */
  Node constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x );
  /** heuristically choose the best conditional term  from conds in context x,
   * currently random */
  Node constructBestConditional( std::vector< Node >& conds, UnifContext& x );
  /** heuristically choose the best string to concatenate from strs to the
  * solution in context x, currently random
  * incr stores the vector of indices that are incremented by this solution in
  * example outputs.
  * total_inc[x] is the sum of incr[x] for each x in strs.
  */
  Node constructBestStringToConcat( std::vector< Node > strs,
                                    std::map< Node, unsigned > total_inc, 
                                    std::map< Node, std::vector< unsigned > > incr,
                                    UnifContext& x );
  //------------------------------ end constructing solutions

  /** get guard status
  * Returns 1 if g is asserted true in the SAT solver.
  * Returns -1 if g is asserted false in the SAT solver.
  * Returns 0 otherwise.
  */
  int getGuardStatus(Node g);
};


}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
