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
#include "theory/quantifiers/sygus/sygus_module.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** roles for enumerators
 *
 * This indicates the role of an enumerator that is allocated by approaches
 * for synthesis-by-unification (see details below).
 *   io : the enumerator should enumerate values that are overall solutions
 *        for the function-to-synthesize,
 *   ite_condition : the enumerator should enumerate values that are useful
 *                   in ite conditions in the ITE strategy,
 *   concat_term : the enumerator should enumerate values that are used as
 *                 components of string concatenation solutions.
 */
enum EnumRole
{
  enum_invalid,
  enum_io,
  enum_ite_condition,
  enum_concat_term,
};
std::ostream& operator<<(std::ostream& os, EnumRole r);

/** roles for strategy nodes
 *
 * This indicates the role of a strategy node, which is a subprocedure of
 * CegConjecturePbe::constructSolution (see details below).
 *   equal : the node constructed must be equal to the overall solution for
 *           the function-to-synthesize,
 *   string_prefix/suffix : the node constructed must be a prefix/suffix
 *                          of the function-to-synthesize,
 *   ite_condition : the node constructed must be a condition that makes some
 *                   active input examples true and some input examples false.
 */
enum NodeRole
{
  role_invalid,
  role_equal,
  role_string_prefix,
  role_string_suffix,
  role_ite_condition,
};
std::ostream& operator<<(std::ostream& os, NodeRole r);

/** enumerator role for node role */
EnumRole getEnumeratorRoleForNodeRole(NodeRole r);

/** strategy types
 *
 * This indicates a strategy for synthesis-by-unification (see details below).
 *   ITE : strategy for constructing if-then-else solutions via decision
 *         tree learning techniques,
 *   CONCAT_PREFIX/SUFFIX : strategy for constructing string concatenation
 *         solutions via a divide and conquer approach,
 *   ID : identity strategy used for calling strategies on child type through
 *        an identity function.
 */
enum StrategyType
{
  strat_INVALID,
  strat_ITE,
  strat_CONCAT_PREFIX,
  strat_CONCAT_SUFFIX,
  strat_ID,
};
std::ostream& operator<<(std::ostream& os, StrategyType st);

class CegConjecture;

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
* function-to-synthesize, but a function-to-sythesize may be mapped to multiple 
* enumerators. Some public functions of this class expect an enumerator as 
* input, which we map to a function-to-synthesize via 
* TermDatabaseSygus::getSynthFunFor(e).
*
* An enumerator is initially "active" but may become inactive if the enumeration
* exhausts all possible values in the datatype corresponding to syntactic
* restrictions for it. The search may continue unless all enumerators become 
* inactive.
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
*       CegConjecturePbe::addSearchVal(...).
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
* to specify incremental problems in SyguS.
*/
class CegConjecturePbe : public SygusModule
{
 public:
  CegConjecturePbe(QuantifiersEngine* qe, CegConjecture* p);
  ~CegConjecturePbe();

  /** initialize this class
  *
  * This function may add lemmas to the vector lemmas corresponding
  * to initial lemmas regarding static analysis of enumerators it
  * introduced. For example, we may say that the top-level symbol
  * of an enumerator is not ITE if it is being used to construct
  * return values for decision trees.
  */
  bool initialize(Node n,
                  const std::vector<Node>& candidates,
                  std::vector<Node>& lemmas) override;
  /** get term list
   *
  * Adds all active enumerators associated with functions-to-synthesize in
  * candidates to terms.
  */
  void getTermList(const std::vector<Node>& candidates,
                   std::vector<Node>& terms) override;
  /** construct candidates
   *
   * This function attempts to use unification-based approaches for constructing
   * solutions for all functions-to-synthesize (indicated by candidates). These
   * approaches include decision tree learning and a divide-and-conquer
   * algorithm based on string concatenation.
   *
   * Calls to this function are such that terms is the list of active
   * enumerators (returned by getTermList), and term_values are their current
   * model values. This function registers { terms -> terms_values } in
   * the database of values that have been enumerated, which are in turn used
   * for constructing candidate solutions when possible.
   *
   * This function also excludes models where (terms = terms_values) by adding
   * blocking clauses to lems. For example, for grammar:
   *   A -> A+A | x | 1 | 0
   * and a call where terms = { d } and term_values = { +( x, 1 ) }, it adds:
   *   ~G V ~is_+( d ) V ~is_x( d.1 ) V ~is_1( d.2 )
   * to lems, where G is active guard of the enumerator d (see
   * TermDatabaseSygus::getActiveGuardForEnumerator). This blocking clause
   * indicates that d should not be given the model value +( x, 1 ) anymore,
   * since { d -> +( x, 1 ) } has now been added to the database of this class.
   */
  bool constructCandidates(const std::vector<Node>& terms,
                           const std::vector<Node>& term_values,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& candidate_values,
                           std::vector<Node>& lems) override;
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
  * - A SyGuS term whose analog is equivalent to bvr up to examples
  *   In the above example,
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
  /** sygus term database of d_qe */
  quantifiers::TermDbSygus * d_tds;
  /** true and false nodes */
  Node d_true;
  Node d_false;
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

  /** information about an enumerator
   *
   * We say an enumerator is a master enumerator if it is the variable that
   * we use to enumerate values for its sort. Master enumerators may have
   * (possibly multiple) slave enumerators, stored in d_enum_slave,
   */
  class EnumInfo {
   public:
    EnumInfo() : d_role(enum_io), d_is_conditional(false) {}
    /** initialize this class
    * c is the parent function-to-synthesize
    * role is the "role" the enumerator plays in the high-level strategy,
    *   which is one of enum_* above.
    */
    void initialize(Node c, EnumRole role);
    /** is this enumerator associated with a template? */
    bool isTemplated() { return !d_template.isNull(); }
    /** set conditional
      *
      * This flag is set to true if this enumerator may not apply to all
      * input/output examples. For example, if this enumerator is used
      * as an output value beneath a conditional in an instance of strat_ITE,
      * then this enumerator is conditional.
      */
    void setConditional() { d_is_conditional = true; }
    /** is conditional */
    bool isConditional() { return d_is_conditional; }
    void addEnumValue(CegConjecturePbe* pbe,
                      Node v,
                      std::vector<Node>& results);
    void setSolved(Node slv);
    bool isSolved() { return !d_enum_solved.isNull(); }
    Node getSolved() { return d_enum_solved; }
    EnumRole getRole() { return d_role; }
    Node d_parent_candidate;
    // for template
    Node d_template;
    Node d_template_arg;

    Node d_active_guard;
    std::vector<Node> d_enum_slave;
    /** values we have enumerated */
    std::vector<Node> d_enum_vals;
    /**
      * This either stores the values of f( I ) for inputs
      * or the value of f( I ) = O if d_role==enum_io
      */
    std::vector<std::vector<Node> > d_enum_vals_res;
    std::vector<Node> d_enum_subsume;
    std::map<Node, unsigned> d_enum_val_to_index;
    SubsumeTrie d_term_trie;

   private:
    /**
     * Whether an enumerated value for this conjecture has solved the entire
     * conjecture.
     */
    Node d_enum_solved;
    /** the role of this enumerator (one of enum_* above). */
    EnumRole d_role;
    /** is this enumerator conditional */
    bool d_is_conditional;
  };
  /** maps enumerators to the information above */
  std::map< Node, EnumInfo > d_einfo;

  class CandidateInfo;

  /** represents a strategy for a SyGuS datatype type
   *
   * This represents a possible strategy to apply when processing a strategy
   * node in constructSolution. When applying the strategy represented by this
   * class, we may make recursive calls to the children of the strategy,
   * given in d_cenum. If all recursive calls to constructSolution are
   * successful, say:
   *   constructSolution( c, d_cenum[1], ... ) = t1,
   *    ...,
   *   constructSolution( c, d_cenum[n], ... ) = tn,
   * Then, the solution returned by this strategy is
   *   d_sol_templ * { d_sol_templ_args -> (t1,...,tn) }
   */
  class EnumTypeInfoStrat {
   public:
    /** the type of strategy this represents */
    StrategyType d_this;
    /** the sygus datatype constructor that induced this strategy
     *
     * For example, this may be a sygus datatype whose sygus operator is ITE,
     * if the strategy type above is strat_ITE.
     */
    Node d_cons;
    /** children of this strategy */
    std::vector<std::pair<Node, NodeRole> > d_cenum;
    /** the arguments for the (templated) solution */
    std::vector<Node> d_sol_templ_args;
    /** the template for the solution */
    Node d_sol_templ;
  };

  /** represents a node in the strategy graph
   *
   * It contains a list of possible strategies which are tried during calls
   * to constructSolution.
   */
  class StrategyNode
  {
   public:
    StrategyNode() {}
    ~StrategyNode();
    /** the set of strategies to try at this node in the strategy graph */
    std::vector<EnumTypeInfoStrat*> d_strats;
  };

  /** stores enumerators and strategies for a SyGuS datatype type */
  class EnumTypeInfo {
  public:
    EnumTypeInfo() : d_parent( NULL ){}
    /** the parent candidate info (see below) */
    CandidateInfo * d_parent;
    /** the type that this information is for */
    TypeNode d_this_type;
    /** map from enum roles to enumerators for this type */
    std::map<EnumRole, Node> d_enum;
    /** map from node roles to strategy nodes */
    std::map<NodeRole, StrategyNode> d_snodes;
  };

  /** stores strategy and enumeration information for a function-to-synthesize
   */
  class CandidateInfo {
  public:
    CandidateInfo() : d_check_sol( false ), d_cond_count( 0 ){}
    Node d_this_candidate;
    /**
     * The root sygus datatype for the function-to-synthesize,
     * which encodes the overall syntactic restrictions on the space
     * of solutions.
     */
    TypeNode d_root;
    /** Info for sygus datatype type occurring in a field of d_root */
    std::map< TypeNode, EnumTypeInfo > d_tinfo;
    /** list of all enumerators for the function-to-synthesize */
    std::vector< Node > d_esym_list;
    /**
     * Maps sygus datatypes to their search enumerator. This is the (single)
     * enumerator of that type that we enumerate values for.
     */
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
  /** add enumerated value
   *
   * We have enumerated the value v for x. This function adds x->v to the
   * relevant data structures that are used for strategy-specific construction
   * of solutions when necessary, and returns a set of lemmas, which are added
   * to the input argument lems. These lemmas are used to rule out models where
   * x = v, to force that a new value is enumerated for x.
   */
  void addEnumeratedValue( Node x, Node v, std::vector< Node >& lems );
  /** domain-specific enumerator exclusion techniques
   *
   * Returns true if the value v for x can be excluded based on a
   * domain-specific exclusion technique like the ones below.
   *
   * c : the candidate variable that x is enumerating for,
   * results : the values of v under the input examples of c,
   * ei : the enumerator information for x,
   * exp : if this function returns true, then exp contains a (possibly
   * generalize) explanation for why v can be excluded.
   */
  bool getExplanationForEnumeratorExclude( Node c, Node x, Node v, std::vector< Node >& results, EnumInfo& ei, std::vector< Node >& exp );
  /** returns true if we can exlude values of x based on negative str.contains
   *
   * Values v for x may be excluded if we realize that the value of v under the
   * substitution for some input example will never be contained in some output
   * example. For details on this technique, see NegContainsSygusInvarianceTest
   * in sygus_invariance.h.
   *
   * This function depends on whether x is being used to enumerate values
   * for any node that is conditional in the strategy graph. For example,
   * nodes that are children of ITE strategy nodes are conditional. If any node
   * is conditional, then this function returns false.
   */
  bool useStrContainsEnumeratorExclude(Node x, EnumInfo& ei);
  /** cache for the above function */
  std::map<Node, bool> d_use_str_contains_eexc;

  //------------------------------ strategy registration
  /** collect enumerator types
   *
   * This builds the strategy for enumerated values of type tn for the given
   * role of nrole, for solutions to function-to-synthesize c.
   */
  void collectEnumeratorTypes(Node c, TypeNode tn, NodeRole nrole);
  /** register enumerator
   *
   * This registers that et is an enumerator for function-to-synthesize c
   * of type tn, having enumerator role enum_role.
   *
   * inSearch is whether we will enumerate values based on this enumerator.
   * A strategy node is represented by a (enumerator, node role) pair. Hence,
   * we may use enumerators for which this flag is false to represent strategy
   * nodes that have child strategies.
   */
  void registerEnumerator(
      Node et, Node c, TypeNode tn, EnumRole enum_role, bool inSearch);
  /** infer template */
  bool inferTemplate(unsigned k,
                     Node n,
                     std::map<Node, unsigned>& templ_var_index,
                     std::map<unsigned, unsigned>& templ_injection);
  /** static learn redundant operators
   *
   * This learns static lemmas for pruning enumerative space based on the
   * strategy for the function-to-synthesize c, and stores these into lemmas.
   */
  void staticLearnRedundantOps(Node c, std::vector<Node>& lemmas);
  /** helper for static learn redundant operators
   *
   * (e, nrole) specify the strategy node in the graph we are currently
   * analyzing, visited stores the nodes we have already visited.
   *
   * This method builds the mapping needs_cons, which maps (master) enumerators
   * to a map from the constructors that it needs.
   *
   * ind is the depth in the strategy graph we are at (for debugging).
   *
   * isCond is whether the current enumerator is conditional (beneath a
   * conditional of an strat_ITE strategy).
   */
  void staticLearnRedundantOps(
      Node c,
      Node e,
      NodeRole nrole,
      std::map<Node, std::map<NodeRole, bool> >& visited,
      std::map<Node, std::map<unsigned, bool> >& needs_cons,
      int ind,
      bool isCond);
  //------------------------------ end strategy registration

  //------------------------------ constructing solutions
  class UnifContext {
  public:
   UnifContext() : d_has_string_pos(role_invalid) {}
   /** this intiializes this context for function-to-synthesize c */
   void initialize(CegConjecturePbe* pbe, Node c);

   //----------for ITE strategy
   /** the value of the context conditional
    *
    * This stores a list of Boolean constants that is the same length of the
    * number of input/output example pairs we are considering. For each i,
    * if d_vals[i] = true, i/o pair #i is active according to this context
    * if d_vals[i] = false, i/o pair #i is inactive according to this context
    */
   std::vector<Node> d_vals;
   /** update the examples
    *
    * if pol=true, this method updates d_vals to d_vals & vals
    * if pol=false, this method updates d_vals to d_vals & ( ~vals )
    */
   bool updateContext(CegConjecturePbe* pbe, std::vector<Node>& vals, bool pol);
   //----------end for ITE strategy

   //----------for CONCAT strategies
   /** the position in the strings
    *
    * For each i/o example pair, this stores the length of the current solution
    * for the input of the pair, where the solution for that input is a prefix
    * or
    * suffix of the output of the pair. For example, if our i/o pairs are:
    *   f( "abcd" ) = "abcdcd"
    *   f( "aa" ) = "aacd"
    * If the solution we have currently constructed is str.++( x1, "c", ... ),
    * then d_str_pos = ( 5, 3 ), where notice that
    *   str.++( "abc", "c" ) is a prefix of "abcdcd" and
    *   str.++( "aa", "c" ) is a prefix of "aacd".
    */
   std::vector<unsigned> d_str_pos;
   /** has string position
    *
    * Whether the solution positions indicate a prefix or suffix of the output
    * examples. If this is role_invalid, then we have not updated the string
    * position.
    */
   NodeRole d_has_string_pos;
   /** update the string examples
    *
    * This method updates d_str_pos to d_str_pos + pos.
    */
   bool updateStringPosition(CegConjecturePbe* pbe, std::vector<unsigned>& pos);
   /** get current strings
    *
    * This returns the prefix/suffix of the string constants stored in vals
    * of size d_str_pos, and stores the result in ex_vals. For example, if vals
    * is (abcdcd", "aacde") and d_str_pos = ( 5, 3 ), then we add
    * "d" and "de" to ex_vals.
    */
   void getCurrentStrings(CegConjecturePbe* pbe,
                          const std::vector<Node>& vals,
                          std::vector<String>& ex_vals);
   /** get string increment
    *
    * If this method returns true, then inc and tot are updated such that
    *   for all active indices i,
    *      vals[i] is a prefix (or suffix if isPrefix=false) of ex_vals[i], and
    *      inc[i] = str.len(vals[i])
    *   for all inactive indices i, inc[i] = 0
    * We set tot to the sum of inc[i] for i=1,...,n. This indicates the total
    * number of characters incremented across all examples.
    */
   bool getStringIncrement(CegConjecturePbe* pbe,
                           bool isPrefix,
                           const std::vector<String>& ex_vals,
                           const std::vector<Node>& vals,
                           std::vector<unsigned>& inc,
                           unsigned& tot);
   /** returns true if ex_vals[i] = vals[i] for all active indices i. */
   bool isStringSolved(CegConjecturePbe* pbe,
                       const std::vector<String>& ex_vals,
                       const std::vector<Node>& vals);
   //----------end for CONCAT strategies

   /** is return value modified?
    *
    * This returns true if we are currently in a state where the return value
    * of the solution has been modified, e.g. by a previous node that solved
    * for a prefix.
    */
   bool isReturnValueModified();
   /** returns true if argument is valid strategy in this context */
   bool isValidStrategy(EnumTypeInfoStrat* etis);
   /** visited role
    *
    * This is the current set of enumerator/node role pairs we are currently
    * visiting. This set is cleared when the context is updated.
    */
   std::map<Node, std::map<NodeRole, bool> > d_visit_role;

   /** unif context enumerator information */
   class UEnumInfo
   {
    public:
     UEnumInfo() {}
     /** map from conditions and branch positions to a solved node
      *
      * For example, if we have:
      *   f( 1 ) = 2 ^ f( 3 ) = 4 ^ f( -1 ) = 1
      * Then, valid entries in this map is:
      *   d_look_ahead_sols[x>0][1] = x+1
      *   d_look_ahead_sols[x>0][2] = 1
      * For the first entry, notice that  for all input examples such that x>0
      * evaluates to true, which are (1) and (3), we have that their output
      * values for x+1 under the substitution that maps x to the input value,
      * resulting in 2 and 4, are equal to the output value for the respective
      * pairs.
      */
     std::map<Node, std::map<unsigned, Node> > d_look_ahead_sols;
    };
    /** map from enumerators to the above info class */
    std::map< Node, UEnumInfo > d_uinfo;
  };

  /** construct solution
   *
   * This method tries to construct a solution for function-to-synthesize c
   * based on the strategy stored for c in d_cinfo, which may include
   * synthesis-by-unification approaches for ite and string concatenation terms.
   * These approaches include the work of Alur et al. TACAS 2017.
   * If it cannot construct a solution, it returns the null node.
   */
  Node constructSolution( Node c );
  /** helper function for construct solution.
   *
   * Construct a solution based on enumerator e for function-to-synthesize c
   * with node role nrole in context x.
   *
   * ind is the term depth of the context (for debugging).
   */
  Node constructSolution(
      Node c, Node e, NodeRole nrole, UnifContext& x, int ind);
  /** Heuristically choose the best solved term from solved in context x,
   * currently return the first. */
  Node constructBestSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  /** Heuristically choose the best solved string term  from solved in context
   * x, currently  return the first. */
  Node constructBestStringSolvedTerm( std::vector< Node >& solved, UnifContext& x );
  /** Heuristically choose the best solved conditional term  from solved in
   * context x, currently random */
  Node constructBestSolvedConditional( std::vector< Node >& solved, UnifContext& x );
  /** Heuristically choose the best conditional term  from conds in context x,
   * currently random */
  Node constructBestConditional( std::vector< Node >& conds, UnifContext& x );
  /** Heuristically choose the best string to concatenate from strs to the
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
};

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

#endif
