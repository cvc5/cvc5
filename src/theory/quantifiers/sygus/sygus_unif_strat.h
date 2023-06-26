/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * sygus_unif_strat
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_STRAT_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_STRAT_H

#include <map>

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbSygus;

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
 * SygusUnif::constructSolution (see details below).
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

/** virtual base class for context in synthesis-by-unification approaches */
class UnifContext
{
 public:
  virtual ~UnifContext() {}

  /** Get the current role
   *
   * In a particular context when constructing solutions in synthesis by
   * unification, we may be solving based on a modified role. For example,
   * if we are currently synthesizing x in a solution ("a" ++ x), we are
   * synthesizing the string suffix of the overall solution. In this case, this
   * function returns role_string_suffix.
   */
  virtual NodeRole getCurrentRole() = 0;
  /** is return value modified?
   *
   * This returns true if we are currently in a state where the return value
   * of the solution has been modified, e.g. by a previous node that solved
   * for a string prefix.
   */
  bool isReturnValueModified() { return getCurrentRole() != role_equal; }
};

/**
* This class stores information regarding an enumerator, including
* information regarding the role of this enumerator (see EnumRole), its
* parent, whether it is templated, its slave enumerators, and so on.
*
* We say an enumerator is a master enumerator if it is the variable that
* we use to enumerate values for its sort. Master enumerators may have
* (possibly multiple) slave enumerators, stored in d_enum_slave. When
* constructing a sygus unifciation strategy, we make the first enumerator for
* each type a master enumerator, and any additional ones slaves of it.
*/
class EnumInfo
{
 public:
  EnumInfo() : d_role(enum_io), d_is_conditional(false) {}
  /** initialize this class
  *
  * role is the "role" the enumerator plays in the high-level strategy,
  *   which is one of enum_* above.
  */
  void initialize(EnumRole role);
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
  /** returns if this enumerator is conditional */
  bool isConditional() { return d_is_conditional; }
  /** get the role of this enumerator */
  EnumRole getRole() { return d_role; }
  /** enumerator template
  *
  * If d_template non-null, enumerated values V are immediately transformed to
  * d_template { d_template_arg -> V }.
  */
  Node d_template;
  Node d_template_arg;
  /**
  * Slave enumerators of this enumerator. These are other enumerators that
  * have the same type, but a different role in the strategy tree. We
  * generally
  * only use one enumerator per type, and hence these slaves are notified when
  * values are enumerated for this enumerator.
  */
  std::vector<Node> d_enum_slave;

 private:
  /** the role of this enumerator (one of enum_* above). */
  EnumRole d_role;
  /** is this enumerator conditional */
  bool d_is_conditional;
};

class EnumTypeInfoStrat;

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

/**
 * Stores all enumerators and strategies for a SyGuS datatype type.
 */
class EnumTypeInfo
{
 public:
  EnumTypeInfo() {}
  /** the type that this information is for */
  TypeNode d_this_type;
  /** map from enum roles to enumerators for this type */
  std::map<EnumRole, Node> d_enum;
  /** map from node roles to strategy nodes */
  std::map<NodeRole, StrategyNode> d_snodes;
  /** get strategy node for node role */
  StrategyNode& getStrategyNode(NodeRole nrole);
};

/** represents a strategy for a SyGuS datatype type
  *
  * This represents a possible strategy to apply when processing a strategy
  * node in constructSolution. When applying the strategy represented by this
  * class, we may make recursive calls to the children of the strategy,
  * given in d_cenum. If all recursive calls to constructSolution for these
  * children are successful, say:
  *   constructSolution( d_cenum[1], ... ) = t1,
  *    ...,
  *   constructSolution( d_cenum[n], ... ) = tn,
  * Then, the solution returned by this strategy is
  *   d_sol_templ * { d_sol_templ_args -> (t1,...,tn) }
  * where * is application of substitution.
  */
class EnumTypeInfoStrat
{
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
  /** Returns true if argument is valid strategy in unification context x */
  bool isValid(UnifContext& x);
};

/**
 * flags for extra restrictions to be inferred during redundant operators
 * learning
 */
struct StrategyRestrictions
{
  StrategyRestrictions() : d_iteReturnBoolConst(false), d_iteCondOnlyAtoms(true)
  {
  }
  /**
   * if this flag is true then staticLearnRedundantOps will also try to make
   * the return value of boolean ITEs to be restricted to constants
   */
  bool d_iteReturnBoolConst;
  /**
   * if this flag is true then staticLearnRedundantOps will also try to make
   * the condition values of ITEs to be restricted to atoms
   */
  bool d_iteCondOnlyAtoms;
  /**
   * A list of unused strategies. This maps strategy points to the indices
   * in StrategyNode::d_strats that are not used by the caller of
   * staticLearnRedundantOps, and hence should not be taken into account
   * when doing redundant operator learning.
   */
  std::map<Node, std::unordered_set<unsigned>> d_unused_strategies;
};

/**
 * Stores strategy and enumeration information for a function-to-synthesize.
 *
 * When this class is initialized, we construct a "strategy tree" based on
 * the grammar of the function to synthesize f. This tree is represented by
 * the above classes.
 */
class SygusUnifStrategy : protected EnvObj
{
 public:
  SygusUnifStrategy(Env& env) : EnvObj(env), d_tds(nullptr) {}
  /** initialize
   *
   * This initializes this class with function-to-synthesize f. We also call
   * f the candidate variable.
   *
   * This call constructs a set of enumerators for the relevant subfields of
   * the grammar of f and adds them to enums.
   */
  void initialize(TermDbSygus* tds, Node f, std::vector<Node>& enums);
  /** Get the root enumerator for this class */
  Node getRootEnumerator() const;
  /**
   * Get the enumerator info for enumerator e, where e must be an enumerator
   * initialized by this class (in enums after a call to initialize).
   */
  EnumInfo& getEnumInfo(Node e);
  /**
   * Get the enumerator type info for sygus type t, where t must be the type
   * of some enumerator initialized by this class
   */
  EnumTypeInfo& getEnumTypeInfo(TypeNode tn);

  /** static learn redundant operators
   *
   * This learns static lemmas for pruning enumerative space based on the
   * strategy for the function-to-synthesize of this class, and stores these
   * into strategy_lemmas.
   *
   * These may correspond to static symmetry breaking predicates (for example,
   * those that exclude ITE from enumerators whose role is enum_io when the
   * strategy is ITE_strat).
   *
   * then the module may also try to apply the given pruning restrictions (see
   * StrategyRestrictions for more details)
   */
  void staticLearnRedundantOps(
      std::map<Node, std::vector<Node>>& strategy_lemmas,
      StrategyRestrictions& restrictions);
  /**
   * creates the default restrictions when they are not given and calls the
   * above function
   */
  void staticLearnRedundantOps(
      std::map<Node, std::vector<Node>>& strategy_lemmas);

  /** debug print this strategy on Trace c */
  void debugPrint(const char* c);

 private:
  /** pointer to the term database sygus */
  TermDbSygus* d_tds;
  /** The candidate variable this strategy is for */
  Node d_candidate;
  /** maps enumerators to relevant information */
  std::map<Node, EnumInfo> d_einfo;
  /** list of all enumerators for the function-to-synthesize */
  std::vector<Node> d_esym_list;
  /** Info for sygus datatype type occurring in a field of d_root */
  std::map<TypeNode, EnumTypeInfo> d_tinfo;
  /**
    * The root sygus datatype for the function-to-synthesize,
    * which encodes the overall syntactic restrictions on the space
    * of solutions.
    */
  TypeNode d_root;
  /**
    * Maps sygus datatypes to their master enumerator. This is the (single)
    * enumerator of that type that we enumerate values for.
    */
  std::map<TypeNode, Node> d_master_enum;
  /** Initialize necessary information for (sygus) type tn */
  void initializeType(TypeNode tn);

  //-----------------------debug printing
  /** print ind indentations on trace c */
  static void indent(const char* c, int ind);
  //-----------------------end debug printing

  //------------------------------ strategy registration
  /** build strategy graph
   *
   * This builds the strategy for enumerated values of type tn for the given
   * role of nrole, for solutions to function-to-synthesize of this class.
   */
  void buildStrategyGraph(TypeNode tn, NodeRole nrole);
  /** register enumerator
   *
   * This registers that et is an enumerator of type tn, having enumerator
   * role enum_role.
   *
   * inSearch is whether we will enumerate values based on this enumerator.
   * A strategy node is represented by a (enumerator, node role) pair. Hence,
   * we may use enumerators for which this flag is false to represent strategy
   * nodes that have child strategies.
   */
  void registerStrategyPoint(Node et,
                          TypeNode tn,
                          EnumRole enum_role,
                          bool inSearch);
  /** infer template */
  bool inferTemplate(unsigned k,
                     Node n,
                     std::map<Node, unsigned>& templ_var_index,
                     std::map<unsigned, unsigned>& templ_injection);
  /** helper for static learn redundant operators
   *
   * (e, nrole) specify the strategy node in the graph we are currently
   * analyzing, visited stores the nodes we have already visited.
   *
   * This method builds the mapping needs_cons, which maps (master) enumerators
   * to a map from the constructors that it needs.
   */
  void staticLearnRedundantOps(
      Node e,
      NodeRole nrole,
      std::map<Node, std::map<NodeRole, bool>>& visited,
      std::map<Node, std::map<unsigned, bool>>& needs_cons,
      StrategyRestrictions& restrictions);
  /** finish initialization of the strategy tree
   *
   * (e, nrole) specify the strategy node in the graph we are currently
   * analyzing, visited stores the nodes we have already visited.
   *
   * isCond is whether the current enumerator is conditional (beneath a
   * conditional of an strat_ITE strategy).
   */
  void finishInit(Node e,
                  NodeRole nrole,
                  std::map<Node, std::map<NodeRole, bool> >& visited,
                  bool isCond);
  /** helper for debug print
   *
   * Prints the node e with role nrole on Trace(c).
   *
   * (e, nrole) specify the strategy node in the graph we are currently
   * analyzing, visited stores the nodes we have already visited.
   *
   * ind is the current level of indentation (for debugging)
   */
  void debugPrint(const char* c,
                  Node e,
                  NodeRole nrole,
                  std::map<Node, std::map<NodeRole, bool> >& visited,
                  int ind);
  //------------------------------ end strategy registration
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_UNIF_H */
