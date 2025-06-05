/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for augmenting model-based instantiations via fast sygus enumeration.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MBQI_ENUM_H
#define CVC5__THEORY__QUANTIFIERS__MBQI_ENUM_H

#include <map>
#include <unordered_map>

#include "expr/sygus_term_enumerator.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstStrategyMbqi;

/**
 * Maintains a sygus enumeration for a single quantified variable in our
 * strategy.
 */
class MVarInfo
{
 public:
  /**
   * Initialize this class for variable v of quantified formula q.
   *
   * @param env Reference to the environment.
   * @param q The quantified formula.
   * @param v The variable from q we are enumerating terms for.
   * @param etrules A list of terms which to consider terminals in the grammar
   * we enumerate. These terms may be of any sort.
   */
  void initialize(Env& env,
                  const Node& q,
                  const Node& v,
                  const std::vector<Node>& etrules);
  /**
   * Get the i^th term in the enumeration maintained by this class. Will
   * continue the sygus enumeration if i is greater than the number of terms
   * enumerated so far.
   */
  Node getEnumeratedTerm(NodeManager* nm, size_t i);

 private:
  /** The underlying sygus enumerator utility */
  std::unique_ptr<SygusTermEnumerator> d_senum;
  /** A cache of all enumerated terms so far */
  std::vector<Node> d_enum;
  /**
   * If we are enumerating function values, this is a BOUND_VAR_LIST node.
   * The terms we enumerate are t_1, ..., which are transformed to
   * (lambda <var_list> t_1) ... for this variable list.
   */
  Node d_lamVars;
};

/**
 * Maintains information about a quantified formula in our strategy, including
 * which variables are processed/unprocessed, and the sygus enumeration for
 * each of them (in MVarInfo).
 */
class MQuantInfo
{
 public:
  /**
   * Intialize the instantiation strategy for quantified formula q.
   *
   * @param env Reference to the environment.
   * @param parent Reference to the parent instantiation strategy.
   * @param q The quantified formula.
   */
  void initialize(Env& env, InstStrategyMbqi& parent, const Node& q);
  /** Get indices of variables to instantiate */
  std::vector<size_t> getInstIndices();
  /** Get indices of variables not to instantiate */
  std::vector<size_t> getNoInstIndices();
  /** Get variable info for the index^th variable of the quantified formula */
  MVarInfo& getVarInfo(size_t index);
  /** Should we enumerate terms for type tn? */
  static bool shouldEnumerate(const TypeNode& tn);

 private:
  /** The quantified formula */
  Node d_quant;
  /** A list of variable informations for each of the variables of q */
  std::vector<MVarInfo> d_vinfo;
  /** The indices of variables we are enumerating */
  std::vector<size_t> d_indices;
  /** The indices of variables we are not enumerating */
  std::vector<size_t> d_nindices;
};

/**
 * MbqiEnum, which postprocesses an instantiation from MBQI based on
 * sygus enumeration.
 */
class MbqiEnum : protected EnvObj
{
 public:
  MbqiEnum(Env& env, InstStrategyMbqi& parent);
  ~MbqiEnum() {}

  /**
   * Updates mvs to the desired instantiation of q. Returns true if successful.
   *
   * In detail, this method maintains the invariant that
   *   query[ mvs / vars ] is satisfiable.
   * This is initially guaranteed since mvs is a model for vars in query
   * due to MBQI. This method iterates over the variables vars[i] and replaces
   * mvs[i] with the first term in the SyGuS enumeration such that the updated
   * mvs still satisfies the query. Checking whether the invariant holds is
   * confirmed via a subsolver call for each replacement.
   *
   * @param q The quantified formula to instantiate.
   * @param query The query that was made to a subsolver for MBQI.
   * @param vars The input variables that were used in the query, which
   * correspond 1-to-1 with the variables of the quantified formula.
   * @param mvs The model values of vars found in the subsolver for MBQI.
   * @param mvFreshVar Maps model values to variables, for the purposes
   * of representing term models for uninterpreted sorts.
   * @return true if we successfully modified the instantiation.
   */
  bool constructInstantiation(const Node& q,
                              const Node& query,
                              const std::vector<Node>& vars,
                              std::vector<Node>& mvs,
                              const std::map<Node, Node>& mvFreshVar);

 private:
  /**
   * @return The information for quantified formula q.
   */
  MQuantInfo& getOrMkQuantInfo(const Node& q);
  /** Map from quantified formulas to information above */
  std::map<Node, MQuantInfo> d_qinfo;
  /** Reference to the parent instantiation strategy */
  InstStrategyMbqi& d_parent;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__MBQI_ENUM_H */
