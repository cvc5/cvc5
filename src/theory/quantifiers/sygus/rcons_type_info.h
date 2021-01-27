/*********************                                                        */
/*! \file rcons_type_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility class for Sygus Reconstruct module
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__RCONS_TYPE_INFO_H
#define CVC4__THEORY__QUANTIFIERS__RCONS_TYPE_INFO_H

#include "theory/quantifiers/sygus/sygus_enumerator.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * A utility class for Sygus Reconstruct datatype types (grammar non-terminals).
 */
class RConsTypeInfo
{
 public:
  /**
   * Initialize a sygus enumerator and a candidate rewrite database for the
   * corresponding sygus datatype type.
   *
   * @param tds Database for sygus terms
   * @param s Statistics managed for the synth engine
   * @param stn The sygus datatype type encoding the syntax restrictions
   * @param builtinVars A list containing the builtin analog of sygus variable
   *                    list for the sygus datatype type
   */
  void initialize(TermDbSygus* tds,
                  SygusStatistics& s,
                  TypeNode stn,
                  const std::vector<Node>& builtinVars);

  /**
   * Returns the next enumerated term for the given sygus datatype type.
   *
   * @param stn The sygus datatype type to enumerate a term for
   * @return The enumerated sygus term
   */
  Node nextEnum();

  /**
   * Add a ground term to the candidate rewrite database for the corresponding
   * sygus datatype type.
   *
   * @param n The term to add to the database
   * @return A previous term `eq_n` added to this class, such that `n` is
   * equivalent to `eq_n`
   */
  Node addTerm(Node n);

  /**
   * Set the obligation responsible for solving the given builtin term.
   *
   * @param builtin The builtin term
   * @param ob The corresponding obligation
   */
  void setObligation(Node builtin, Node ob);

  /**
   * Return the obligation responsible for solving the given builtin term.
   *
   * @param builtin The builtin term
   * @return The corresponding obligation
   */
  Node builtinToOb(Node builtin);

  /**
   * Reset the state of this RConsTypeInfo object.
   */
  void clear();

 private:
  /** Sygus terms enumerator for the corresponding Sygus datatype type */
  std::unique_ptr<SygusEnumerator> d_enumerator;
  /** Candidate rewrite database for the corresponding sgyus datatype type */
  std::unique_ptr<CandidateRewriteDatabase> d_crd;
  /** Sygus sampler needed for initializing the candidate rewrite database */
  SygusSampler d_sygusSampler;
  /** a map from a builtin term to its obligation. The sygus type of the
   * obligation is needed as different sygus types may have obligations to
   * reconstruct the same builtin term */
  std::unordered_map<Node, Node, NodeHashFunction> d_ob;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif  // CVC4__THEORY__QUANTIFIERS__RCONS_TYPE_INFO_H
