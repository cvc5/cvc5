/*********************                                                        */
/*! \file sygus_unif_io.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief sygus_unif_rl
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H
#define __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H

#include <map>
#include "theory/quantifiers/sygus/sygus_unif.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Sygus unification Refinement Lemmas utility
 *
 * This class implement synthesis-by-unification, where the specification is a
 * set of refinement lemmas. With respect to SygusUnif, it's main interface
 * function is addExample, which adds a refinement lemma to the specification.
 */
class SygusUnifRl : public SygusUnif
{
  friend class UnifContextRl;

 public:
  SygusUnifRl();
  ~SygusUnifRl();

  /** initialize */
  virtual void initialize(QuantifiersEngine* qe,
                          Node f,
                          std::vector<Node>& enums,
                          std::vector<Node>& lemmas) override;
  /** Notify enumeration */
  virtual void notifyEnumeration(Node e,
                                 Node v,
                                 std::vector<Node>& lemmas) override;
  /** add refinement lemma
   *
   * This adds a lemma to the specification for f.
   */
  void addRefLemma(Node lemma);

 protected:
  /** set of refinmente lemmas */
  std::vector<std::vector<Node>> d_refLemmas;

  /**
  * This class stores information regarding an enumerator, including:
  * a database of values that have been enumerated for this enumerator.
  */
  class EnumCache
  {
   public:
    EnumCache() {}
    /**
    * Notify this class that the term v has been enumerated for this enumerator.
    * Its evaluation under the set of examples in sui are stored in results.
    */
    void addEnumValue(Node v, std::vector<Node>& results);
    /**
    * Notify this class that slv is the complete solution to the synthesis
    * conjecture. This occurs rarely, for instance, when during an ITE strategy
    * we find that a single enumerated term satisfies all lemmas.
    */
    void setSolved(Node slv) { d_enum_solved = slv; }
    /** Have we been notified that a complete solution exists? */
    bool isSolved() { return !d_enum_solved.isNull(); }
    /** Get the complete solution to the synthesis conjecture. */
    Node getSolved() { return d_enum_solved; }
    /** Values that have been enumerated for this enumerator */
    std::vector<Node> d_enum_vals;

   private:
    /**
      * Whether an enumerated value for this conjecture has solved the entire
      * conjecture.
      */
    Node d_enum_solved;
  };
  /** maps enumerators to the information above */
  std::map<Node, EnumCache> d_ecache;

  /** the unification context used within constructSolution */
  UnifContextRl d_context;
  /** initialize construct solution */
  void initializeConstructSol() override;
  /** construct solution */
  Node constructSol(Node e, NodeRole nrole, int ind) override;
};

} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__SYGUS_UNIF_RL_H */
