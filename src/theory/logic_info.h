/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class giving information about a logic (group of theory modules and
 * configuration information).
 */

#include "cvc5_public.h"

#ifndef CVC5__LOGIC_INFO_H
#define CVC5__LOGIC_INFO_H

#include <cvc5/cvc5_export.h>

#include <string>
#include <vector>

#include "theory/theory_id.h"

namespace cvc5::internal {

/**
 * A LogicInfo instance describes a collection of theory modules and some
 * basic configuration about them.  Conceptually, it provides a background
 * context for all operations in cvc5.  Typically, when cvc5's SolverEngine
 * is created, it is issued a setLogic() command indicating features of the
 * assertions and queries to follow---for example, whether quantifiers are
 * used, whether integers or reals (or both) will be used, etc.
 *
 * Most places in cvc5 will only ever need to access a const reference to an
 * instance of this class.  Such an instance is generally set by the
 * SolverEngine when setLogic() is called.  However, mutating member functions
 * are also provided by this class so that it can be used as a more general
 * mechanism (e.g., for communicating to the SolverEngine which theories should
 * be used, rather than having to provide an SMT-LIB string).
 */
class CVC5_EXPORT LogicInfo
{
  mutable std::string d_logicString; /**< an SMT-LIB-like logic string */
  std::vector<bool> d_theories; /**< set of active theories */
  size_t d_sharingTheories; /**< count of theories that need sharing */

  /** are integers used in this logic? */
  bool d_integers;
  /** are reals used in this logic? */
  bool d_reals;
  /** transcendentals in this logic? */
  bool d_transcendentals;
  /** linear-only arithmetic in this logic? */
  bool d_linear;
  /** difference-only arithmetic in this logic? */
  bool d_differenceLogic;
  /** cardinality constraints in this logic? */
  bool d_cardinalityConstraints;
  /** higher-order constraints in this logic? */
  bool d_higherOrder;

  bool d_locked; /**< is this LogicInfo instance locked (and thus immutable)? */

  /**
   * Returns true iff this is a "true" theory (one that must be worried
   * about for sharing
   */
  static inline bool isTrueTheory(theory::TheoryId theory) {
    switch(theory) {
    case theory::THEORY_BUILTIN:
    case theory::THEORY_BOOL:
    case theory::THEORY_QUANTIFIERS:
      return false;
    default:
      return true;
    }
  }

public:

  /**
   * Constructs a LogicInfo for the most general logic (quantifiers, all
   * background theory modules, ...).
   */
  LogicInfo();

  /**
   * Construct a LogicInfo from an SMT-LIB-like logic string.
   * Throws an IllegalArgumentException if the logic string cannot
   * be interpreted.
   */
  LogicInfo(std::string logicString);

  /**
   * Construct a LogicInfo from an SMT-LIB-like logic string.
   * Throws an IllegalArgumentException if the logic string cannot
   * be interpreted.
   */
  LogicInfo(const char* logicString);

  // ACCESSORS

  /**
   * Get an SMT-LIB-like logic string.  These are only guaranteed to
   * be SMT-LIB-compliant if an SMT-LIB-compliant string was used in
   * the constructor and no mutating functions were called.
   */
  std::string getLogicString() const;

  /** Is sharing enabled for this logic? */
  bool isSharingEnabled() const;

  /** Is the given theory module active in this logic? */
  bool isTheoryEnabled(theory::TheoryId theory) const;

  /** Is this a quantified logic? */
  bool isQuantified() const;

  /** Is this a logic that includes the all-inclusive logic?
   *
   * @return Yields true if the logic corresponds to "ALL" or its super
   * set including , such as "HO_ALL".
   */
  bool hasEverything() const;

  /** Is this the all-exclusive logic?  (Here, that means propositional logic) */
  bool hasNothing() const;

  /**
   * Is this a pure logic (only one "true" background theory).  Quantifiers
   * can exist in such logics though; to test for quantifier-free purity,
   * use "isPure(theory) && !isQuantified()".
   */
  bool isPure(theory::TheoryId theory) const;

  // these are for arithmetic

  /** Are integers in this logic? */
  bool areIntegersUsed() const;

  /** Are reals in this logic? */
  bool areRealsUsed() const;

  /** Are transcendentals in this logic? */
  bool areTranscendentalsUsed() const;

  /** Does this logic only linear arithmetic? */
  bool isLinear() const;

  /** Does this logic only permit difference reasoning? (implies linear) */
  bool isDifferenceLogic() const;

  /** Does this logic allow cardinality constraints? */
  bool hasCardinalityConstraints() const;

  /** Is this a higher order logic? */
  bool isHigherOrder() const;

  // MUTATORS

  /**
   * Initialize the LogicInfo with an SMT-LIB-like logic string.
   * Throws an IllegalArgumentException if the string can't be
   * interpreted.
   */
  void setLogicString(std::string logicString);

  /**
   * Enable all functionality.  All theories, plus quantifiers, will be
   * enabled.
   *
   * @param enableHigherOrder Whether HOL should be enable together with the
   * above.
   */
  void enableEverything(bool enableHigherOrder = false);

  /**
   * Disable all functionality.  The result will be a LogicInfo with
   * the BUILTIN and BOOLEAN theories enabled only ("QF_SAT").
   */
  void disableEverything();

  /**
   * Enable the given theory module.
   */
  void enableTheory(theory::TheoryId theory);

  /**
   * Disable the given theory module.  THEORY_BUILTIN and THEORY_BOOL cannot
   * be disabled (and if given here, the request will be silently ignored).
   */
  void disableTheory(theory::TheoryId theory);

  /**
   * Quantifiers are a special case, since two theory modules handle them.
   */
  void enableQuantifiers() {
    enableTheory(theory::THEORY_QUANTIFIERS);
  }

  /**
   * Quantifiers are a special case, since two theory modules handle them.
   */
  void disableQuantifiers() {
    disableTheory(theory::THEORY_QUANTIFIERS);
  }

  /**
   * Enable everything that is needed for sygus with respect to this logic info.
   * This means enabling quantifiers, datatypes, UF, integers, and higher order.
   */
  void enableSygus();
  /**
   * Enable everything that is needed for separation logic. This means enabling
   * the theories of separation logic, UF and sets.
   */
  void enableSeparationLogic();

  // these are for arithmetic

  /** Enable the use of integers in this logic. */
  void enableIntegers();
  /** Disable the use of integers in this logic. */
  void disableIntegers();
  /** Enable the use of reals in this logic. */
  void enableReals();
  /** Disable the use of reals in this logic. */
  void disableReals();
  /** Enable the use of transcendentals in this logic. */
  void arithTranscendentals();
  /** Only permit difference arithmetic in this logic. */
  void arithOnlyDifference();
  /** Only permit linear arithmetic in this logic. */
  void arithOnlyLinear();
  /** Permit nonlinear arithmetic in this logic. */
  void arithNonLinear();

  // for cardinality constraints

  /** Enable the use of cardinality constraints in this logic. */
  void enableCardinalityConstraints();
  /** Disable the use of cardinality constraints in this logic. */
  void disableCardinalityConstraints();

  // for higher-order

  /** Enable the use of higher-order in this logic. */
  void enableHigherOrder();
  /** Disable the use of higher-order in this logic. */
  void disableHigherOrder();

  // LOCKING FUNCTIONALITY

  /** Lock this LogicInfo, disabling further mutation and allowing queries */
  void lock() { d_locked = true; }
  /** Check whether this LogicInfo is locked, disallowing further mutation */
  bool isLocked() const { return d_locked; }
  /** Get a copy of this LogicInfo that is identical, but unlocked */
  LogicInfo getUnlockedCopy() const;

  // COMPARISON

  /** Are these two LogicInfos equal? */
  bool operator==(const LogicInfo& other) const;

  /** Are these two LogicInfos disequal? */
  bool operator!=(const LogicInfo& other) const {
    return !(*this == other);
  }

  /** Is this LogicInfo "greater than" (does it contain everything and more) the other? */
  bool operator>(const LogicInfo& other) const {
    return *this >= other && *this != other;
  }

  /** Is this LogicInfo "less than" (does it contain strictly less) the other? */
  bool operator<(const LogicInfo& other) const {
    return *this <= other && *this != other;
  }
  /** Is this LogicInfo "less than or equal" the other? */
  bool operator<=(const LogicInfo& other) const;

  /** Is this LogicInfo "greater than or equal" the other? */
  bool operator>=(const LogicInfo& other) const;

  /** Are two LogicInfos comparable?  That is, is one of <= or > true? */
  bool isComparableTo(const LogicInfo& other) const {
    return *this <= other || *this >= other;
  }

}; /* class LogicInfo */

std::ostream& operator<<(std::ostream& out, const LogicInfo& logic);

}  // namespace cvc5::internal

#endif /* CVC5__LOGIC_INFO_H */
