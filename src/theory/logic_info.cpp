/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class giving information about a logic (group a theory modules
 * and configuration information)
 */
#include "theory/logic_info.h"

#include <cstring>
#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "base/configuration.h"
#include "expr/kind.h"

using namespace std;
using namespace cvc5::internal::theory;

namespace cvc5::internal {

LogicInfo::LogicInfo()
    : d_logicString(""),
      d_theories(THEORY_LAST, false),
      d_sharingTheories(0),
      d_integers(true),
      d_reals(true),
      d_transcendentals(true),
      d_linear(false),
      d_differenceLogic(false),
      d_cardinalityConstraints(false),
      d_higherOrder(false),
      d_locked(false)
{
  for (TheoryId id = THEORY_FIRST; id < THEORY_LAST; ++id)
  {
    enableTheory(id);
  }
}

LogicInfo::LogicInfo(std::string logicString)
    : d_logicString(""),
      d_theories(THEORY_LAST, false),
      d_sharingTheories(0),
      d_integers(false),
      d_reals(false),
      d_transcendentals(false),
      d_linear(false),
      d_differenceLogic(false),
      d_cardinalityConstraints(false),
      d_higherOrder(false),
      d_locked(false)
{
  setLogicString(logicString);
  lock();
}

LogicInfo::LogicInfo(const char* logicString)
    : d_logicString(""),
      d_theories(THEORY_LAST, false),
      d_sharingTheories(0),
      d_integers(false),
      d_reals(false),
      d_transcendentals(false),
      d_linear(false),
      d_differenceLogic(false),
      d_cardinalityConstraints(false),
      d_higherOrder(false),
      d_locked(false)
{
  setLogicString(logicString);
  lock();
}

/** Is sharing enabled for this logic? */
bool LogicInfo::isSharingEnabled() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  return d_sharingTheories > 1;
}


/** Is the given theory module active in this logic? */
bool LogicInfo::isTheoryEnabled(theory::TheoryId theory) const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  return d_theories[theory];
}

/** Is this a quantified logic? */
bool LogicInfo::isQuantified() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  return isTheoryEnabled(theory::THEORY_QUANTIFIERS);
}

/** Is this a higher-order logic? */
bool LogicInfo::isHigherOrder() const
{
  PrettyCheckArgument(d_locked,
                      *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  return d_higherOrder;
}

bool LogicInfo::hasEverything() const
{
  PrettyCheckArgument(d_locked,
                      *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  LogicInfo everything;
  everything.enableEverything(isHigherOrder());
  everything.lock();
  return (*this == everything);
}

/** Is this the all-exclusive logic?  (Here, that means propositional logic) */
bool LogicInfo::hasNothing() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  LogicInfo nothing("");
  nothing.lock();
  return *this == nothing;
}

bool LogicInfo::isPure(theory::TheoryId theory) const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  // the third and fourth conjucts are really just to rule out the misleading
  // case where you ask isPure(THEORY_BOOL) and get true even in e.g. QF_LIA
  return isTheoryEnabled(theory) && !isSharingEnabled() &&
      ( !isTrueTheory(theory) || d_sharingTheories == 1 ) &&
      ( isTrueTheory(theory) || d_sharingTheories == 0 );
}

bool LogicInfo::areIntegersUsed() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  PrettyCheckArgument(
      isTheoryEnabled(theory::THEORY_ARITH), *this,
      "Arithmetic not used in this LogicInfo; cannot ask whether integers are used");
  return d_integers;
}

bool LogicInfo::areRealsUsed() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  PrettyCheckArgument(
      isTheoryEnabled(theory::THEORY_ARITH), *this,
      "Arithmetic not used in this LogicInfo; cannot ask whether reals are used");
  return d_reals;
}

bool LogicInfo::areTranscendentalsUsed() const
{
  PrettyCheckArgument(d_locked,
                      *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  PrettyCheckArgument(isTheoryEnabled(theory::THEORY_ARITH),
                      *this,
                      "Arithmetic not used in this LogicInfo; cannot ask "
                      "whether transcendentals are used");
  return d_transcendentals;
}

bool LogicInfo::isLinear() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  PrettyCheckArgument(
      isTheoryEnabled(theory::THEORY_ARITH), *this,
      "Arithmetic not used in this LogicInfo; cannot ask whether it's linear");
  return d_linear || d_differenceLogic;
}

bool LogicInfo::isDifferenceLogic() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  PrettyCheckArgument(
      isTheoryEnabled(theory::THEORY_ARITH), *this,
      "Arithmetic not used in this LogicInfo; cannot ask whether it's difference logic");
  return d_differenceLogic;
}

bool LogicInfo::hasCardinalityConstraints() const {
  PrettyCheckArgument(d_locked, *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  return d_cardinalityConstraints;
}


bool LogicInfo::operator==(const LogicInfo& other) const {
  PrettyCheckArgument(isLocked() && other.isLocked(), *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  for(theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    if(d_theories[id] != other.d_theories[id]) {
      return false;
    }
  }

  PrettyCheckArgument(d_sharingTheories == other.d_sharingTheories, *this,
                      "LogicInfo internal inconsistency");
  if (d_cardinalityConstraints != other.d_cardinalityConstraints ||
             d_higherOrder != other.d_higherOrder )
  {
    return false;
  }
  if(isTheoryEnabled(theory::THEORY_ARITH)) {
    return d_integers == other.d_integers && d_reals == other.d_reals
           && d_transcendentals == other.d_transcendentals
           && d_linear == other.d_linear
           && d_differenceLogic == other.d_differenceLogic;
  }
  return true;
}

bool LogicInfo::operator<=(const LogicInfo& other) const {
  PrettyCheckArgument(isLocked() && other.isLocked(), *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  for(theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    if(d_theories[id] && !other.d_theories[id]) {
      return false;
    }
  }
  PrettyCheckArgument(d_sharingTheories <= other.d_sharingTheories, *this,
                      "LogicInfo internal inconsistency");
  bool res = (!d_cardinalityConstraints || other.d_cardinalityConstraints)
             && (!d_higherOrder || other.d_higherOrder);
  if(isTheoryEnabled(theory::THEORY_ARITH) && other.isTheoryEnabled(theory::THEORY_ARITH)) {
    return (!d_integers || other.d_integers) && (!d_reals || other.d_reals)
           && (!d_transcendentals || other.d_transcendentals)
           && (d_linear || !other.d_linear)
           && (d_differenceLogic || !other.d_differenceLogic) && res;
  } else {
    return res;
  }
}

bool LogicInfo::operator>=(const LogicInfo& other) const {
  PrettyCheckArgument(isLocked() && other.isLocked(), *this,
                      "This LogicInfo isn't locked yet, and cannot be queried");
  for(theory::TheoryId id = theory::THEORY_FIRST; id < theory::THEORY_LAST; ++id) {
    if(!d_theories[id] && other.d_theories[id]) {
      return false;
    }
  }
  PrettyCheckArgument(d_sharingTheories >= other.d_sharingTheories, *this,
                      "LogicInfo internal inconsistency");
  bool res = (d_cardinalityConstraints || !other.d_cardinalityConstraints)
             && (d_higherOrder || !other.d_higherOrder);
  if(isTheoryEnabled(theory::THEORY_ARITH) && other.isTheoryEnabled(theory::THEORY_ARITH)) {
    return (d_integers || !other.d_integers) && (d_reals || !other.d_reals)
           && (d_transcendentals || !other.d_transcendentals)
           && (!d_linear || other.d_linear)
           && (!d_differenceLogic || other.d_differenceLogic) && res;
    } else {
      return res;
  }
}

std::string LogicInfo::getLogicString() const {
  PrettyCheckArgument(
      d_locked, *this,
      "This LogicInfo isn't locked yet, and cannot be queried");
  if(d_logicString == "") {
    LogicInfo qf_all_supported;
    qf_all_supported.disableQuantifiers();
    qf_all_supported.lock();
    stringstream ss;
    if (isHigherOrder())
    {
      ss << "HO_";
    }
    if (!isQuantified())
    {
      ss << "QF_";
    }
    if (*this == qf_all_supported || hasEverything())
    {
      ss << "ALL";
    }
    else
    {
      size_t seen = 0; // make sure we support all the active theories
      if (d_theories[THEORY_SEP])
      {
        ss << "SEP_";
        ++seen;
      }
      if(d_theories[THEORY_ARRAYS]) {
        ss << (d_sharingTheories == 1 ? "AX" : "A");
        ++seen;
      }
      if(d_theories[THEORY_UF]) {
        ss << "UF";
        ++seen;
      }
      if( d_cardinalityConstraints ){
        ss << "C";
      }
      if(d_theories[THEORY_BV]) {
        ss << "BV";
        ++seen;
      }
      if (d_theories[THEORY_FF])
      {
        ss << "FF";
        ++seen;
      }
      if(d_theories[THEORY_FP]) {
        ss << "FP";
        ++seen;
      }
      if(d_theories[THEORY_DATATYPES]) {
        ss << "DT";
        ++seen;
      }
      if(d_theories[THEORY_STRINGS]) {
        ss << "S";
        ++seen;
      }
      if(d_theories[THEORY_ARITH]) {
        if(isDifferenceLogic()) {
          ss << (areIntegersUsed() ? "I" : "");
          ss << (areRealsUsed() ? "R" : "");
          ss << "DL";
        } else {
          ss << (isLinear() ? "L" : "N");
          ss << (areIntegersUsed() ? "I" : "");
          ss << (areRealsUsed() ? "R" : "");
          ss << "A";
          ss << (areTranscendentalsUsed() ? "T" : "");
        }
        ++seen;
      }
      if(d_theories[THEORY_SETS]) {
        ss << "FS";
        ++seen;
      }
      if (d_theories[THEORY_BAGS])
      {
        ss << "FB";
        ++seen;
      }
      if(seen != d_sharingTheories) {
        Unhandled()
            << "can't extract a logic string from LogicInfo; at least one "
               "active theory is unknown to LogicInfo::getLogicString() !";
      }

      if(seen == 0) {
        ss << "SAT";
      }
    }
    d_logicString = ss.str();
  }
  return d_logicString;
}

void throwTwoArithmeticTheoriesError(const char* th1, const char* th2)
{
  stringstream err;
  err << "a logic name can only contain one arithmetic theory but found two: "
      << th1 << " and " << th2;
  throw cvc5::internal::Exception(err.str().c_str());
}

void checkMultipleArithmeticTheories(const char* prevTheory,
                                     const char* currentTheory)
{
  if (*prevTheory != '\0')
  {
    throwTwoArithmeticTheoriesError(prevTheory, currentTheory);
  }
}

void LogicInfo::checkDuplicateTheory(TheoryId theory, const char* id)
{
  if (d_theories[theory])
  {
    stringstream err;
    err << "duplicate theory: " << id;
    throw cvc5::internal::Exception(err.str().c_str());
  }
}

void LogicInfo::setLogicString(std::string logicString)
{
  PrettyCheckArgument(!d_locked, *this,
                      "This LogicInfo is locked, and cannot be modified");
  for(TheoryId id = THEORY_FIRST; id < THEORY_LAST; ++id) {
    d_theories[id] = false;// ensure it's cleared
  }
  d_sharingTheories = 0;

  // Below, ONLY use enableTheory()/disableTheory() rather than
  // accessing d_theories[] directly.  This makes sure to set up
  // sharing properly.

  enableTheory(THEORY_BUILTIN);
  enableTheory(THEORY_BOOL);

  const char* p = logicString.c_str();
  if (!strncmp(p, "HO_", 3))
  {
    enableHigherOrder();
    p += 3;
  }
  if(*p == '\0') {
    // propositional logic only; we're done.
  } else if(!strcmp(p, "QF_SAT")) {
    // propositional logic only; we're done.
    p += 6;
  } else if(!strcmp(p, "SAT")) {
    // quantified Boolean formulas only; we're done.
    enableQuantifiers();
    p += 3;
  } else if(!strcmp(p, "QF_ALL")) {
    // the "all theories included" logic, no quantifiers.
    enableEverything(d_higherOrder);
    disableQuantifiers();
    arithNonLinear();
    p += 6;
  } else if(!strcmp(p, "ALL")) {
    // the "all theories included" logic, with quantifiers.
    enableEverything(d_higherOrder);
    enableQuantifiers();
    arithNonLinear();
    p += 3;
  }
  else if (!strcmp(p, "HORN"))
  {
    // the HORN logic
    enableEverything(d_higherOrder);
    enableQuantifiers();
    arithNonLinear();
    p += 4;
  } else {
    if(!strncmp(p, "QF_", 3)) {
      disableQuantifiers();
      p += 3;
    } else {
      enableQuantifiers();
    }
    if (!strncmp(p, "SEP_", 4))
    {
      enableSeparationLogic();
      p += 4;
    }
    if(!strncmp(p, "AX", 2)) {
      enableTheory(THEORY_ARRAYS);
      p += 2;
    } else {
      // arithmeticTheory points to "\0" if no arithmetic theory has been read
      // yet; otherwise it points to the arithmetic theory that has already been
      // read.
      const char* arithmeticTheory = "\0";
      // whether an unrecognized theory has been read
      bool unrecognizedTheory = false;
      while (!unrecognizedTheory && (*p != '\0'))
      {
        if (*p == 'A')
        {
          checkDuplicateTheory(THEORY_ARRAYS, "A");
          enableTheory(THEORY_ARRAYS);
          ++p;
        }
        else if (!strncmp(p, "UF", 2))
        {
          checkDuplicateTheory(THEORY_UF, "UF");
          enableTheory(THEORY_UF);
          p += 2;
        }
        else if (!strncmp(p, "C", 1))
        {
          if (d_cardinalityConstraints)
          {
            throw cvc5::internal::Exception("duplicate theory: C");
          }
          enableCardinalityConstraints();
          p += 1;
        }
        else if (!strncmp(p, "BV", 2))
        {
          checkDuplicateTheory(THEORY_BV, "BV");
          enableTheory(THEORY_BV);
          p += 2;
        }
        else if (!strncmp(p, "FF", 2))
        {
          checkDuplicateTheory(THEORY_FF, "FF");
          enableTheory(THEORY_FF);
          p += 2;
        }
        else if (!strncmp(p, "FP", 2))
        {
          checkDuplicateTheory(THEORY_FP, "FP");
          enableTheory(THEORY_FP);
          p += 2;
        }
        else if (!strncmp(p, "DT", 2))
        {
          checkDuplicateTheory(THEORY_DATATYPES, "DT");
          enableTheory(THEORY_DATATYPES);
          p += 2;
        }
        else if (*p == 'S')
        {
          checkDuplicateTheory(THEORY_STRINGS, "S");
          enableTheory(THEORY_STRINGS);
          ++p;
        }
        else if (!strncmp(p, "IDL", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "IDL");
          enableIntegers();
          disableReals();
          arithOnlyDifference();
          p += 3;
          arithmeticTheory = "IDL";
        }
        else if (!strncmp(p, "RDL", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "RDL");
          disableIntegers();
          enableReals();
          arithOnlyDifference();
          arithmeticTheory = "RDL";
          p += 3;
        }
        else if (!strncmp(p, "IRDL", 4))
        {
          // "IRDL" ?! --not very useful, but getLogicString() can produce
          // that string, so we really had better be able to read it back in.
          checkMultipleArithmeticTheories(arithmeticTheory, "IRDL");
          enableIntegers();
          enableReals();
          arithOnlyDifference();
          arithmeticTheory = "IRDL";
          p += 4;
        }
        else if (!strncmp(p, "LIA", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "LIA");
          enableIntegers();
          disableReals();
          arithOnlyLinear();
          arithmeticTheory = "LIA";
          p += 3;
        }
        else if (!strncmp(p, "LRA", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "LRA");
          disableIntegers();
          enableReals();
          arithOnlyLinear();
          arithmeticTheory = "LRA";
          p += 3;
        }
        else if (!strncmp(p, "LIRA", 4))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "LIRA");
          enableIntegers();
          enableReals();
          arithOnlyLinear();
          arithmeticTheory = "LIRA";
          p += 4;
        }
        else if (!strncmp(p, "NIA", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "NIA");
          enableIntegers();
          disableReals();
          arithNonLinear();
          arithmeticTheory = "NIA";
          p += 3;
        }
        else if (!strncmp(p, "NRA", 3))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "NRA");
          disableIntegers();
          enableReals();
          arithNonLinear();
          arithmeticTheory = "NRA";
          p += 3;
          if (*p == 'T')
          {
            arithTranscendentals();
            p += 1;
          }
        }
        else if (!strncmp(p, "NIRA", 4))
        {
          checkMultipleArithmeticTheories(arithmeticTheory, "NIRA");
          enableIntegers();
          enableReals();
          arithNonLinear();
          arithmeticTheory = "NIRA";
          p += 4;
          if (*p == 'T')
          {
            arithTranscendentals();
            p += 1;
          }
        }
        else if (!strncmp(p, "FS", 2))
        {
          checkDuplicateTheory(THEORY_SETS, "FS");
          enableTheory(THEORY_SETS);
          p += 2;
        }
        else
        {
          unrecognizedTheory = true;
        }
      }
    }
  }

  if (d_theories[THEORY_FP])
  {
    // THEORY_BV is needed for bit-blasting.
    // We have to set this here rather than in expandDefinition as it
    // is possible to create variables without any theory specific
    // operations, so expandDefinition won't be called.
    enableTheory(THEORY_BV);
  }

  if(*p != '\0') {
    stringstream err;
    err << "LogicInfo::setLogicString(): ";
    if(p == logicString) {
      err << "cannot parse logic string: " << logicString;
    } else {
      err << "junk (\"" << p << "\") at end of logic string: " << logicString;
    }
    // The strings logicString and p are user-provided and
    // may include format specifiers (e.g. "QF_LIA%s").
    // Do not use unsafe macros/functions such as IllegalArgument.
    throw cvc5::internal::Exception(err.str().c_str());
  }

  // ensure a getLogic() returns the same thing as was set
  d_logicString = logicString;
}

void LogicInfo::enableEverything(bool enableHigherOrder)
{
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  *this = LogicInfo();
  this->d_higherOrder = enableHigherOrder;
}

void LogicInfo::disableEverything() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  *this = LogicInfo("");
}

void LogicInfo::enableTheory(theory::TheoryId theory) {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  if(!d_theories[theory]) {
    if(isTrueTheory(theory)) {
      ++d_sharingTheories;
    }
    d_logicString = "";
    d_theories[theory] = true;
  }
}

void LogicInfo::disableTheory(theory::TheoryId theory) {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  if(d_theories[theory]) {
    if(isTrueTheory(theory)) {
      Assert(d_sharingTheories > 0);
      --d_sharingTheories;
    }
    if(theory == THEORY_BUILTIN ||
       theory == THEORY_BOOL) {
      return;
    }
    d_logicString = "";
    d_theories[theory] = false;
  }
}

void LogicInfo::enableSygus()
{
  enableQuantifiers();
  enableTheory(THEORY_UF);
  enableTheory(THEORY_DATATYPES);
  enableIntegers();
}

void LogicInfo::enableSeparationLogic()
{
  enableTheory(THEORY_SEP);
  enableTheory(THEORY_UF);
  enableTheory(THEORY_SETS);
}

void LogicInfo::enableIntegers() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  enableTheory(THEORY_ARITH);
  d_integers = true;
}

void LogicInfo::disableIntegers() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_integers = false;
  if(!d_reals) {
    disableTheory(THEORY_ARITH);
  }
}

void LogicInfo::enableReals() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  enableTheory(THEORY_ARITH);
  d_reals = true;
}

void LogicInfo::disableReals() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_reals = false;
  if(!d_integers) {
    disableTheory(THEORY_ARITH);
  }
}

void LogicInfo::arithTranscendentals()
{
  PrettyCheckArgument(
      !d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_transcendentals = true;
  if (!d_reals)
  {
    enableReals();
  }
  if (d_linear)
  {
    arithNonLinear();
  }
}

void LogicInfo::arithOnlyDifference() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_linear = true;
  d_differenceLogic = true;
  d_transcendentals = false;
}

void LogicInfo::arithOnlyLinear() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_linear = true;
  d_differenceLogic = false;
  d_transcendentals = false;
}

void LogicInfo::arithNonLinear() {
  PrettyCheckArgument(!d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_linear = false;
  d_differenceLogic = false;
}

void LogicInfo::enableCardinalityConstraints()
{
  PrettyCheckArgument(
      !d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_cardinalityConstraints = true;
}

void LogicInfo::disableCardinalityConstraints()
{
  PrettyCheckArgument(
      !d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_cardinalityConstraints = false;
}

void LogicInfo::enableHigherOrder()
{
  PrettyCheckArgument(
      !d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_higherOrder = true;
}

void LogicInfo::disableHigherOrder()
{
  PrettyCheckArgument(
      !d_locked, *this, "This LogicInfo is locked, and cannot be modified");
  d_logicString = "";
  d_higherOrder = false;
}

LogicInfo LogicInfo::getUnlockedCopy() const {
  if(d_locked) {
    LogicInfo info = *this;
    info.d_locked = false;
    return info;
  } else {
    return *this;
  }
}

std::ostream& operator<<(std::ostream& out, const LogicInfo& logic) {
  return out << logic.getLogicString();
}

}  // namespace cvc5::internal
