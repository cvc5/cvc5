/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/arith/linear/error_set.h"

#include "theory/arith/linear/constraint.h"
#include "util/statistics_registry.h"

using namespace std;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ErrorInformation::ErrorInformation()
    : d_variable(ARITHVAR_SENTINEL),
      d_violated(NullConstraint),
      d_sgn(0),
      d_relaxed(false),
      d_inFocus(false),
      d_handle(),
      d_amount(nullptr),
      d_metric(0)
{
  Trace("arith::error::mem")
      << "def constructor " << d_variable << " " << d_amount.get() << endl;
}

ErrorInformation::ErrorInformation(ArithVar var, ConstraintP vio, int sgn)
    : d_variable(var),
      d_violated(vio),
      d_sgn(sgn),
      d_relaxed(false),
      d_inFocus(false),
      d_handle(),
      d_amount(nullptr),
      d_metric(0)
{
  Assert(debugInitialized());
  Trace("arith::error::mem")
      << "constructor " << d_variable << " " << d_amount.get() << endl;
}


ErrorInformation::~ErrorInformation() {
  Assert(d_relaxed != true);
  if (d_amount != nullptr)
  {
    Trace("arith::error::mem") << d_amount.get() << endl;
    Trace("arith::error::mem")
        << "destroy " << d_variable << " " << d_amount.get() << endl;
    d_amount = nullptr;
  }
}

ErrorInformation::ErrorInformation(const ErrorInformation& ei)
  : d_variable(ei.d_variable)
  , d_violated(ei.d_violated)
  , d_sgn(ei.d_sgn)
  , d_relaxed(ei.d_relaxed)
  , d_inFocus(ei.d_inFocus)
  , d_handle(ei.d_handle)
  , d_metric(0)
{
  if (ei.d_amount == nullptr)
  {
    d_amount = nullptr;
  }
  else
  {
    d_amount = std::make_unique<DeltaRational>(*ei.d_amount);
  }
  Trace("arith::error::mem")
      << "copy const " << d_variable << " " << d_amount.get() << endl;
}

ErrorInformation& ErrorInformation::operator=(const ErrorInformation& ei){
  d_variable = ei.d_variable;
  d_violated = ei.d_violated;
  d_sgn = ei.d_sgn;
  d_relaxed = (ei.d_relaxed);
  d_inFocus = (ei.d_inFocus);
  d_handle = (ei.d_handle);
  d_metric = ei.d_metric;
  if (d_amount != nullptr && ei.d_amount != nullptr)
  {
    Trace("arith::error::mem")
        << "assignment assign " << d_variable << " " << d_amount.get() << endl;
    *d_amount = *ei.d_amount;
  }
  else if (ei.d_amount != nullptr)
  {
    d_amount = std::make_unique<DeltaRational>(*ei.d_amount);
    Trace("arith::error::mem")
        << "assignment alloc " << d_variable << " " << d_amount.get() << endl;
  }
  else if (d_amount != nullptr)
  {
    Trace("arith::error::mem")
        << "assignment release " << d_variable << " " << d_amount.get() << endl;
    d_amount = nullptr;
  }
  else
  {
    d_amount = nullptr;
  }
  return *this;
}

void ErrorInformation::reset(ConstraintP c, int sgn){
  Assert(!isRelaxed());
  Assert(c != NullConstraint);
  d_violated = c;
  d_sgn = sgn;

  if (d_amount != nullptr)
  {
    Trace("arith::error::mem")
        << "reset " << d_variable << " " << d_amount.get() << endl;
    d_amount = nullptr;
  }
}

void ErrorInformation::setAmount(const DeltaRational& am){
  if (d_amount == nullptr)
  {
    d_amount = std::make_unique<DeltaRational>();
    Trace("arith::error::mem")
        << "setAmount " << d_variable << " " << d_amount.get() << endl;
  }
  (*d_amount) = am;
}

ErrorSet::Statistics::Statistics(StatisticsRegistry& sr)
    : d_enqueues(sr.registerInt("theory::arith::pqueue::enqueues")),
      d_enqueuesCollection(
          sr.registerInt("theory::arith::pqueue::enqueuesCollection")),
      d_enqueuesDiffMode(
          sr.registerInt("theory::arith::pqueue::enqueuesDiffMode")),
      d_enqueuesVarOrderMode(
          sr.registerInt("theory::arith::pqueue::enqueuesVarOrderMode")),
      d_enqueuesCollectionDuplicates(sr.registerInt(
          "theory::arith::pqueue::enqueuesCollectionDuplicates")),
      d_enqueuesVarOrderModeDuplicates(sr.registerInt(
          "theory::arith::pqueue::enqueuesVarOrderModeDuplicates"))
{
}

ErrorSet::ErrorSet(StatisticsRegistry& sr,
                   ArithVariables& vars,
                   TableauSizes tabSizes,
                   BoundCountingLookup lookups)
    : d_variables(vars),
      d_errInfo(),
      d_selectionRule(options::ErrorSelectionRule::VAR_ORDER),
      d_focus(ComparatorPivotRule(this, d_selectionRule)),
      d_outOfFocus(),
      d_signals(),
      d_tableauSizes(tabSizes),
      d_boundLookup(lookups),
      d_statistics(sr)
{}

options::ErrorSelectionRule ErrorSet::getSelectionRule() const
{
  return d_selectionRule;
}

void ErrorSet::recomputeAmount(ErrorInformation& ei,
                               options::ErrorSelectionRule rule)
{
  switch(rule){
    case options::ErrorSelectionRule::MINIMUM_AMOUNT:
    case options::ErrorSelectionRule::MAXIMUM_AMOUNT:
      ei.setAmount(computeDiff(ei.getVariable()));
      break;
    case options::ErrorSelectionRule::SUM_METRIC:
      ei.setMetric(sumMetric(ei.getVariable()));
      break;
    case options::ErrorSelectionRule::VAR_ORDER:
      // do nothing
      break;
  }
}

void ErrorSet::setSelectionRule(options::ErrorSelectionRule rule)
{
  if(rule != getSelectionRule()){
    FocusSet into(ComparatorPivotRule(this, rule));
    FocusSet::const_iterator iter = d_focus.begin();
    FocusSet::const_iterator i_end = d_focus.end();
    for(; iter != i_end; ++iter){
      ArithVar v = *iter;
      ErrorInformation& ei = d_errInfo.get(v);
      if(ei.inFocus()){
        recomputeAmount(ei, rule);
        FocusSetHandle handle = into.push(v);
        ei.setHandle(handle);
      }
    }
    d_focus.swap(into);
    d_selectionRule = rule;
  }
  Assert(getSelectionRule() == rule);
}

ComparatorPivotRule::ComparatorPivotRule(const ErrorSet* es,
                                         options::ErrorSelectionRule r)
    : d_errorSet(es), d_rule(r)
{}

bool ComparatorPivotRule::operator()(ArithVar v, ArithVar u) const {
  switch(d_rule){
    case options::ErrorSelectionRule::VAR_ORDER:
      // This needs to be the reverse of the minVariableOrder
      return v > u;
    case options::ErrorSelectionRule::SUM_METRIC:
    {
      uint32_t v_metric = d_errorSet->getMetric(v);
      uint32_t u_metric = d_errorSet->getMetric(u);
      if(v_metric == u_metric){
        return v > u;
      }else{
        return v_metric > u_metric;
      }
    }
    case options::ErrorSelectionRule::MINIMUM_AMOUNT:
    {
      const DeltaRational& vamt = d_errorSet->getAmount(v);
      const DeltaRational& uamt = d_errorSet->getAmount(u);
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v > u;
      }else{
        return cmp > 0;
      }
    }
    case options::ErrorSelectionRule::MAXIMUM_AMOUNT:
    {
      const DeltaRational& vamt = d_errorSet->getAmount(v);
      const DeltaRational& uamt = d_errorSet->getAmount(u);
      int cmp = vamt.cmp(uamt);
      if(cmp == 0){
        return v > u;
      }else{
        return cmp < 0;
      }
    }
  }
  Unreachable();
}

void ErrorSet::update(ErrorInformation& ei){
  if(ei.inFocus()){

    switch(getSelectionRule()){
      case options::ErrorSelectionRule::MINIMUM_AMOUNT:
      case options::ErrorSelectionRule::MAXIMUM_AMOUNT:
        ei.setAmount(computeDiff(ei.getVariable()));
        d_focus.update(ei.getHandle(), ei.getVariable());
        break;
      case options::ErrorSelectionRule::SUM_METRIC:
        ei.setMetric(sumMetric(ei.getVariable()));
        d_focus.update(ei.getHandle(), ei.getVariable());
        break;
      case options::ErrorSelectionRule::VAR_ORDER:
        // do nothing
        break;
    }
  }
}

/** A variable becomes satisfied. */
void ErrorSet::transitionVariableOutOfError(ArithVar v) {
  Assert(!inconsistent(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(ei.debugInitialized());
  if(ei.isRelaxed()){
    ConstraintP viol = ei.getViolated();
    if(ei.sgn() > 0){
      d_variables.setLowerBoundConstraint(viol);
    }else{
      d_variables.setUpperBoundConstraint(viol);
    }
    Assert(!inconsistent(v));
    ei.setUnrelaxed();
  }
  if(ei.inFocus()){
    d_focus.erase(ei.getHandle());
    ei.setInFocus(false);
  }
  d_errInfo.remove(v);
}


void ErrorSet::transitionVariableIntoError(ArithVar v) {
  Assert(inconsistent(v));
  bool vilb = d_variables.cmpAssignmentLowerBound(v) < 0;
  int sgn = vilb ? 1 : -1;
  ConstraintP c = vilb ?
    d_variables.getLowerBoundConstraint(v) : d_variables.getUpperBoundConstraint(v);
  d_errInfo.set(v, ErrorInformation(v, c, sgn));
  ErrorInformation& ei = d_errInfo.get(v);

  switch(getSelectionRule()){
    case options::ErrorSelectionRule::MINIMUM_AMOUNT:
    case options::ErrorSelectionRule::MAXIMUM_AMOUNT:
      ei.setAmount(computeDiff(v));
      break;
    case options::ErrorSelectionRule::SUM_METRIC:
      ei.setMetric(sumMetric(ei.getVariable()));
      break;
    case options::ErrorSelectionRule::VAR_ORDER:
      // do nothing
      break;
  }
  ei.setInFocus(true);
  FocusSetHandle handle = d_focus.push(v);
  ei.setHandle(handle);
}

void ErrorSet::dropFromFocus(ArithVar v) {
  Assert(inError(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(ei.inFocus());
  d_focus.erase(ei.getHandle());
  ei.setInFocus(false);
  d_outOfFocus.push_back(v);
}

void ErrorSet::addBackIntoFocus(ArithVar v) {
  Assert(inError(v));
  ErrorInformation& ei = d_errInfo.get(v);
  Assert(!ei.inFocus());
  switch(getSelectionRule()){
    case options::ErrorSelectionRule::MINIMUM_AMOUNT:
    case options::ErrorSelectionRule::MAXIMUM_AMOUNT:
      ei.setAmount(computeDiff(v));
      break;
    case options::ErrorSelectionRule::SUM_METRIC:
      ei.setMetric(sumMetric(v));
      break;
    case options::ErrorSelectionRule::VAR_ORDER:
      // do nothing
      break;
  }

  ei.setInFocus(true);
  FocusSetHandle handle = d_focus.push(v);
  ei.setHandle(handle);
}

void ErrorSet::blur(){
  while(!d_outOfFocus.empty()){
    ArithVar v = d_outOfFocus.back();
    d_outOfFocus.pop_back();

    if(inError(v) && !inFocus(v)){
      addBackIntoFocus(v);
    }
  }
}



int ErrorSet::popSignal() {
  ArithVar back = d_signals.back();
  d_signals.pop_back();

  if(inError(back)){
    ErrorInformation& ei = d_errInfo.get(back);
    int prevSgn = ei.sgn();
    int focusSgn = ei.focusSgn();
    bool vilb = d_variables.cmpAssignmentLowerBound(back) < 0;
    bool viub = d_variables.cmpAssignmentUpperBound(back) > 0;
    if(vilb || viub){
      Assert(!vilb || !viub);
      int currSgn = vilb ? 1 : -1;
      if(currSgn != prevSgn){
        ConstraintP curr = vilb ?  d_variables.getLowerBoundConstraint(back)
          : d_variables.getUpperBoundConstraint(back);
        ei.reset(curr, currSgn);
      }
      update(ei);
    }else{
      transitionVariableOutOfError(back);
    }
    return focusSgn;
  }else if(inconsistent(back)){
    transitionVariableIntoError(back);
  }
  return 0;
}

void ErrorSet::clear(){
  // Nothing should be relaxed!
  d_signals.clear();
  d_errInfo.purge();
  d_focus.clear();
}

void ErrorSet::clearFocus(){
  for(ErrorSet::focus_iterator i =focusBegin(), i_end = focusEnd(); i != i_end; ++i){
    ArithVar f = *i;
    ErrorInformation& fei = d_errInfo.get(f);
    fei.setInFocus(false);
    d_outOfFocus.push_back(f);
  }
  d_focus.clear();
}

void ErrorSet::reduceToSignals(){
  for(error_iterator ei=errorBegin(), ei_end=errorEnd(); ei != ei_end; ++ei){
    ArithVar curr = *ei;
    signalVariable(curr);
  }

  d_errInfo.purge();
  d_focus.clear();
  d_outOfFocus.clear();
}

DeltaRational ErrorSet::computeDiff(ArithVar v) const{
  Assert(inconsistent(v));
  const DeltaRational& beta = d_variables.getAssignment(v);
  DeltaRational diff = d_variables.cmpAssignmentLowerBound(v) < 0 ?
    d_variables.getLowerBound(v) - beta:
    beta - d_variables.getUpperBound(v);

  Assert(diff.sgn() > 0);
  return diff;
}

void ErrorSet::debugPrint(std::ostream& out) const {
  out << "error set debugprint" << endl;
  for(error_iterator i = errorBegin(), i_end = errorEnd();
      i != i_end; ++i){
    ArithVar e = *i;
    const ErrorInformation& ei = d_errInfo[e];
    ei.print(out);
    out << "  ";
    d_variables.printModel(e, out);
    out << endl;
  }
  out << "focus ";
  for(focus_iterator i = focusBegin(), i_end = focusEnd();
      i != i_end; ++i){
    out << *i << " ";
  }
  out << ";" << endl;
}

void ErrorSet::focusDownToJust(ArithVar v) {
  clearFocus();

  ErrorInformation& vei = d_errInfo.get(v);
  vei.setInFocus(true);
  FocusSetHandle handle = d_focus.push(v);
  vei.setHandle(handle);
}

void ErrorSet::pushErrorInto(ArithVarVec& vec) const{
  for(error_iterator i = errorBegin(), e = errorEnd(); i != e; ++i ){
    vec.push_back(*i);
  }
}

void ErrorSet::pushFocusInto(ArithVarVec& vec) const{
  for(focus_iterator i = focusBegin(), e = focusEnd(); i != e; ++i ){
    vec.push_back(*i);
  }
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
