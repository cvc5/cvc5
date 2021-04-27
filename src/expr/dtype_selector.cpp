/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a datatype selector.
 */

#include "expr/dtype_selector.h"

#include "options/set_language.h"

using namespace cvc5::kind;

namespace cvc5 {

DTypeSelector::DTypeSelector(std::string name, Node selector, Node updater)
    : d_name(name), d_selector(selector), d_updater(updater), d_resolved(false)
{
  Assert(name != "");
}

const std::string& DTypeSelector::getName() const { return d_name; }

Node DTypeSelector::getSelector() const
{
  Assert(d_resolved);
  return d_selector;
}
Node DTypeSelector::getUpdater() const
{
  Assert(d_resolved);
  return d_updater;
}

Node DTypeSelector::getConstructor() const
{
  Assert(d_resolved);
  return d_constructor;
}

TypeNode DTypeSelector::getType() const { return d_selector.getType(); }

TypeNode DTypeSelector::getRangeType() const
{
  return getType().getRangeType();
}

bool DTypeSelector::isResolved() const { return d_resolved; }

void DTypeSelector::toStream(std::ostream& out) const
{
  out << getName() << ": ";
  TypeNode t;
  if (d_resolved)
  {
    // don't try to print the range type of null, instead we print null itself.
    if (!getType().isNull())
    {
      t = getRangeType();
    }
  }
  else if (d_selector.isNull())
  {
    std::string typeName = d_name.substr(d_name.find('\0') + 1);
    out << ((typeName == "") ? "[self]" : typeName);
    return;
  }
  else
  {
    out << "unresolved";
    return;
  }
  out << t;
}

std::ostream& operator<<(std::ostream& os, const DTypeSelector& arg)
{
  // can only output datatypes in the cvc5 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC);
  arg.toStream(os);
  return os;
}

}  // namespace cvc5
