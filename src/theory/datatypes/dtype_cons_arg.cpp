/*********************                                                        */
/*! \file dtype.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a datatype definition
 **/

#include "theory/datatypes/dtype_cons_arg.h"

#include "options/set_language.h"

using namespace CVC4::kind;

namespace CVC4 {

DTypeConstructorArg::DTypeConstructorArg(std::string name, Node selector)
    : d_name(name), d_selector(selector), d_resolved(false)
{
  Assert(name != "");
}

std::string DTypeConstructorArg::getName() const { return d_name; }

Node DTypeConstructorArg::getSelector() const
{
  Assert(d_resolved);
  return d_selector;
}

Node DTypeConstructorArg::getConstructor() const
{
  Assert(d_resolved);
  return d_constructor;
}

TypeNode DTypeConstructorArg::getType() const
{
  return getSelector().getType();
}

TypeNode DTypeConstructorArg::getRangeType() const
{
  return getType().getRangeType();
}

bool DTypeConstructorArg::isResolved() const { return d_resolved; }

void DTypeConstructorArg::toStream(std::ostream& out) const
{
  out << getName() << ": ";
  TypeNode t;
  if (d_resolved)
  {
    t = getRangeType();
  }
  else if (d_selector.isNull())
  {
    std::string typeName = d_name.substr(d_name.find('\0') + 1);
    out << ((typeName == "") ? "[self]" : typeName);
    return;
  }
  else
  {
    t = d_selector.getType();
  }
  out << t;
}

std::ostream& operator<<(std::ostream& os, const DTypeConstructorArg& arg)
{
  // can only output datatypes in the CVC4 native language
  language::SetLanguage::Scope ls(os, language::output::LANG_CVC4);
  arg.toStream(os);
  return os;
}

}  // namespace CVC4
