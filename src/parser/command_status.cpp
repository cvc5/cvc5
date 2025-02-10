/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of command objects.
 */

#include "parser/command_status.h"

#include "printer/printer.h"

using namespace std;

namespace cvc5::parser {

const CommandSuccess* CommandSuccess::s_instance = new CommandSuccess();
const CommandInterrupted* CommandInterrupted::s_instance =
    new CommandInterrupted();

std::ostream& operator<<(std::ostream& out, const CommandStatus& s)
{
  s.toStream(out);
  return out;
}

ostream& operator<<(ostream& out, const CommandStatus* s)
{
  if (s == NULL)
  {
    out << "null";
  }
  else
  {
    out << *s;
  }
  return out;
}

void CommandSuccess::toStream(std::ostream& out) const
{
  internal::Printer::getPrinter(out)->toStreamCmdSuccess(out);
}

void CommandInterrupted::toStream(std::ostream& out) const
{
  internal::Printer::getPrinter(out)->toStreamCmdInterrupted(out);
}

void CommandUnsupported::toStream(std::ostream& out) const
{
  internal::Printer::getPrinter(out)->toStreamCmdUnsupported(out);
}

void CommandFailure::toStream(std::ostream& out) const
{
  internal::Printer::getPrinter(out)->toStreamCmdFailure(out, d_message);
}

void CommandRecoverableFailure::toStream(std::ostream& out) const
{
  internal::Printer::getPrinter(out)->toStreamCmdRecoverableFailure(out,
                                                                    d_message);
}

}  // namespace cvc5::parser
