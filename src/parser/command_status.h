/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Command status utility
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__COMMAND_STATUS_H
#define CVC5__PARSER__COMMAND_STATUS_H

#include <iosfwd>
#include <sstream>
#include <string>
#include <vector>

#include <cvc5/cvc5_export.h>

namespace cvc5 {
namespace parser {

class Command;
class CommandStatus;
class SymbolManager;

std::ostream& operator<<(std::ostream&, const CommandStatus&) CVC5_EXPORT;
std::ostream& operator<<(std::ostream&, const CommandStatus*) CVC5_EXPORT;

class CVC5_EXPORT CommandStatus
{
 protected:
  // shouldn't construct a CommandStatus (use a derived class)
  CommandStatus() {}

 public:
  virtual ~CommandStatus() {}
  virtual void toStream(std::ostream& out) const = 0;
  virtual CommandStatus& clone() const = 0;
}; /* class CommandStatus */

class CVC5_EXPORT CommandSuccess : public CommandStatus
{
  static const CommandSuccess* s_instance;

 public:
  static const CommandSuccess* instance() { return s_instance; }
  void toStream(std::ostream& out) const override;
  CommandStatus& clone() const override
  {
    return const_cast<CommandSuccess&>(*this);
  }
}; /* class CommandSuccess */

class CVC5_EXPORT CommandInterrupted : public CommandStatus
{
  static const CommandInterrupted* s_instance;

 public:
  static const CommandInterrupted* instance() { return s_instance; }
  void toStream(std::ostream& out) const override;
  CommandStatus& clone() const override
  {
    return const_cast<CommandInterrupted&>(*this);
  }
}; /* class CommandInterrupted */

class CVC5_EXPORT CommandUnsupported : public CommandStatus
{
 public:
  void toStream(std::ostream& out) const override;
  CommandStatus& clone() const override
  {
    return *new CommandUnsupported(*this);
  }
}; /* class CommandSuccess */

class CVC5_EXPORT CommandFailure : public CommandStatus
{
 public:
  CommandFailure(const std::string& message) : d_message(message) {}
  void toStream(std::ostream& out) const override;
  CommandFailure& clone() const override { return *new CommandFailure(*this); }
  std::string getMessage() const { return d_message; }

 private:
  std::string d_message;
}; /* class CommandFailure */

/**
 * The execution of the command resulted in a non-fatal error and further
 * commands can be processed. This status is for example used when a user asks
 * for an unsat core in a place that is not immediately preceded by an
 * unsat/valid response.
 */
class CVC5_EXPORT CommandRecoverableFailure : public CommandStatus
{
  std::string d_message;

 public:
  CommandRecoverableFailure(std::string message) : d_message(message) {}
  void toStream(std::ostream& out) const override;
  CommandRecoverableFailure& clone() const override
  {
    return *new CommandRecoverableFailure(*this);
  }
  std::string getMessage() const { return d_message; }
}; /* class CommandRecoverableFailure */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__COMMAND_H */
