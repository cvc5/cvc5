/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Daniel Larraz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An intermediary between the parser and the command executor, optionally using
 * predefined portfolio strategies.
 */

#ifndef CVC5__MAIN__PORTFOLIO_DRIVER_H
#define CVC5__MAIN__PORTFOLIO_DRIVER_H

#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>

#include <optional>

#include "base/check.h"
#include "main/command_executor.h"

namespace cvc5::main {

/**
 * Holds the command executor and provides a few convenience methods for parsing
 * and executing commands with the executor.
 */

class ExecutionContext
{
 public:
  /** The command executor used for solving */
  CommandExecutor* d_executor;
  /** The logic, if it has been set by a command */
  std::optional<std::string> d_logic;
  /* Whether a check-sat command has been read */
  bool d_hasReadCheckSat = false;
  /** The last stored declarations and named terms **/
  std::vector<cvc5::Sort> d_sorts;
  std::vector<cvc5::Term> d_terms;
  std::map<cvc5::Term, std::string> d_named_terms;

  /** Retrieve the solver object from the command executor */
  Solver& solver() { return *d_executor->getSolver(); }

  /**
   * Read commands from the parser and continuously execute them. If
   * stopAtSetLogic is true, stop when the logic has been set to some value.
   * If this happens, d_logic is set to the respective value.
   * If stopAtCheckSat is true, stop when the a check-sat command has been read.
   * If this happens, d_hasReadCheckSat is set to true.
   * Otherwise (if stopAtSetLogic is false or the logic is never set, or
   * stopAtCheckSat is false or a check-sat command is never read) all
   * commands are executed until a quit command is found or the whole input
   * has been parsed.
   * Returns true if the commands have been executed without being interrupted.
   */
  bool solveContinuous(parser::InputParser* parser,
                       bool stopAtSetLogic,
                       bool stopAtCheckSat = false);

  /**
   * Store the current declarations and named terms to be used by
   * continueAfterSolving().
   */
  void storeDeclarationsAndNamedTerms();

  /**
   * Read commands from the parser and continuously execute them.
   * If a (get-model) command is detected, the last stored declarations are
   * used. If a (get-unsat-core) command is detected, the last stored named
   * terms are used. Returns true if the commands were executed without
   * interruption.
   */
  bool continueAfterSolving(parser::InputParser* parser);

  /**
   * Execute a check-sat command.
   * @return true if the command was executed successfully.
   */
  bool runCheckSatCommand();

  /**
   * Execute a reset command.
   * @return true if the command was executed successfully.
   */
  bool runResetCommand();

  /**
   * Execute the given commands.
   * Returns true if the commands have been executed without being interrupted.
   */
  bool solveCommands(std::vector<cvc5::parser::Command>& cmds);

  /** Parse the remaining input from d_parser into a vector of commands */
  std::vector<cvc5::parser::Command> parseCommands(parser::InputParser* parser);

};

/**
 * Represents a single configuration within a portfolio strategy, consisting of
 * a set of command line options and a timeout (as part of a total timeout).
 */
struct PortfolioConfig
{
  /**
   * Set timeout as part of the total timeout. The given number should be at
   * most 1.
   */
  PortfolioConfig(double timeout = 0.0) : d_timeout(timeout)
  {
    Assert(timeout <= 1)
        << "The given timeout should be given as part of the total timeout";
  }
  /**
   * Set a command line option. While no formal restriction is imposed, they
   * are only set after parsing has already started. Thus, options that affect
   * how the parser behaves should not be specified here.
   * The value is optional and defaults to "true".
   */
  PortfolioConfig& set(const std::string& option,
                       const std::string& value = "true")
  {
    d_options.emplace_back(option, value);
    return *this;
  }
  /** Convenience function to set option to "false". */
  PortfolioConfig& unset(const std::string& option)
  {
    return set(option, "false");
  }

  /** Apply configured options to a solver object */
  void applyOptions(Solver& solver) const
  {
    for (const auto& o : d_options)
    {
      solver.setOption(o.first, o.second);
    }
  }
  /** To option string */
  std::string toOptionString() const;
  /** List of options as pair of name and value */
  std::vector<std::pair<std::string, std::string>> d_options;
  /** Timeout as part of the total timeout */
  double d_timeout = 0;
};
std::ostream& operator<<(std::ostream& os, const PortfolioConfig& config);

/**
 * Represents a portfolio strategy, consisting of a list of configurations.
 */
struct PortfolioStrategy
{
  /** Add a new configurations */
  PortfolioConfig& add(double timeout = 0)
  {
    d_strategies.emplace_back(timeout);
    return d_strategies.back();
  }

  std::vector<PortfolioConfig> d_strategies;
};

class PortfolioDriver
{
 public:
  PortfolioDriver(std::unique_ptr<parser::InputParser>& parser)
      : d_parser(parser.get())
  {
  }

  /**
   * Solve the input obtained from the parser using the given executor.
   * Internally runs the appropriate portfolio strategy if a logic is set.
   * Returns true if the input was executed without being interrupted.
   */
  bool solve(std::unique_ptr<CommandExecutor>& executor);

 private:
  PortfolioStrategy getStrategy(bool incremental_solving,
                                const std::string& logic);
  PortfolioStrategy getIncrementalStrategy(const std::string& logic);
  PortfolioStrategy getNonIncrementalStrategy(const std::string& logic);

  /** The parser we use to get the commands */
  parser::InputParser* d_parser;
};

}  // namespace cvc5::main

#endif /* CVC5__MAIN__PORTFOLIO_DRIVER_H */
