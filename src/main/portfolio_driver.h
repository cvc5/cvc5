/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An additional layer between commands and invoking them.
 */

#ifndef CVC5__MAIN__PORTFOLIO_DRIVER_H
#define CVC5__MAIN__PORTFOLIO_DRIVER_H

#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

#include <chrono>
#include <optional>
#include <thread>

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "base/exception.h"
#include "base/output.h"
#include "main/command_executor.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace cvc5 {
namespace main {

struct ExecutionContext
{
  CommandExecutor* d_executor;

  Solver& solver() { return *d_executor->getSolver(); }

  bool runCommands(std::vector<std::unique_ptr<cvc5::Command>>& cmds)
  {
    bool interrupted = false;
    bool status = true;
    auto it = cmds.begin();
    while (status && it != cmds.end())
    {
      if (interrupted)
      {
        solver().getDriverOptions().out() << cvc5::CommandInterrupted();
        d_executor->reset();
        break;
      }

      Command* cmd = it->get();

      status = d_executor->doCommand(cmd);
      if (cmd->interrupted() && status == 0)
      {
        interrupted = true;
        break;
      }

      if (dynamic_cast<cvc5::QuitCommand*>(cmd) != nullptr)
      {
        break;
      }
    }
    if (status)
    {
      Result res = d_executor->getResult();
      return res.isSat() || res.isUnsat();
    }
    else
    {
      return false;
    }
  }
};

class Pipe
{
 public:
  void open()
  {
    if (pipe(d_pipe) == -1)
    {
      throw internal::Exception("Unable to open pipe for child process");
    }
  }
  void dup(int fd)
  {
    while ((dup2(d_pipe[1], fd) == -1) && (errno == EINTR))
    {
    }
    close(d_pipe[0]);
    close(d_pipe[1]);
  }
  void closeIn() { close(d_pipe[1]); }
  void flushTo(std::ostream& os)
  {
    char buf[4096];
    while (true)
    {
      ssize_t cnt = read(d_pipe[0], buf, sizeof(buf));
      if (cnt == -1)
      {
        if (errno == EINTR)
        {
          continue;
        }
        else
        {
          throw internal::Exception("Unable to read from pipe");
        }
      }
      else if (cnt == 0)
      {
        break;
      }
      os.write(buf, cnt);
    }
  }

 private:
  int d_pipe[2];
};

struct PortfolioConfig
{
  PortfolioConfig& set(const std::string& option, const std::string& value)
  {
    d_options.emplace_back(option, value);
    return *this;
  }
  /**
   * Set timeout as part of the total timeout. The given number should be at
   * most 1.
   */
  PortfolioConfig& timeout(double timeout)
  {
    Assert(timeout <= 1)
        << "The given timeout should be given as part of the total timeout";
    d_timeout = timeout;
    return *this;
  }

  void applyOptions(Solver& solver) const
  {
    for (const auto& o : d_options)
    {
      solver.setOption(o.first, o.second);
    }
  }

  std::vector<std::pair<std::string, std::string>> d_options;
  double d_timeout;
};

struct PortfolioStrategy
{
  PortfolioConfig& add()
  {
    d_strategies.emplace_back();
    return d_strategies.back();
  }

  std::vector<PortfolioConfig> d_strategies;
};

class PortfolioProcessPool
{
  struct Job
  {
    PortfolioConfig d_config;
    pid_t d_worker = -1;
    pid_t d_timeout = -1;
    Pipe d_errPipe;
    Pipe d_outPipe;
  };

 public:
  PortfolioProcessPool(ExecutionContext& ctx,
                       std::vector<std::unique_ptr<cvc5::Command>>&& cmds)
      : d_ctx(ctx),
        d_commands(std::move(cmds)),
        d_numJobs(ctx.solver().getOptionInfo("portfolio-jobs").uintValue()),
        d_timeout(ctx.solver().getOptionInfo("tlimit").uintValue())
  {
  }

  int run(PortfolioStrategy& strategy)
  {
    Trace("portfolio") << "Initializing strategies" << std::endl;
    for (const auto& s : strategy.d_strategies)
    {
      d_jobs.emplace_back(Job{s});
    }

    // While there are jobs to be run or jobs still running
    while (d_nextJob < d_jobs.size() || d_running > 0)
    {
      Trace("portfolio") << "Looping" << std::endl;
      Trace("portfolio") << "running: " << d_running << ", next " << d_nextJob
                         << " / " << d_jobs.size() << std::endl;
      // Check if any job was successful
      if (checkResults())
      {
        Trace("portfolio") << "Got successful result" << std::endl;
        return 0;
      }

      // While we can start jobs right now
      while (d_nextJob < d_jobs.size() && d_running < d_numJobs)
      {
        Trace("portfolio") << "Start a job" << std::endl;
        startNextJob();
      }

      if (d_running > 0)
      {
        Trace("portfolio") << "Wait for something to happen" << std::endl;
        std::this_thread::sleep_for(std::chrono::duration<int>(1));
        wait(nullptr);
        Trace("portfolio") << "Something has happened" << std::endl;
        if (checkResults())
        {
          Trace("portfolio") << "Got successful result" << std::endl;
          return 0;
        }
      }
    }
    if (checkResults()) return 0;

    return 1;
  }

 private:
  void startNextJob()
  {
    std::cerr << "Starting new process from " << getpid() << std::endl;
    Assert(d_nextJob < d_jobs.size());
    Job& job = d_jobs[d_nextJob];

    // Set up pipes to capture output of worker
    job.d_errPipe.open();
    job.d_outPipe.open();
    // Start the worker process
    job.d_worker = fork();
    if (job.d_worker == -1)
    {
      throw internal::Exception("Unable to fork");
    }
    if (job.d_worker == 0)
    {
      std::cerr << "Starting worker " << getpid() << std::endl;
      // job.d_errPipe.dup(STDERR_FILENO);
      // job.d_outPipe.dup(STDOUT_FILENO);
      job.d_config.applyOptions(d_ctx.solver());
      std::cerr << "applied options " << std::endl;
      // 0 = solved, 1 = not solved
      int rc = d_ctx.runCommands(d_commands) ? 0 : 1;
      std::cerr << "worker returns " << rc << std::endl;
      std::quick_exit(rc);
    }
    job.d_errPipe.closeIn();
    job.d_outPipe.closeIn();

    // Start the timeout process
    if (d_timeout > 0)
    {
      job.d_timeout = fork();
      if (job.d_timeout == 0)
      {
        std::cerr << "Starting timeout " << getpid() << ", waiting for "
                  << job.d_config.d_timeout * d_timeout << std::endl;
        auto duration = std::chrono::duration<double, std::milli>(
            job.d_config.d_timeout * d_timeout);
        // std::cerr << "sleeping for " << duration << std::endl;
        std::this_thread::sleep_for(duration);
        std::cerr << "killing worker " << job.d_worker << std::endl;
        kill(job.d_worker, SIGKILL);
        std::cerr << "timeout returns 0" << std::endl;
        std::quick_exit(0);
      }
    }
    else
    {
      job.d_timeout = 0;
    }

    ++d_nextJob;
    ++d_running;
  }

  /**
   * Check whether some process terminated and solved the input. If so,
   * forward the child process output to the main out and return true.
   * Otherwise return false.
   */
  bool checkResults()
  {
    // check d_jobs for items there worker has terminated and timeout != -1
    for (auto& job : d_jobs)
    {
      // has not been started yet
      if (job.d_worker == -1) continue;
      // has already been analyzed
      if (job.d_timeout == -1) continue;

      int wstatus = 0;
      pid_t res = waitpid(job.d_worker, &wstatus, WNOHANG);
      // has not terminated yet
      if (res == 0) continue;
      Trace("portfolio") << "Job has terminated" << std::endl;
      --d_running;
      // check if exited normally
      if (WIFEXITED(wstatus))
      {
        // mark as analyzed
        job.d_timeout = -1;
        int returncode = WEXITSTATUS(wstatus);
        Trace("portfolio") << "Job has terminated with " << returncode
                           << std::endl;
        if (returncode == 0)
        {
          job.d_errPipe.flushTo(std::cerr);
          job.d_outPipe.flushTo(std::cout);
          return true;
        }
      }
    }
    return false;
  }

  ExecutionContext& d_ctx;
  std::vector<std::unique_ptr<cvc5::Command>> d_commands;
  /**
   * All jobs, consisting of the config the pid of the worker process, and
   * the pid is the timeout process (or zero if no timeout was necessary).
   * If the job has not been started yet, both pids are -1. If the job has
   * finished and the result has been inspected, the pid of the timeout
   * process is -1.
   */
  std::vector<Job> d_jobs;
  /** The id of the next job to be started within d_jobs */
  size_t d_nextJob = 0;
  /** The number of currently running jobs */
  size_t d_running = 0;
  const uint64_t d_numJobs;
  const uint64_t d_timeout;
};

class PortfolioDriver
{
 public:
  PortfolioDriver(std::unique_ptr<parser::Parser>& parser)
      : d_parser(parser.get())
  {
  }

  int execute(std::unique_ptr<CommandExecutor>& executor)
  {
    ExecutionContext ctx{executor.get()};
    Solver& solver = ctx.solver();
    bool use_portfolio = solver.getOption("use-portfolio") == "true";
    if (!use_portfolio)
    {
      return executeContinuous(ctx, false);
    }

    executeContinuous(ctx, true);

    if (!d_logic)
    {
      return executeContinuous(ctx, false);
    }

    PortfolioStrategy strategy = getStrategy(*d_logic);
    if (strategy.d_strategies.size() == 0)
    {
      return executeContinuous(ctx, false);
    }
    if (strategy.d_strategies.size() == 1)
    {
      strategy.d_strategies.front().applyOptions(solver);
      return executeContinuous(ctx, false);
    }

    uint64_t total_timeout = ctx.solver().getOptionInfo("tlimit").uintValue();
    if (total_timeout == 0)
    {
      total_timeout = 1200;
    }

    PortfolioProcessPool pool(ctx, parseIntoVector(ctx));

    return pool.run(strategy);
  }

 private:
  PortfolioStrategy getStrategy(const std::string& logic);

  int executeContinuous(ExecutionContext& ctx, bool stopAtSetLogic = false)
  {
    std::unique_ptr<cvc5::Command> cmd;
    bool interrupted = false;
    bool status = true;
    while (status)
    {
      if (interrupted)
      {
        ctx.solver().getDriverOptions().out() << cvc5::CommandInterrupted();
        ctx.d_executor->reset();
        break;
      }
      cmd.reset(d_parser->nextCommand());
      if (cmd == nullptr) break;

      status = ctx.d_executor->doCommand(cmd);
      if (cmd->interrupted() && status == 0)
      {
        interrupted = true;
        break;
      }

      if (dynamic_cast<cvc5::QuitCommand*>(cmd.get()) != nullptr)
      {
        break;
      }
      if (stopAtSetLogic)
      {
        auto* slc = dynamic_cast<cvc5::SetBenchmarkLogicCommand*>(cmd.get());
        if (slc != nullptr)
        {
          d_logic = slc->getLogic();
          break;
        }
      }
    }
    return status ? 0 : 1;
  }

  /** Parse the remaining input from d_parser into a vector of commands */
  std::vector<std::unique_ptr<cvc5::Command>> parseIntoVector();

  /** The logic, if it has been set by a command */
  std::optional<std::string> d_logic;
  /** The parser we use to get the commands */
  parser::Parser* d_parser;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__COMMAND_EXECUTOR_H */
