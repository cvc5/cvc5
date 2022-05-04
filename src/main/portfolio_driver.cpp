/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Christopher L. Conway, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 */
#include "main/portfolio_driver.h"

#if HAVE_SYS_WAIT_H
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

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

namespace cvc5::main {

bool ExecutionContext::solveContinuous(parser::Parser* parser,
                                       bool stopAtSetLogic)
{
  std::unique_ptr<cvc5::Command> cmd;
  bool interrupted = false;
  bool status = true;
  while (status)
  {
    if (interrupted)
    {
      solver().getDriverOptions().out() << cvc5::CommandInterrupted();
      d_executor->reset();
      break;
    }
    cmd.reset(parser->nextCommand());
    if (cmd == nullptr) break;

    status = d_executor->doCommand(cmd);
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
  return status;
}

std::vector<std::unique_ptr<cvc5::Command>> ExecutionContext::parseCommands(
    parser::Parser* parser)
{
  std::vector<std::unique_ptr<cvc5::Command>> res;
  while (true)
  {
    res.emplace_back(parser->nextCommand());
    if (!res.back()) break;
    if (dynamic_cast<cvc5::QuitCommand*>(res.back().get()) != nullptr)
    {
      break;
    }
  }
  return res;
}

bool ExecutionContext::solveCommands(
    std::vector<std::unique_ptr<cvc5::Command>>& cmds)
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
  return status;
}

#if HAVE_SYS_WAIT_H

namespace {

/**
 * Provides a convenient wrapper for POSIX pipes in the context of forking.
 * The implemented mechanism is using a pipe to buffer the (standard or error)
 * output of a child process and optionally copy it to the respective output of
 * the parent process.
 */
class Pipe
{
 public:
  /** Open a new pipe */
  void open()
  {
    if (pipe(d_pipe) == -1)
    {
      throw internal::Exception("Unable to open pipe for child process");
    }
  }
  /**
   * Redirects the given file descriptor fd into this pipe using dup2 and closes
   * both ends of the pipe. This method should be called within the child
   * process after forking to redirect standard out or error out into the pipe.
   */
  void dup(int fd)
  {
    while ((dup2(d_pipe[1], fd) == -1) && (errno == EINTR))
    {
    }
    close(d_pipe[0]);
    close(d_pipe[1]);
  }
  /**
   * Close the input of this pipe. This method should be called within the
   * parent process after forking.
   */
  void closeIn() { close(d_pipe[1]); }
  /**
   * Copy the content of the pipe into the given output stream. This method
   * should be called within the parent process after the child process has
   * terminated.
   */
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

/**
 * Manages running portfolio configurations until one has solved the input
 * problem. Depending on --portfolio-jobs runs multiple jobs in parallel.
 */
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

  bool run(PortfolioStrategy& strategy)
  {
    for (const auto& s : strategy.d_strategies)
    {
      d_jobs.emplace_back(Job{s});
    }

    // While there are jobs to be run or jobs still running
    while (d_nextJob < d_jobs.size() || d_running > 0)
    {
      // Check if any job was successful
      if (checkResults())
      {
        return true;
      }

      // While we can start jobs right now
      while (d_nextJob < d_jobs.size() && d_running < d_numJobs)
      {
        startNextJob();
      }

      if (d_running > 0)
      {
        int wstatus = 0;
        pid_t child = wait(&wstatus);
        if (checkResults(child, wstatus))
        {
          return true;
        }
      }
    }
    if (checkResults()) return true;

    return false;
  }

 private:
  void startNextJob()
  {
    Assert(d_nextJob < d_jobs.size());
    Job& job = d_jobs[d_nextJob];
    Trace("portfolio") << "Starting " << job.d_config << std::endl;

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
      job.d_errPipe.dup(STDERR_FILENO);
      job.d_outPipe.dup(STDOUT_FILENO);
      job.d_config.applyOptions(d_ctx.solver());
      // 0 = solved, 1 = not solved
      int rc = 1;
      if (d_ctx.solveCommands(d_commands))
      {
        Result res = d_ctx.d_executor->getResult();
        if (res.isSat() || res.isUnsat())
        {
          rc = 0;
        }
      }
      std::quick_exit(rc);
    }
    job.d_errPipe.closeIn();
    job.d_outPipe.closeIn();

    // Start the timeout process
    if (d_timeout > 0 && job.d_config.d_timeout > 0)
    {
      job.d_timeout = fork();
      if (job.d_timeout == 0)
      {
        auto duration = std::chrono::duration<double, std::milli>(
            job.d_config.d_timeout * d_timeout);
        std::this_thread::sleep_for(duration);
        kill(job.d_worker, SIGKILL);
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
   * If child and status are given, only the job with this particular worker is
   * considered and status is assumed to be the wstatus reported by waitpid.
   */
  bool checkResults(pid_t child = -1, int status = 0)
  {
    // check d_jobs for items there worker has terminated and timeout != -1
    for (auto& job : d_jobs)
    {
      // has not been started yet
      if (job.d_worker == -1) continue;
      // has already been analyzed
      if (job.d_timeout == -1) continue;
      if (child != -1 && job.d_worker != child) continue;

      int wstatus = 0;
      pid_t res = 0;
      if (child == -1)
      {
        res = waitpid(job.d_worker, &wstatus, WNOHANG);
        // has not terminated yet
        if (res == 0) continue;
        if (res == -1) continue;
      }
      else
      {
        res = child;
        wstatus = status;
      }
      // mark as analyzed
      Trace("portfolio") << "Finished " << job.d_config << std::endl;
      job.d_timeout = -1;
      --d_running;
      // check if exited normally
      if (WIFSIGNALED(wstatus))
      {
        continue;
      }
      if (WIFEXITED(wstatus))
      {
        if (WEXITSTATUS(wstatus) == 0)
        {
          Trace("portfolio") << "Successful!" << std::endl;
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

}  // namespace

#endif

bool PortfolioDriver::solve(std::unique_ptr<CommandExecutor>& executor)
{
  ExecutionContext ctx{executor.get()};
  Solver& solver = ctx.solver();
  bool use_portfolio = solver.getOption("use-portfolio") == "true";
  if (!use_portfolio)
  {
    return ctx.solveContinuous(d_parser, false);
  }
#if HAVE_SYS_WAIT_H
  ctx.solveContinuous(d_parser, true);

  if (!ctx.d_logic)
  {
    return ctx.solveContinuous(d_parser, false);
  }

  PortfolioStrategy strategy = getStrategy(*ctx.d_logic);
  if (strategy.d_strategies.size() == 0)
  {
    return ctx.solveContinuous(d_parser, false);
  }
  if (strategy.d_strategies.size() == 1)
  {
    strategy.d_strategies.front().applyOptions(solver);
    return ctx.solveContinuous(d_parser, false);
  }

  uint64_t total_timeout = ctx.solver().getOptionInfo("tlimit").uintValue();
  if (total_timeout == 0)
  {
    total_timeout = 1200;
  }

  PortfolioProcessPool pool(ctx, ctx.parseCommands(d_parser));

  return pool.run(strategy);
#else
  Warning() << "Can't run portfolio without <sys/wait.h>.";
  return ctx.solveContinuous(d_parser, false);
#endif
}

std::ostream& operator<<(std::ostream& os, const PortfolioConfig& config)
{
  for (const auto& o : config.d_options)
  {
    os << o.first << "=" << o.second << " ";
  }
  os << "timeout=" << config.d_timeout;
  return os;
}

PortfolioStrategy PortfolioDriver::getStrategy(const std::string& logic)
{
  PortfolioStrategy s;
  if (logic == "QF_LRA")
  {
    s.add(0.2)
        .set("miplib-trick")
        .set("miplib-trick-subs", "4")
        .set("use-approx")
        .set("lemmas-on-replay-failure")
        .set("replay-early-close-depth", "4")
        .set("replay-lemma-reject-cut", "128")
        .set("replay-reject-cut", "512")
        .set("unconstrained-simp")
        .set("use-soi");
    s.add()
        .set("restrict-pivots", "false")
        .set("use-soi")
        .set("new-prop")
        .set("unconstrained-simp");
  }
  else if (logic == "QF_LIA")
  {
    s.add()
        .set("miplib-trick")
        .set("miplib-trick-subs", "4")
        .set("use-approx")
        .set("lemmas-on-replay-failure")
        .set("replay-early-close-depth", "4")
        .set("replay-lemma-reject-cut", "128")
        .set("replay-reject-cut", "512")
        .set("unconstrained-simp")
        .set("use-soi")
        .set("pb-rewrites")
        .set("ite-simp")
        .set("simp-ite-compress");
  }
  else if (logic == "QF_NIA")
  {
    s.add(0.35).set("nl-ext-tplanes").set("decision", "justification");
    s.add(0.05).set("nl-ext-tplanes").set("decision", "internal");
    s.add(0.05).set("nl-ext-tplanes").set("decision", "justification-old");
    s.add(0.05).set("nl-ext-tplanes", "false").set("decision", "internal");
    s.add(0.05)
        .set("arith-brab", "false")
        .set("nl-ext-tplanes")
        .set("decision", "internal");
    s.add(0.25).set("solve-int-as-bv", "2").set("bitblast", "eager");
    s.add(0.25).set("solve-int-as-bv", "4").set("bitblast", "eager");
    s.add(0.25).set("solve-int-as-bv", "8").set("bitblast", "eager");
    s.add(0.25).set("solve-int-as-bv", "16").set("bitblast", "eager");
    s.add(0.5).set("solve-int-as-bv", "32").set("bitblast", "eager");
    s.add().set("nl-ext-tplanes").set("decision", "internal");
  }
  else if (logic == "QF_NRA")
  {
    s.add(0.5).set("decision", "justification");
    s.add(0.25)
        .set("decision", "internal")
        .set("nl-cov", "false")
        .set("nl-ext", "full")
        .set("nl-ext-tplanes");
    s.add().set("decision", "internal").set("nl-ext", "none");
  }
  return s;
}

}  // namespace cvc5::main
