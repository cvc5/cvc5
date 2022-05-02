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

#include <optional>

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "main/command_executor.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace cvc5 {
namespace main {

struct ExecutionContext
{
	CommandExecutor* d_executor;
	cvc5::parser::Parser* d_parser;

	Solver& solver() {
		return *d_executor->getSolver();
	}
};

struct PortfolioConfig
{
	PortfolioConfig& set(const std::string& option, const std::string& value)
	{
		d_options.emplace_back(option, value);
		return *this;
	}
	/**
	 * Set timeout as part of the total timeout. The given number should be at most 1.
	 */
	PortfolioConfig& timeout(double timeout)
	{
		Assert(timeout <= 1) << "The given timeout should be given as part of the total timeout";
		d_timeout = timeout;
		return *this;
	}

	void applyOptions(Solver& solver) const
	{
		for (const auto& o: d_options)
		{
			solver.setOption(o.first, o.second);
		}
	}
	
	std::vector<std::pair<std::string,std::string>> d_options;
	uint64_t d_timeout;
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


class PortfolioDriver
{
	public:
		void execute(ExecutionContext& ctx)
		{
			Solver& solver = ctx.solver();
			bool use_portfolio = solver.getOption("use-portfolio") == "true";
			if (!use_portfolio)
			{
				executeContinuous(ctx, false);
				return;
			}
			
			executeContinuous(ctx, true);

			if (!d_logic)
			{
				executeContinuous(ctx, false);
				return;
			}
			
			PortfolioStrategy strategy = getStrategy(*d_logic);
			if (strategy.d_strategies.size() == 0)
			{
				executeContinuous(ctx, false);
				return;
			}
			if (strategy.d_strategies.size() == 1)
			{
				strategy.d_strategies.front().applyOptions(solver);
				executeContinuous(ctx, false);
				return;
			}

			uint64_t total_timeout = ctx.solver().getOptionInfo("tlimit").uintValue();
			if (total_timeout == 0)
			{
				total_timeout = 1200;
			}

			auto cmds = parseIntoVector(ctx);
			for (const auto& s: strategy.d_strategies)
			{
				// fork
				// set timeout: s.d_timeout * total_timeout
				s.applyOptions(solver);
				execute(ctx, cmds);
			}
		}
	private:
		PortfolioStrategy getStrategy(const std::string& logic);

		void executeContinuous(ExecutionContext& ctx, bool stopAtSetLogic = false)
		{
    		std::unique_ptr<cvc5::Command> cmd;
			bool interrupted = false;
			bool status = false;
			while (status)
			{
				if (interrupted) {
					ctx.solver().getDriverOptions().out() << cvc5::CommandInterrupted();
					ctx.d_executor->reset();
					break;
				}
				cmd.reset(ctx.d_parser->nextCommand());
				if (cmd == nullptr) break;

				status = ctx.d_executor->doCommand(cmd);
				if (cmd->interrupted() && status == 0) {
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
		}

		std::vector<std::unique_ptr<cvc5::Command>> parseIntoVector(ExecutionContext& ctx)
		{
			std::vector<std::unique_ptr<cvc5::Command>> res;
			while (true)
			{
				res.emplace_back(ctx.d_parser->nextCommand());
				if (!res.back()) break;
				if (dynamic_cast<cvc5::QuitCommand*>(res.back().get()) != nullptr)
				{
					break;
				}
			}
			return res;
		}

		void execute(ExecutionContext& ctx, std::vector<std::unique_ptr<cvc5::Command>>& cmds)
		{
    		bool interrupted = false;
			bool status = false;
			auto it = cmds.begin();
			while (status && it != cmds.end())
			{
				if (interrupted) {
					ctx.solver().getDriverOptions().out() << cvc5::CommandInterrupted();
					ctx.d_executor->reset();
					break;
				}

				Command* cmd = it->get();

				status = ctx.d_executor->doCommand(cmd);
				if (cmd->interrupted() && status == 0) {
					interrupted = true;
					break;
				}

				if (dynamic_cast<cvc5::QuitCommand*>(cmd) != nullptr)
				{
					break;
				}
			}
		}

		std::optional<std::string> d_logic;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__MAIN__COMMAND_EXECUTOR_H */
