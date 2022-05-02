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

namespace cvc5::main {

PortfolioStrategy PortfolioDriver::getStrategy(const std::string& logic)
{
	PortfolioStrategy s;
	if (logic == "QF_NRA")
	{
		s.add().set("decision", "justification").timeout(0.5);
		s.add().set("decision", "internal").set("nl-cad", "false").set("nl-ext", "full").set("nl-ext-tplanes", "true").timeout(0.25);
		s.add().set("decision", "internal").set("nl-ext", "none");
	}
	return s;
}

}  // namespace cvc5::internal
