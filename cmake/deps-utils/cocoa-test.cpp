/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Checks whether CoCoA has been patched.
 */
#include <iostream>
#include <CoCoA/TmpGPoly.H>

int main()
{
    std::cout << "CoCoA::handlersEnabled = ";
    std::cout << CoCoA::handlersEnabled << std::endl;
    return 0;
}