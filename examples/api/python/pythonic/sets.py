###############################################################################
# Top contributors (to current version):
#   Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of reasoning about sets with cvc5.
##
from cvc5.pythonic import *

if __name__ == "__main__":
    A, B, C = [Set(name, IntSort()) for name in "ABC"]

    # holds
    prove((A | B) & C == (A & C) | (B & C))

    # holds
    prove(IsSubset(EmptySet(IntSort()), A))

    # x must be 2.
    x = Int("x")
    solve(
        IsMember(
            x,
            (Singleton(IntVal(1)) | Singleton(IntVal(2)))
            & (Singleton(IntVal(2)) | Singleton(IntVal(3))),
        )
    )
