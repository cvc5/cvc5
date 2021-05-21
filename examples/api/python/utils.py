#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Utility Methods, translated from examples/api/utils.h
##

import pycvc5
from pycvc5 import kinds

# Get the string version of define-fun command.
# @param f the function to print
# @param params the function parameters
# @param body the function body
# @return a string version of define-fun


def define_fun_to_string(f, params, body):
    sort = f.getSort()
    if sort.isFunction():
        sort = f.getSort().getFunctionCodomainSort()
    result = ""
    result += "(define-fun " + str(f) + " ("
    for i in range(0, len(params)):
        if i > 0:
            result += " "
        else:
            result += "(" + str(params[i]) + " " + str(params[i].getSort()) + ")"
    result += ") " + str(sort) + " " + str(body) + ")"
    return result


# Print solutions for synthesis conjecture to the standard output stream.
# @param terms the terms for which the synthesis solutions were retrieved
# @param sols the synthesis solutions of the given terms


def print_synth_solutions(terms, sols):
    result = ""
    for i in range(0, len(terms)):
        params = []
        if sols[i].getKind() == kinds.Lambda:
            params += sols[i][0]
            body = sols[i][1]
        result += "  " + define_fun_to_string(terms[i], params, body) + "\n"
    print(result)
