###############################################################################
# Top contributors (to current version):
#   Haniel Barbosa
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Data structure for DSL rules
##

class Rule:
    def __init__(self, name, bvars, cond, lhs, rhs, is_fixed_point, rhs_context):
        self.name = name
        self.bvars = bvars
        self.cond = cond
        self.lhs = lhs
        self.rhs = rhs
        self.is_fixed_point = is_fixed_point
        self.rhs_context = rhs_context

    def get_enum(self):
        """
            Get the rule name and convert it to be a member of an enumeration of the DSL rules.

            :return: The name of the rule converted to an Enum member
        """
        return self.name.replace('-', '_').upper()

    def __repr__(self):
        bvars_str = ' '.join(str(bvar) for bvar in self.bvars)
        rhs_context_str = f' {self.rhs_context}' if self.rhs_context else ''
        return f"(define-rule {self.name} ({bvars_str}) {self.lhs} {self.rhs}{rhs_context_str})"
