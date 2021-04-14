#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Makai Mann, Mudathir Mohamed, Aina Niemetz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##

"""
This script implements KindsParser which
parses the header file CVC4/src/api/cpp/cvc5_kind.h

The script is aware of the '#if 0' pattern and will ignore
kinds declared between '#if 0' and '#endif'. It can also
handle nested '#if 0' pairs.
"""

from collections import OrderedDict


##################### Useful Constants ################
OCB = '{'
CCB = '}'
SC = ';'
EQ = '='
C = ','
US = '_'
NL = '\n'

# Enum Declarations
ENUM_START = 'enum CVC4_EXPORT Kind'
ENUM_END = CCB + SC

# Comments and Macro Tokens
COMMENT = '//'
BLOCK_COMMENT_BEGIN = '/*'
BLOCK_COMMENT_END = '*/'
MACRO_BLOCK_BEGIN = '#if 0'
MACRO_BLOCK_END = '#endif'

# Format Kind Names
# special cases for format_name
_IS = '_IS'
# replacements after some preprocessing
replacements = {
    'Bitvector': 'BV',
    'Floatingpoint': 'FP'
}


class KindsParser:
    tokenmap = {
        BLOCK_COMMENT_BEGIN: BLOCK_COMMENT_END,
        MACRO_BLOCK_BEGIN: MACRO_BLOCK_END
    }

    def __init__(self):
        self.kinds = OrderedDict()
        self.endtoken = None
        self.endtoken_stack = []
        self.in_kinds = False

    def format_name(self, name):
        '''
        In the Python API, each Kind name is reformatted for easier use

        The naming scheme is:
           1. capitalize the first letter of each word (delimited by underscores)
           2. make the rest of the letters lowercase
           3. replace Floatingpoint with FP
           4. replace Bitvector with BV

        There is one exception:
           FLOATINGPOINT_ISNAN  --> FPIsNan

        For every "_IS" in the name, there's an underscore added before step 1,
           so that the word after "Is" is capitalized

        Examples:
           BITVECTOR_PLUS      -->  BVPlus
           APPLY_SELECTOR      -->  ApplySelector
           FLOATINGPOINT_ISNAN -->  FPIsNan
           SETMINUS            -->  Setminus

        See the generated .pxi file for an explicit mapping
        '''
        name = name.replace(_IS, _IS + US)
        words = [w.capitalize() for w in name.lower().split(US)]
        name = "".join(words)

        for og, new in replacements.items():
            name = name.replace(og, new)

        return name

    def ignore_block(self, line):
        '''
        Returns a boolean telling self.parse whether to ignore a line or not.
        It also updates all the necessary state to track comments and macro
        blocks
        '''

        # check if entering block comment or macro block
        for token in self.tokenmap:
            if token in line:
                if self.tokenmap[token] not in line:
                    if self.endtoken is not None:
                        self.endtoken_stack.append(self.endtoken)
                    self.endtoken = self.tokenmap[token]
                return True

        # check if currently in block comment or macro block
        if self.endtoken is not None:
            # check if reached the end of block comment or macro block
            if self.endtoken in line:
                if self.endtoken_stack:
                    self.endtoken = self.endtoken_stack.pop()
                else:
                    self.endtoken = None
            return True

        return False

    def parse(self, filename):
        f = open(filename, "r")

        for line in f.read().split(NL):
            line = line.strip()
            if COMMENT in line:
                line = line[:line.find(COMMENT)]
            if not line:
                continue

            if self.ignore_block(line):
                continue

            if ENUM_END in line:
                self.in_kinds = False
                break
            elif self.in_kinds:
                if line == OCB:
                    continue
                if EQ in line:
                    line = line[:line.find(EQ)].strip()
                elif C in line:
                    line = line[:line.find(C)].strip()
                self.kinds[line] = self.format_name(line)
            elif ENUM_START in line:
                self.in_kinds = True
                continue
        f.close()

