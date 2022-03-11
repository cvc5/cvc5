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
parses the header file cvc5/src/api/cpp/cvc5_kind.h

The script is aware of the '#if 0' pattern and will ignore
kinds declared between '#if 0' and '#endif'. It can also
handle nested '#if 0' pairs.
"""

from collections import OrderedDict
import textwrap

##################### Useful Constants ################
OCB = '{'
CCB = '}'
SC = ';'
EQ = '='
C = ','
US = '_'
NL = '\n'

# Expected C++ Enum Declarations
ENUM_START = 'enum Kind'
ENUM_END = CCB + SC

# Comments and Macro Tokens
COMMENT = '//'
BLOCK_COMMENT_BEGIN = '/*'
BLOCK_COMMENT_END = '*/'
MACRO_BLOCK_BEGIN = '#if 0'
MACRO_BLOCK_END = '#endif'


class KindsParser:
    tokenmap = {
        BLOCK_COMMENT_BEGIN: BLOCK_COMMENT_END,
        MACRO_BLOCK_BEGIN: MACRO_BLOCK_END
    }

    def __init__(self):
        # dictionary from shortened name to documentation comment
        self.kinds_doc = OrderedDict()
        # the end token for the current type of block
        # none if not in a block comment or macro
        self.endtoken = None
        # stack of end tokens
        self.endtoken_stack = []
        # boolean that is true when in the kinds enum
        self.in_kinds = False
        # latest block comment - used for kinds documentation
        self.latest_block_comment = ""

    def get_comment(self, kind_name):
        '''
        Look up a documentation comment for a Kind by C++ name
        '''
        return self.kinds_doc[kind_name]

    def format_comment(self, comment):
        '''
        Removes the C++ syntax for block comments and returns just the text.
        '''
        assert comment[:2]  == '/*', \
            "Expecting to start with /* but got \"{}\"".format(comment[:2])
        assert comment[-2:] == '*/', \
            "Expecting to end with */ but got \"{}\"".format(comment[-2:])
        comment = comment[2:-2].strip('*\n')  # /** ... */ -> ...
        comment = textwrap.dedent(comment)  # remove indentation
        comment = comment.replace('\n*', '\n')  # remove leading "*""
        comment = textwrap.dedent(comment)  # remove indentation
        comment = comment.replace('\\rst', '').replace('\\endrst', '')
        comment = comment.strip()  # remove leading and trailing spaces
        return comment

    def ignore_block(self, line):
        '''
        Returns a boolean telling self.parse whether to ignore a line or not.
        It also updates all the necessary state to track comments and macro
        blocks
        '''

        # check if entering block comment or macro block
        for token in self.tokenmap:
            if token in line:
                # if entering block comment, override previous block comment
                if token == BLOCK_COMMENT_BEGIN:
                    self.latest_block_comment = line
                if self.tokenmap[token] not in line:
                    if self.endtoken is not None:
                        self.endtoken_stack.append(self.endtoken)
                    self.endtoken = self.tokenmap[token]
                return True

        # check if currently in block comment or macro block
        if self.endtoken is not None:
            # if in block comment, record the line
            if self.endtoken == BLOCK_COMMENT_END:
                self.latest_block_comment += "\n" + line
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
                name = line
                if EQ in line:
                    name = line[:line.find(EQ)].strip()
                elif C in line:
                    name = line[:line.find(C)].strip()
                fmt_comment = self.format_comment(self.latest_block_comment)
                self.kinds_doc[name] = fmt_comment
            elif ENUM_START in line:
                self.in_kinds = True
                continue
        f.close()
