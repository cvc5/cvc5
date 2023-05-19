#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Andres Noetzli, Makai Mann, Mudathir Mohamed
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##
"""
This script implements EnumParser which parses a header file that defines
enums.

The script is aware of the '#if 0' pattern and will ignore enum values declared
between '#if 0' and '#endif'. It can also handle nested '#if 0' pairs.
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

NAMESPACE_START = 'namespace'

# Expected C++ Enum Declarations
ENUM_START = 'enum'
ENUM_END = CCB + SC

# Comments and Macro Tokens
COMMENT = '//'
BLOCK_COMMENT_BEGIN = '/*'
BLOCK_COMMENT_END = '*/'
MACRO_BLOCK_BEGIN = '#if 0'
MACRO_BLOCK_END = '#endif'


class CppNamespace:

    def __init__(self, name):
        # The name of the namespace
        self.name = name
        # The enums in this namespace
        self.enums = []


class CppEnum:

    def __init__(self, name):
        # The name of the enum
        self.name = name
        # dictionary from C++ value name to shortened name
        self.enumerators = OrderedDict()
        # dictionary from shortened name to documentation comment
        self.enumerators_doc = OrderedDict()


class EnumParser:
    tokenmap = {
        BLOCK_COMMENT_BEGIN: BLOCK_COMMENT_END,
        MACRO_BLOCK_BEGIN: MACRO_BLOCK_END
    }

    def __init__(self):
        # the namespaces that have been parsed
        self.namespaces = []
        # the end token for the current type of block
        # none if not in a block comment or macro
        self.endtoken = None
        # stack of end tokens
        self.endtoken_stack = []
        # boolean that is true when in an enum
        self.in_enum = False
        # latest block comment - used for enums documentation
        self.latest_block_comment = ""
        # The value of the last enumerator
        self.last_value = -1

    def get_current_namespace(self):
        '''
        Returns the namespace that is currently being parsed
        '''
        return self.namespaces[-1]

    def get_current_enum(self):
        '''
        Returns the enum that is currently being parsed
        '''
        return self.get_current_namespace().enums[-1]

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
        with open(filename, "r") as f:
            for line in f:
                line = line.strip()
                if COMMENT in line:
                    line = line[:line.find(COMMENT)]
                if not line:
                    continue

                if self.ignore_block(line):
                    continue

                if ENUM_END in line:
                    self.in_enum = False
                    self.last_value = -1
                    continue
                elif self.in_enum:
                    if line == OCB:
                        continue
                    name = None
                    value = None
                    if EQ in line:
                        (name, remainder) = line.split(EQ)
                        name = name.strip()
                        if C in remainder:
                            value = int(remainder[:remainder.find(C)].strip())
                        else:
                            value = int(remainder)
                    elif C in line:
                        name = line[:line.find(C)].strip()
                    else:
                        name = line

                    if not value:
                        value = self.last_value + 1
                    self.last_value = value

                    enum = self.get_current_enum()
                    enum.enumerators[name] = value
                    fmt_comment = self.format_comment(
                        self.latest_block_comment)
                    enum.enumerators_doc[name] = fmt_comment
                elif line.startswith(ENUM_START):
                    self.in_enum = True
                    tokens = line.split()
                    name = tokens[1]
                    self.get_current_namespace().enums.append(CppEnum(name))
                    continue
                elif line.startswith(NAMESPACE_START):
                    tokens = line.split()
                    name = tokens[1]
                    self.namespaces.append(CppNamespace(name))
