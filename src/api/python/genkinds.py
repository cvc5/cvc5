#!/usr/bin/env python
"""
This script reads CVC4/src/api/cvc4cppkind.h and generates
.pxd and .pxi files which declare all the CVC4 kinds and
implement a Python wrapper for kinds, respectively. The
default names are kinds.pxd / kinds.pxi, but the name is
configurable from the command line with --kinds-file-prefix.

The script is aware of the '#if 0' pattern and will ignore
kinds declared between '#if 0' and '#endif'. It can also
handle nested '#if 0' pairs.
"""

import argparse
from collections import OrderedDict

#################### Default Filenames ################
DEFAULT_HEADER      = 'cvc4cppkind.h'
DEFAULT_PREFIX      = 'kinds'

##################### Useful Constants ################
OCB                 = '{'
CCB                 = '}'
SC                  = ';'
EQ                  = '='
C                   = ','
US                  = '_'
NL                  = '\n'

#################### Enum Declarations ################
ENUM_START          = 'enum CVC4_PUBLIC Kind'
ENUM_END            = CCB+SC

################ Comments and Macro Tokens ############
PYCOMMENT           = '#'
COMMENT             = '//'
BLOCK_COMMENT_BEGIN = '/*'
BLOCK_COMMENT_END   = '*/'
MACRO_BLOCK_BEGIN   = '#if 0'
MACRO_BLOCK_END     = '#endif'

#################### Format Kind Names ################
# special cases for format_name
_IS                 = '_IS'
# replacements after some preprocessing
replacements        = {
    'Bitvector'    : 'BV',
    'Floatingpoint': 'FP'
}

####################### Code Blocks ###################
CDEF_KIND = "    cdef Kind "

KINDS_PXD_TOP = \
r"""cdef extern from "api/cvc4cppkind.h" namespace "CVC4::api":
    cdef cppclass Kind:
        pass


# Kind declarations: See cvc4cppkind.h for additional information
cdef extern from "api/cvc4cppkind.h" namespace "CVC4::api::Kind":
"""

KINDS_PXI_TOP = \
r"""# distutils: language = c++
# distutils: extra_compile_args = -std=c++11

from cvc4kinds cimport *
import sys
from types import ModuleType

from libcpp.string cimport string
from libcpp.unordered_map cimport unordered_map

# these maps are used for creating a kind
# it is needed for dynamically making a kind
# e.g. for getKind()
cdef unordered_map[int, Kind] int2kind
cdef unordered_map[int, string] int2name

cdef class kind:
    cdef Kind k
    cdef str name
    def __cinit__(self, int kindint):
        self.k = int2kind[kindint]
        self.name = str(int2name[kindint])

    def __eq__(self, kind other):
        return (<int> self.k) == (<int> other.k)

    def __ne__(self, kind other):
        return (<int> self.k) != (<int> other.k)

    def __hash__(self):
        return hash((<int> self.k, self.name))

    def __str__(self):
        return self.name

    def __repr__(self):
        return self.name

    def as_int(self):
        return <int> self.k

# create a kinds submodule
kinds = ModuleType('kinds')
kinds.__file__ = kinds.__name__ + ".py"
"""

KINDS_ATTR_TEMPLATE = \
r"""
int2kind[<int> {kind}] = {kind}
int2name[<int> {kind}] = b"{name}"
cdef kind {name} = kind(<int> {kind})
setattr(kinds, "{name}", {name})
"""

class KindsParser:
    tokenmap = {
        BLOCK_COMMENT_BEGIN : BLOCK_COMMENT_END,
        MACRO_BLOCK_BEGIN   : MACRO_BLOCK_END
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
        name = name.replace(_IS, _IS+US)
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
                    self.endtoken =None
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

    def gen_pxd(self, filename):
        f = open(filename, "w")
        f.write(KINDS_PXD_TOP)
        # include the format_name docstring in the generated file
        # could be helpful for users to see the formatting rules
        for line in self.format_name.__doc__.split(NL):
            f.write(PYCOMMENT)
            if not line.isspace():
                f.write(line)
            f.write(NL)
        for kind in self.kinds:
            f.write(CDEF_KIND + kind + NL)
        f.close()

    def gen_pxi(self, filename):
        f = open(filename, "w")
        pxi = KINDS_PXI_TOP
        for kind, name in self.kinds.items():
            pxi += KINDS_ATTR_TEMPLATE.format(name=name, kind=kind)
        f.write(pxi)
        f.close()


if __name__ == "__main__":
    parser = argparse.ArgumentParser('Read a kinds header file and generate a '
                         'corresponding pxd file, with simplified kind names.')
    parser.add_argument('--kinds-header', metavar='<KINDS_HEADER>',
                        help='The header file to read kinds from',
                        default=DEFAULT_HEADER)
    parser.add_argument('--kinds-file-prefix', metavar='<KIND_FILE_PREFIX>',
                        help='The prefix for the .pxd and .pxi files to write '
                        'the Cython declarations to.',
                        default=DEFAULT_PREFIX)

    args               = parser.parse_args()
    kinds_header       = args.kinds_header
    kinds_file_prefix  = args.kinds_file_prefix

    kp = KindsParser()
    kp.parse(kinds_header)

    kp.gen_pxd(kinds_file_prefix + ".pxd")
    kp.gen_pxi(kinds_file_prefix + ".pxi")
