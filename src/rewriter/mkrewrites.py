###############################################################################
# Top contributors (to current version):
#   Andres Noetzli
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The DSL rewrite rule compiler
##

import argparse
import logging
import os
import sys
from collections import defaultdict
from util import *

def gen_rewrite_db(args):
    block_tpl = '''
        {{
            // from {filename}
            {block_code}
        }}
    '''

    decls = []
    rewrites = []

    defns = {}

    decls_code = []

    defns_code = []

    ids = []
    printer_code = []
    rules_code = []

    rewrites_h = read_tpl(args.src_dir, 'rewrites_template.h')
    with open('rewrites.h', 'w') as f:
        f.write(format_cpp(rewrites_h.format(rule_ids=','.join(ids))))

    rewrites_cpp = read_tpl(args.src_dir, 'rewrites_template.cpp')
    with open('rewrites.cpp', 'w') as f:
        f.write(
            format_cpp(
                rewrites_cpp.format(decls='\n'.join(decls_code),
                                    defns='\n'.join(defns_code),
                                    rules='\n'.join(rules_code),
                                    printer='\n'.join(printer_code))))


def main():
    parser = argparse.ArgumentParser(description="Compile rewrite rules.")
    subparsers = parser.add_subparsers()

    parser_compile = subparsers.add_parser("rewrite-db")
    parser_compile.add_argument("src_dir", help="Source directory")
    parser_compile.add_argument("rewrites_files",
                                nargs='+',
                                type=argparse.FileType("r"),
                                help="Rule files")
    parser_compile.set_defaults(func=gen_rewrite_db)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
