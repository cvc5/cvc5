import argparse
import logging
import os
import sys
from subprocess import Popen, PIPE, STDOUT
from parser import Parser
from node import *


# TODO: refactor common code
def read_tpl(directory, name):
    """
    Read a template file directory/name. The contents of the template file will
    be read into a string, which will later be used to fill in the generated
    code/documentation via format. Hence, we have to escape curly braces. All
    placeholder variables in the template files are enclosed in ${placeholer}$
    and will be {placeholder} in the returned string.
    """
    fname = os.path.join(directory, name)
    try:
        # Escape { and } since we later use .format to add the generated code.
        # Further, strip ${ and }$ from placeholder variables in the template
        # file.
        with open(fname, 'r') as file:
            contents = \
                file.read().replace('{', '{{').replace('}', '}}').\
                            replace('${', '').replace('}$', '')
            return contents
    except IOError:
        die("Could not find '{}'. Aborting.".format(fname))


def format_cpp(s):
    p = Popen(["clang-format"], stdout=PIPE, stdin=PIPE, stderr=STDOUT)
    out = p.communicate(input=s.encode())[0]
    return out.decode()


def gen_kind(op):
    op_to_kind = {
        Op.NOT: 'NOT',
        Op.AND: 'AND',
        Op.OR: 'OR',
        Op.EQ: 'EQUAL',
        Op.STRING_CONCAT: 'STRING_CONCAT'
    }
    return op_to_kind[op]


def gen_mk_skolem(name, sort):
    sort_code = None
    if sort.base == BaseSort.String:
        sort_code = 'nm->stringType()'
    else:
        die(f'Cannot generate code for {sort}')
    return f'Node {name} = nm->mkBoundVar("{name}", {sort_code})'


def gen_mk_node(expr):
    if isinstance(expr, App):
        args = ",".join(gen_mk_node(child) for child in expr.children)
        return f'nm->mkNode({gen_kind(expr.op)}, {args})'
    elif isinstance(expr, CString):
        return f'nm->mkConst(String("{expr.val}"))'
    elif isinstance(expr, CBool):
        val_code = 'true' if expr.val else 'false'
        return f'nm->mkConst({val_code})'
    elif isinstance(expr, Var):
        return expr.name
    else:
        die(f'Cannot generate code for {expr}')


def gen_rewrite_db_rule(rule):
    return f'db.addRule({gen_mk_node(rule.lhs)}, {gen_mk_node(rule.rhs)}, nm->mkConst(true), "{rule.name}");'


def gen_rewrite_db(args):
    instrs = []
    for rewrites_file in args.rewrites_files:
        parser = Parser()
        rules = parser.parse_rules(rewrites_file.read())
        symbols = parser.get_symbols()

        for name, sort in parser.get_symbols().symbols.items():
            instrs.append(gen_mk_skolem(name, sort))

        for rule in rules:
            instrs.append(gen_rewrite_db_rule(rule))

    rewrites_h = read_tpl(args.src_dir, 'rewrites_template.h')
    with open('rewrites.h', 'w') as f:
        f.write(format_cpp(rewrites_h.format()))

    rewrites_cpp = read_tpl(args.src_dir, 'rewrites_template.cpp')
    with open('rewrites.cpp', 'w') as f:
        f.write(format_cpp(rewrites_cpp.format(instrs=';'.join(instrs))))


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
