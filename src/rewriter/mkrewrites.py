import argparse
import logging
import os
import sys
from collections import defaultdict
from parser import Parser
from node import *
from util import *


def gen_kind(op):
    op_to_kind = {
        Op.NOT: 'NOT',
        Op.AND: 'AND',
        Op.OR: 'OR',
        Op.IMPLIES: 'IMPLIES',
        Op.EQ: 'EQUAL',
        Op.PLUS: 'PLUS',
        Op.MINUS: 'MINUS',
        Op.MULT: 'MULT',
        Op.LT: 'LT',
        Op.GT: 'GT',
        Op.LEQ: 'LEQ',
        Op.GEQ: 'GEQ',
        Op.STRING_CONCAT: 'STRING_CONCAT',
        Op.STRING_LENGTH: 'STRING_LENGTH',
        Op.STRING_SUBSTR: 'STRING_SUBSTR',
        Op.STRING_REPLACE: 'STRING_REPLACE',
    }
    return op_to_kind[op]


def gen_mk_skolem(name, sort):
    sort_code = None
    if sort.base == BaseSort.Bool:
        sort_code = 'nm->booleanType()'
    elif sort.base == BaseSort.Int:
        sort_code = 'nm->integerType()'
    elif sort.base == BaseSort.Real:
        sort_code = 'nm->realType()'
    elif sort.base == BaseSort.String:
        sort_code = 'nm->stringType()'
    else:
        die(f'Cannot generate code for {sort}')
    return f'Node {name} = nm->mkBoundVar("{name}", {sort_code});'


def gen_mk_node(defns, expr):
    if defns is not None and expr in defns:
        return defns[expr]

    if isinstance(expr, App):
        args = ",".join(gen_mk_node(defns, child) for child in expr.children)
        return f'nm->mkNode({gen_kind(expr.op)}, {args})'
    elif isinstance(expr, CBool):
        val_code = 'true' if expr.val else 'false'
        return f'nm->mkConst({val_code})'
    elif isinstance(expr, CString):
        return f'nm->mkConst(String("{expr.val}"))'
    elif isinstance(expr, CInt):
        return f'nm->mkConst(Rational({expr.val}))'
    elif isinstance(expr, Var):
        return expr.name
    else:
        die(f'Cannot generate code for {expr}')


def gen_rewrite_db_rule(defns, rule):
    fvs_list = ', '.join(bvar.name for bvar in rule.bvars)
    return f'db.addRule(DslPfRule::{rule.get_enum()}, {{ {fvs_list} }}, {gen_mk_node(defns, rule.lhs)}, {gen_mk_node(defns, rule.rhs)}, {gen_mk_node(defns, rule.cond)});'


class Rewrites:
    def __init__(self, filename, decls, rules):
        self.filename = filename
        self.decls = decls
        self.rules = rules


def validate_rule(rule):
    used_vars = set()
    to_visit = [rule.cond, rule.lhs, rule.rhs]
    while to_visit:
        curr = to_visit.pop()
        if isinstance(curr, Var):
            used_vars.add(curr)
        to_visit.extend(curr.children)

    unused_vars = set(rule.bvars) - used_vars
    if unused_vars:
        die(f'Variables {unused_vars} are unused in {rule.name}')


def gen_rewrite_db(args):
    block_tpl = '''
        {{
            // from {filename}
            {block_code}
        }}
    '''

    decls = []
    rewrites = []
    for rewrites_file in args.rewrites_files:
        parser = Parser()
        rules = parser.parse_rules(rewrites_file.read())
        symbols = parser.get_symbols()

        file_decls = []
        for rule in rules:
            file_decls.extend(rule.bvars)
            validate_rule(rule)

        rewrites.append(Rewrites(rewrites_file.name, file_decls, rules))
        decls.extend(file_decls)

    defns = {}
    expr_counts = defaultdict(lambda: 0)
    to_visit = [
        expr for rewrite in rewrites for rule in rewrite.rules
        for expr in [rule.cond, rule.lhs, rule.rhs]
    ]
    while to_visit:
        curr = to_visit.pop()

        if isinstance(curr, Var):
            # Don't generate definitions for variables
            continue

        if expr_counts[curr] == 0:
            expr_counts[curr] = 1
            to_visit.extend(curr.children)
        elif curr not in defns:
            defns[curr] = fresh_name('e')

    decls_code = []
    for decl in decls:
        decls_code.append(gen_mk_skolem(decl.name, decl.sort))

    defns_code = []
    for expr, name in defns.items():
        defns_code.append(f'Node {name} = {gen_mk_node(None, expr)};')

    ids = []
    printer_code = []
    rules_code = []
    for rewrite_file in rewrites:
        block = []
        for rule in rewrite_file.rules:
            block.append(gen_rewrite_db_rule(defns, rule))

            enum = rule.get_enum()
            ids.append(enum)
            printer_code.append(
                f'case DslPfRule::{enum}: return "{rule.name}";')

        rules_code.append(
            block_tpl.format(filename=rewrite_file.filename,
                             block_code='\n'.join(block)))

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
