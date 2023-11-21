###############################################################################
# Top contributors (to current version):
#   Haniel Barbosa, Andrew Reynolds, Vinícius Camillo
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
from rw_parser import Parser
from node import *
from util import *


def gen_kind(op):
    return op.kind

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
    elif sort.base == BaseSort.RegLan:
        sort_code = 'nm->regExpType()'
    elif sort.base == BaseSort.String:
        sort_code = 'nm->stringType()'
    elif sort.base == BaseSort.AbsArray:
        sort_code = 'nm->mkAbstractType(Kind::ARRAY_TYPE)'
    elif sort.base == BaseSort.AbsBitVec:
        sort_code = 'nm->mkAbstractType(Kind::BITVECTOR_TYPE)'
    elif sort.base == BaseSort.AbsSeq:
        sort_code = 'nm->mkAbstractType(Kind::SEQUENCE_TYPE)'
    elif sort.base == BaseSort.AbsSet:
        sort_code = 'nm->mkAbstractType(Kind::SET_TYPE)'
    elif sort.base == BaseSort.AbsAbs:
        sort_code = 'nm->mkAbstractType(Kind::ABSTRACT_TYPE)'
    elif sort.base == BaseSort.BitVec:
        assert len(sort.children) == 1, \
            "BitVec parser generated an incorrect number of children"
        sort_code = f'nm->mkBitVectorType({sort.children[0]})'
    else:
        die(f'Cannot generate code for {sort}')
    res = f'Node {name} = nm->mkBoundVar("{name}", {sort_code});'
    if sort.is_list:
        res += f'expr::markListVar({name});'
    return res


def gen_mk_const(expr):
    if isinstance(expr, CBool):
        return 'true' if expr.val else 'false'
    elif isinstance(expr, CString):
        return f'String("{expr.val}")'
    elif isinstance(expr, CInt):
        return f'Rational({expr.val})'
    elif isinstance(expr, App):
        args = [gen_mk_const(child) for child in expr.children]
        if expr.op == Op.NEG:
            return f'-({args[0]})'
    die(f'Cannot generate constant for {expr}')


def gen_mk_node(defns, expr):
    if defns is not None and expr in defns:
        return defns[expr]
    elif expr.sort and expr.sort.is_const:
        if isinstance(expr, CInt) or \
           (isinstance(expr, App) and expr.op == Op.NEG):
          return f'nm->mkConstRealOrInt({gen_mk_const(expr)})'
        else:
          return f'nm->mkConst({gen_mk_const(expr)})'
    elif isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, App):
        args = ",".join(gen_mk_node(defns, child) for child in expr.children)
        if expr.op in {Op.EXTRACT, Op.REPEAT, Op.ZERO_EXTEND,  Op.SIGN_EXTEND,
                       Op.ROTATE_LEFT, Op.ROTATE_RIGHT, Op.INT_TO_BV}:
          args = f'nm->mkConst(GenericOp(Kind::{gen_kind(expr.op)})),' + args
          return f'nm->mkNode(Kind::APPLY_INDEXED_SYMBOLIC, {{ {args} }})'
        return f'nm->mkNode(Kind::{gen_kind(expr.op)}, {{ {args} }})'
    else:
        die(f'Cannot generate code for {expr}')


def gen_rewrite_db_rule(defns, rule):
    fvs_list = ', '.join(bvar.name for bvar in rule.bvars)
    fixed_point_arg = gen_mk_node(defns, rule.rhs_context) \
        if rule.rhs_context else 'Node::null()'
    return f'db.addRule(DslProofRule::{rule.get_enum()}, {{ {fvs_list} }}, ' \
           f'{gen_mk_node(defns, rule.lhs)}, {gen_mk_node(defns, rule.rhs)}, '\
           f'{gen_mk_node(defns, rule.cond)}, {fixed_point_arg});'


class Rewrites:
    def __init__(self, filename, decls, rules):
        self.filename = filename
        self.decls = decls
        self.rules = rules


def type_check(expr) -> bool:
    """
    Returns true if a const subexpression exists
    """
    hasConst = any([type_check(child) for child in expr.children])

    if isinstance(expr, CBool):
        expr.sort = Sort(BaseSort.Bool, is_const=True)
        hasConst = True
    elif isinstance(expr, CString):
        expr.sort = Sort(BaseSort.String, is_const=True)
        hasConst = True
    elif isinstance(expr, CInt):
        expr.sort = Sort(BaseSort.Int, is_const=True)
        hasConst = True
    elif isinstance(expr, App):
        sort = None
        if expr.op == Op.NEG:
            sort = Sort(BaseSort.Int)
        elif expr.op == Op.STRING_LENGTH:
            sort = Sort(BaseSort.Int)

        if sort:
            sort.is_const = all(child.sort and child.sort.is_const
                                for child in expr.children)
            expr.sort = sort
            hasConst = sort.is_const

    return hasConst


def validate_rule(rule):
    # Check that all variables are matched with the left-hand side of the rule
    used_vars = set()
    to_visit = [rule.lhs]
    while to_visit:
        curr = to_visit.pop()
        if isinstance(curr, Var):
            used_vars.add(curr)
        to_visit.extend(curr.children)

    unused_vars = set(rule.bvars) - used_vars
    if unused_vars:
        die(f'Variables {unused_vars} are not matched in {rule.name}')

    # Check that list variables are always used within the same operators
    var_to_op = dict()
    to_visit = [rule.cond, rule.lhs, rule.rhs]
    while to_visit:
        curr = to_visit.pop()
        if isinstance(curr, App):
            for child in curr.children:
                if isinstance(child, Var) and child.sort.is_list:
                    if child in var_to_op and curr.op != var_to_op[child]:
                        die(f'List variable {child.name} cannot be used in '
                            f'{curr.op} and {var_to_op[child]} simultaneously')
                    var_to_op[child] = curr.op
        elif isinstance(curr, str):
            print(f"Unparsed string detected {curr}")
        to_visit.extend(curr.children)

    # Perform type checking
    lhsHasConst = type_check(rule.lhs)
    if os.getenv('CVC5_RARE_CHECK_CONST', None) is not None and lhsHasConst:
        print(f"Warning: Rule {rule.name} has constants in its match",
              file=sys.stderr)
    type_check(rule.rhs)
    type_check(rule.cond)


def preprocess_rule(rule, decls):
    if not rule.rhs_context:
        return

    # Resolve placeholders
    bvar = Var(fresh_name('t'), Sort(BaseSort.AbsAbs, []))
    decls.append(bvar)
    result = dict()
    to_visit = [rule.rhs_context]
    while to_visit:
        curr = to_visit.pop()

        if isinstance(curr, App) and curr in result:
            if result[curr]:
                continue

            new_args = []
            for child in curr.children:
                new_args.append(result[child])

            result[curr] = App(curr.op, new_args)
            continue

        if isinstance(curr, Placeholder):
            result[curr] = bvar
        elif isinstance(curr, App):
            to_visit.append(curr)
            result[curr] = None
        else:
            result[curr] = curr

        to_visit.extend(curr.children)

    rule.rhs_context = App(Op.LAMBDA, [App(Op.BOUND_VARS, [bvar]),
                                       result[rule.rhs_context]])
    type_check(rule.rhs_context)


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
            preprocess_rule(rule, file_decls)

        rewrites.append(Rewrites(rewrites_file.name, file_decls, rules))
        decls.extend(file_decls)

    defns = {}
    expr_counts = defaultdict(lambda: 0)
    to_visit = [
        expr for rewrite in rewrites for rule in rewrite.rules
        for expr in [rule.cond, rule.lhs, rule.rhs, rule.rhs_context]
    ]
    while to_visit:
        curr = to_visit.pop()

        if not curr or isinstance(curr, Var):
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
                f'case DslProofRule::{enum}: return "{rule.name}";')

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
