#!/usr/bin/env python3
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
##
"""
Exhaustively check the word-blasted encodings of floating-point operations
in small formats against the results of constant folding.

For each instance, i.e., an operation on a format or a pair of formats, the
script

  1. asks the given cvc5 binary for the value of the operation applied to
     every constant input under every rounding mode, which is computed via
     constant folding (checked by requiring that all values are literals),
     and
  2. checks that (not table) is unsat, where rm and b are symbolic, the
     operands of op are given by the bits of b, and table is a decision tree
     over rm and the bits of b, whose leaves are (= (op rm b) v) for the
     values v from 1.

The values of fp.min, fp.max, fp.to_sbv and fp.to_ubv are not constant
folded if their result is unspecified and are computed by this script
instead. Inputs for which their result is unspecified are excluded from the
check. Instances with more than 2^12 inputs are split into chunks of 2^12
inputs.

Constant folding is an independent reference only if cvc5 is configured with
MPFR (the default), else it uses SymFPU as well.

With --self-check, one entry of each table is changed and the query is
expected to be sat, to make sure the check detects incorrect encodings.

The unit test test/unit/theory/theory_fp_word_blaster_black.cpp performs the
same check for smaller formats. Run this script after changing the patches
applied to SymFPU (cmake/deps-utils/symfpu-*.patch) or updating SymFPU, e.g.:

  contrib/check-fp-word-blaster.py build/bin/cvc5
"""

import argparse
import concurrent.futures
import math
import os
import random
import re
import subprocess
import sys
import tempfile
import time
from fractions import Fraction

RMS = ['RNE', 'RNA', 'RTP', 'RTN', 'RTZ']
CHUNK_BITS = 12
# Experimental formats require --fp-exp. Bit-blasting into the main SAT solver
# is considerably faster than lazy bit-blasting for these queries.
CVC5_ARGS = ['--fp-exp', '--bv-solver=bitblast-internal']

# Operations on floating-point operands of the same format:
# name -> (number of operands, has rounding mode, term template)
FP_OPS = {
    'abs': (1, False, '(fp.abs {0})'),
    'neg': (1, False, '(fp.neg {0})'),
    'sqrt': (1, True, '(fp.sqrt {rm} {0})'),
    'rti': (1, True, '(fp.roundToIntegral {rm} {0})'),
    'isNormal': (1, False, '(fp.isNormal {0})'),
    'isSubnormal': (1, False, '(fp.isSubnormal {0})'),
    'isZero': (1, False, '(fp.isZero {0})'),
    'isInfinite': (1, False, '(fp.isInfinite {0})'),
    'isNaN': (1, False, '(fp.isNaN {0})'),
    'isNegative': (1, False, '(fp.isNegative {0})'),
    'isPositive': (1, False, '(fp.isPositive {0})'),
    'add': (2, True, '(fp.add {rm} {0} {1})'),
    'sub': (2, True, '(fp.sub {rm} {0} {1})'),
    'mul': (2, True, '(fp.mul {rm} {0} {1})'),
    'div': (2, True, '(fp.div {rm} {0} {1})'),
    'rem': (2, False, '(fp.rem {0} {1})'),
    'min': (2, False, '(fp.min {0} {1})'),
    'max': (2, False, '(fp.max {0} {1})'),
    'eq': (2, False, '(fp.eq {0} {1})'),
    'lt': (2, False, '(fp.lt {0} {1})'),
    'leq': (2, False, '(fp.leq {0} {1})'),
    'gt': (2, False, '(fp.gt {0} {1})'),
    'geq': (2, False, '(fp.geq {0} {1})'),
    'equal': (2, False, '(= {0} {1})'),
    'fma': (3, True, '(fp.fma {rm} {0} {1} {2})'),
}
UNARY_OPS = [k for k, v in FP_OPS.items() if v[0] == 1 and k != 'rti']
BINARY_OPS = [k for k, v in FP_OPS.items() if v[0] == 2]
CONVERSIONS = ['fp2fp', 'sbv2fp', 'ubv2fp', 'to_sbv', 'to_ubv']
# Operations whose values are computed by this script.
NOT_FOLDED = ['min', 'max', 'to_sbv', 'to_ubv']
# The values printed by cvc5 if they are computed via constant folding.
LITERAL = re.compile(r'\(fp #b[01] #b[01]+ #b[01]+\)|#b[01]+|true|false')


def formats(max_size):
    """All formats of at most max_size bits."""
    return [(e, s) for e in range(2, max_size) for s in range(2, max_size)
            if e + s <= max_size]


def bv_value(size, value):
    return '#b' + format(value, f'0{size}b')


def parse_sexprs(text):
    stack = [[]]
    for tok in re.findall(r'\(|\)|[^\s()]+', text):
        if tok == '(':
            stack.append([])
        elif tok == ')':
            top = stack.pop()
            stack[-1].append(top)
        else:
            stack[-1].append(tok)
    if len(stack) != 1:
        raise ValueError('unbalanced parentheses')
    return stack[0]


def sexpr_str(sexpr):
    if isinstance(sexpr, list):
        return '(' + ' '.join(sexpr_str(x) for x in sexpr) + ')'
    return sexpr


class Instance:
    """
    An operation instance. For operations in FP_OPS, src is the format of
    the operands. For fp2fp, to_sbv and to_ubv, src is the input format, for
    sbv2fp and ubv2fp the size of the bit-vector input. dst is the target
    format of conversions to floating-point, and the size of the result of
    to_sbv and to_ubv.
    """

    def __init__(self, kind, src, dst=None):
        self.kind = kind
        self.src = src
        self.dst = dst

    @property
    def name(self):
        fmt = lambda f: f'{f[0]}_{f[1]}'
        if self.kind in FP_OPS:
            return f'{self.kind}_{fmt(self.src)}'
        if self.kind == 'fp2fp':
            return f'fp2fp_{fmt(self.src)}_to_{fmt(self.dst)}'
        if self.kind in ('to_sbv', 'to_ubv'):
            return f'{self.kind}_{fmt(self.src)}_to_bv{self.dst}'
        return f'{self.kind}_bv{self.src}_to_{fmt(self.dst)}'

    @property
    def num_operands(self):
        return FP_OPS[self.kind][0] if self.kind in FP_OPS else 1

    @property
    def has_rm(self):
        return FP_OPS[self.kind][1] if self.kind in FP_OPS else True

    @property
    def operand_size(self):
        return self.src if isinstance(self.src, int) else sum(self.src)

    @property
    def bv_size(self):
        return self.num_operands * self.operand_size

    @property
    def rms(self):
        return RMS if self.has_rm else RMS[:1]

    def term(self, rm, b):
        """The operation applied to the operands given by the bits of b."""
        n = self.operand_size
        xs = []
        for i in range(self.num_operands):
            x = b
            if self.num_operands > 1:
                x = f'((_ extract {(i + 1) * n - 1} {i * n}) {b})'
            if not isinstance(self.src, int):
                x = f'((_ to_fp {self.src[0]} {self.src[1]}) {x})'
            xs.append(x)
        if self.kind in FP_OPS:
            return FP_OPS[self.kind][2].format(*xs, rm=rm)
        if self.kind in ('to_sbv', 'to_ubv'):
            return f'((_ fp.{self.kind} {self.dst}) {rm} {xs[0]})'
        e, s = self.dst
        if self.kind == 'ubv2fp':
            return f'((_ to_fp_unsigned {e} {s}) {rm} {xs[0]})'
        return f'((_ to_fp {e} {s}) {rm} {xs[0]})'

    def chunks(self):
        """Chunks of inputs as pairs of the value and size of the fixed most
        significant bits of b."""
        hi = max(0, self.bv_size - CHUNK_BITS)
        return [(c, hi) for c in range(1 << hi)]

    def inputs(self, chunk):
        c, hi = chunk
        lo = self.bv_size - hi
        return [(c << lo) | i for i in range(1 << lo)]

    def chunk_name(self, chunk):
        return self.name if chunk[1] == 0 else f'{self.name}_{chunk[0]}'


def decode(value, fmt):
    """Decode a floating-point value of the given format."""
    e, s = fmt
    sign = value >> (e + s - 1)
    exp = (value >> (s - 1)) & ((1 << e) - 1)
    frac = value & ((1 << (s - 1)) - 1)
    bias = (1 << (e - 1)) - 1
    if exp == (1 << e) - 1:
        return ('nan',) if frac else ('inf', sign)
    if exp == 0:
        mag = Fraction(frac, 1 << (s - 1)) * Fraction(2) ** (1 - bias)
    else:
        mag = (1 + Fraction(frac, 1 << (s - 1))) * Fraction(2) ** (exp - bias)
    return ('num', sign, mag)


def round_to_integral(q, rm):
    floor = math.floor(q)
    diff = q - floor
    if rm == 'RTN' or diff == 0:
        return floor
    if rm == 'RTP':
        return floor + 1
    if rm == 'RTZ':
        return math.trunc(q)
    if diff != Fraction(1, 2):
        return floor if diff < Fraction(1, 2) else floor + 1
    if rm == 'RNE':
        return floor if floor % 2 == 0 else floor + 1
    return floor + 1 if q > 0 else floor


def compute_value(inst, rm, value):
    """Get (specified, value) for an operation in NOT_FOLDED."""
    n = inst.operand_size
    if inst.kind in ('min', 'max'):
        x, y = value & ((1 << n) - 1), value >> n
        dx, dy = decode(x, inst.src), decode(y, inst.src)
        fp = lambda v: f'((_ to_fp {inst.src[0]} {inst.src[1]}) {bv_value(n, v)})'
        if dx[0] == 'nan':
            return True, fp(y)
        if dy[0] == 'nan':
            return True, fp(x)
        if dx[0] == dy[0] == 'num' and dx[2] == dy[2] == 0 and dx[1] != dy[1]:
            # The result for -zero and +zero is unspecified.
            return False, fp(x)
        key = lambda d: ((-1 if d[1] else 1) * math.inf if d[0] == 'inf'
                         else (-d[2] if d[1] else d[2]))
        if inst.kind == 'min':
            return True, fp(x if key(dx) <= key(dy) else y)
        return True, fp(x if key(dx) >= key(dy) else y)
    d = decode(value, inst.src)
    m = inst.dst
    if d[0] != 'num':
        # The result for NaN and infinity is unspecified.
        return False, bv_value(m, 0)
    r = round_to_integral(-d[2] if d[1] else d[2], rm)
    if inst.kind == 'to_sbv':
        specified = -(1 << (m - 1)) <= r < (1 << (m - 1))
    else:
        specified = 0 <= r < (1 << m)
    # The result for out-of-range values is unspecified.
    return specified, bv_value(m, r % (1 << m) if specified else 0)


def run(binary, args, smt2, path, timeout):
    with open(path, 'w') as outfile:
        outfile.write(smt2)
    try:
        proc = subprocess.run([binary] + CVC5_ARGS + args + [path],
                              capture_output=True,
                              text=True,
                              timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'timeout', '', ''
    if proc.returncode != 0:
        return f'error({proc.returncode})', proc.stdout, proc.stderr
    return 'ok', proc.stdout, proc.stderr


def compute_values(inst, chunk, binary, outdir, timeout):
    """Get {rm: [(specified, value of input i)]} for the inputs of a chunk."""
    inputs = inst.inputs(chunk)
    if inst.kind in NOT_FOLDED:
        return {rm: [compute_value(inst, rm, v) for v in inputs]
                for rm in inst.rms}
    n = inst.bv_size
    terms = [inst.term(rm, bv_value(n, v)) for rm in inst.rms for v in inputs]
    smt2 = ('(set-option :produce-models true)\n(set-logic ALL)\n'
            '(check-sat)\n(get-value (' + '\n'.join(terms) + '))\n')
    status, out, err = run(
        binary, [], smt2,
        os.path.join(outdir, inst.chunk_name(chunk) + '.values.smt2'), timeout)
    lines = out.splitlines()
    if status != 'ok' or lines[:1] != ['sat']:
        raise RuntimeError(f'computing values failed ({status}): '
                           f'{(out + err)[-500:]}')
    pairs = parse_sexprs('\n'.join(lines[1:]))
    if len(pairs) != 1 or len(pairs[0]) != len(terms):
        raise RuntimeError('unexpected get-value output')
    values = [sexpr_str(p[1]) for p in pairs[0]]
    for v in values:
        if not LITERAL.fullmatch(v):
            raise RuntimeError(f'value not computed via constant folding: {v}')
    k = len(inputs)
    return {rm: [(True, v) for v in values[i * k:(i + 1) * k]]
            for i, rm in enumerate(inst.rms)}


def mk_tree(values, size, leaf):
    """Decision tree over the lower size bits of b with leaves leaf(v) for
    the given values, collapses equal subtrees."""
    if size == 0:
        return leaf(values[0])
    half = len(values) // 2
    lo = mk_tree(values[:half], size - 1, leaf)
    hi = mk_tree(values[half:], size - 1, leaf)
    if lo == hi:
        return lo
    return f'(ite (= ((_ extract {size - 1} {size - 1}) b) #b1) {hi} {lo})'


def mk_query(inst, chunk, values):
    c, hi = chunk
    lo = inst.bv_size - hi
    # The table is a Boolean decision tree with leaves (= r v) rather than a
    # tree over the values, since cvc5 introduces a fresh constant for each
    # ite of floating-point sort, which is considerably slower.
    table = lambda rm: mk_tree([v for _, v in values[rm]], lo,
                               lambda v: f'(= r {v})')
    specified = lambda rm: mk_tree(
        ['true' if s else 'false' for s, _ in values[rm]], lo, lambda v: v)
    rms = inst.rms
    vtable, stable = table(rms[-1]), specified(rms[-1])
    for rm in reversed(rms[:-1]):
        vtable = f'(ite (= rm {rm}) {table(rm)} {vtable})'
        stable = f'(ite (= rm {rm}) {specified(rm)} {stable})'
    query = ['(set-logic ALL)',
             '(declare-const rm RoundingMode)',
             f'(declare-const b (_ BitVec {inst.bv_size}))']
    if not inst.has_rm:
        query.append('(assert (= rm RNE))')
    if hi:
        query.append(f'(assert (= ((_ extract {inst.bv_size - 1} {lo}) b) '
                     f'{bv_value(hi, c)}))')
    if stable != 'true':
        query.append(f'(assert {stable})')
    query.append(f'(assert (let ((r {inst.term("rm", "b")}))\n'
                 f'(not {vtable})))')
    query.append('(check-sat)')
    return '\n'.join(query) + '\n'


def mutate(values, rng):
    """Replace one specified value by a different value of the same sort."""
    values = {rm: list(v) for rm, v in values.items()}
    candidates = sorted({v for vs in values.values() for _, v in vs})
    rm = rng.choice(list(values))
    specified = [i for i, (s, _) in enumerate(values[rm]) if s]
    if not specified or len(candidates) < 2:
        return None
    i = rng.choice(specified)
    values[rm][i] = (True, rng.choice([v for v in candidates
                                       if v != values[rm][i][1]]))
    return values


def check(inst, chunk, binary, outdir, timeout, self_check, seed):
    name = inst.chunk_name(chunk)
    try:
        values = compute_values(inst, chunk, binary, outdir, timeout)
    except Exception as e:
        return 'error', str(e)
    status, out, err = run(binary, [], mk_query(inst, chunk, values),
                           os.path.join(outdir, name + '.smt2'), timeout)
    if status != 'ok':
        return status, (out + err)[-500:]
    result = out.split()[0] if out.split() else ''
    if result != 'unsat':
        return 'fail', f'expected unsat, got {result}'
    if self_check:
        mutated = mutate(values, random.Random(seed))
        if mutated is not None:
            status, out, err = run(
                binary, [], mk_query(inst, chunk, mutated),
                os.path.join(outdir, name + '.mutated.smt2'), timeout)
            if status != 'ok' or out.split()[:1] != ['sat']:
                return 'fail', f'mutated table not detected: {(out + err)[-500:]}'
    return 'pass', ''


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument('binary', help='path to the cvc5 binary')
    ap.add_argument('--ops',
                    default=','.join(list(FP_OPS) + CONVERSIONS),
                    help='comma-separated list of operations (default: %(default)s)')
    ap.add_argument('--unary-size', type=int, default=12,
                    help='max. format size for unary operations (default: %(default)s)')
    ap.add_argument('--rti-size', type=int, default=13,
                    help='max. format size for rti (default: %(default)s)')
    ap.add_argument('--binary-size', type=int, default=8,
                    help='max. format size for binary operations (default: %(default)s)')
    ap.add_argument('--fma-size', type=int, default=6,
                    help='max. format size for fma (default: %(default)s)')
    ap.add_argument('--src-size', type=int, default=10,
                    help='max. source format size for fp2fp, to_sbv, to_ubv '
                         '(default: %(default)s)')
    ap.add_argument('--dst-size', type=int, default=13,
                    help='max. target format size for conversions to '
                         'floating-point (default: %(default)s)')
    ap.add_argument('--bv-size', type=int, default=10,
                    help='max. bit-vector size for sbv2fp, ubv2fp, to_sbv, '
                         'to_ubv (default: %(default)s)')
    ap.add_argument('--filter', help='only check instances matching this regex')
    ap.add_argument('--self-check', action='store_true',
                    help='also check that a mutated table is detected')
    ap.add_argument('--jobs', '-j', type=int, default=os.cpu_count(),
                    help='number of parallel jobs (default: %(default)s)')
    ap.add_argument('--timeout', type=float, default=600,
                    help='time limit per query in seconds (default: %(default)s)')
    ap.add_argument('--outdir',
                    help='directory for the generated queries (default: temporary)')
    args = ap.parse_args()

    ops = args.ops.split(',')
    unknown = [op for op in ops if op not in FP_OPS and op not in CONVERSIONS]
    if unknown:
        ap.error(f'unknown operations: {",".join(unknown)}')
    instances = []
    for op in ops:
        if op == 'rti':
            instances += [Instance(op, f) for f in formats(args.rti_size)]
        elif op in UNARY_OPS:
            instances += [Instance(op, f) for f in formats(args.unary_size)]
        elif op in BINARY_OPS:
            instances += [Instance(op, f) for f in formats(args.binary_size)]
        elif op == 'fma':
            instances += [Instance(op, f) for f in formats(args.fma_size)]
        elif op == 'fp2fp':
            instances += [Instance(op, f1, f2)
                          for f1 in formats(args.src_size)
                          for f2 in formats(args.dst_size)]
        elif op in ('sbv2fp', 'ubv2fp'):
            instances += [Instance(op, size, f)
                          for size in range(1, args.bv_size + 1)
                          for f in formats(args.dst_size)]
        else:
            instances += [Instance(op, f, size)
                          for f in formats(args.src_size)
                          for size in range(1, args.bv_size + 1)]
    if args.filter:
        instances = [i for i in instances if re.search(args.filter, i.name)]
    queries = [(inst, chunk) for inst in instances for chunk in inst.chunks()]
    # Start with the largest queries for better load balancing.
    queries.sort(key=lambda q: -(q[0].bv_size - q[1][1]))

    outdir = args.outdir or tempfile.mkdtemp(prefix='check-fp-word-blaster-')
    os.makedirs(outdir, exist_ok=True)
    print(f'checking {len(instances)} instances ({len(queries)} queries), '
          f'queries in {outdir}', flush=True)

    counts = {}
    start = time.time()
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as executor:
        futures = {
            executor.submit(check, inst, chunk, args.binary, outdir,
                            args.timeout, args.self_check, k): (inst, chunk)
            for k, (inst, chunk) in enumerate(queries)
        }
        for k, future in enumerate(concurrent.futures.as_completed(futures), 1):
            inst, chunk = futures[future]
            status, msg = future.result()
            counts[status] = counts.get(status, 0) + 1
            if status != 'pass':
                print(f'{status}: {inst.chunk_name(chunk)}: {msg.strip()}',
                      flush=True)
            if k % 100 == 0:
                print(f'[{k}/{len(queries)}] {counts}', flush=True)
    print(f'{len(queries)} queries in {time.time() - start:.0f}s: {counts}')
    return 0 if set(counts) <= {'pass'} else 1


if __name__ == '__main__':
    sys.exit(main())
