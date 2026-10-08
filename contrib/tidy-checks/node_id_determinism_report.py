#!/usr/bin/env python3
###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Post-processes the per-translation-unit dumps written by the
# cvc5-node-id-determinism clang-tidy check in dump mode (option DumpDir).
#
# Each dump is a tab-separated file with the following records:
#   T <main file>                     the translation unit
#   N <id> <qualified name>           display name of a function id
#   E <caller id> <callee id>         direct call between project functions
#   S <file:line:col> <kind> <end> <i> <id>
#                                     operand i of the unsequenced site that
#                                     starts at file:line:col and ends at
#                                     <end> (line:col) calls id
#
# The set of NodeId-dependent functions is the transitive closure of the
# callers of the minting points (the functions that increment the NodeId
# counter). A site is reported when at least two of its operands call a
# NodeId-dependent function, since C++ leaves their evaluation order
# unspecified.
##

import argparse
import collections
import os
import re
import sys

MINTING_POINTS = [
    "cvc5::internal::NodeManager::mkConstInternal",
    "cvc5::internal::NodeBuilder::constructNV",
]


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("dump_dir", help="directory with the *.tsv dumps")
    ap.add_argument(
        "--minting-point",
        action="append",
        default=None,
        help="qualified name of a function that assigns NodeIds "
        f"(default: {', '.join(MINTING_POINTS)})",
    )
    ap.add_argument(
        "--write-dependency-list",
        metavar="FILE",
        help="also write the qualified names of all NodeId-dependent "
        "functions to FILE (usable as NodeIdDependencyListPath)",
    )
    ap.add_argument(
        "--write-dependency-ids",
        metavar="FILE",
        help="also write the ids of all NodeId-dependent functions to FILE "
        "(usable as NodeIdDependencyIdListPath)",
    )
    ap.add_argument(
        "--write-flagged-files",
        metavar="FILE",
        help="also write to FILE, one per line, a set of translation units "
        "that together contain all flagged sites; re-checking them with "
        "NodeIdDependencyIdListPath reproduces the report as clang-tidy "
        "diagnostics",
    )
    ap.add_argument(
        "--ignore-path-regex",
        metavar="REGEX",
        help="do not report sites whose file path matches REGEX",
    )
    ap.add_argument("--quiet", action="store_true", help="no summary")
    args = ap.parse_args()
    minting = set(args.minting_point or MINTING_POINTS)

    names = {}
    callers = collections.defaultdict(set)
    # (location, kind, end) -> operand index -> set of callee ids
    sites = collections.defaultdict(lambda: collections.defaultdict(set))
    # (location, kind, end) -> a translation unit in which the site was seen
    site_tu = {}
    ignore = re.compile(args.ignore_path_regex) if args.ignore_path_regex else None
    num_tus = num_edges = 0

    for entry in sorted(os.listdir(args.dump_dir)):
        if not entry.endswith(".tsv"):
            continue
        with open(os.path.join(args.dump_dir, entry), encoding="utf-8") as f:
            tu = None
            for line in f:
                rec = line.rstrip("\n").split("\t")
                tag = rec[0]
                if tag == "E":
                    callers[rec[2]].add(rec[1])
                    num_edges += 1
                elif tag == "S":
                    if ignore and ignore.search(rec[1]):
                        continue
                    key = (rec[1], rec[2], rec[3])
                    sites[key][int(rec[4])].add(rec[5])
                    site_tu.setdefault(key, tu)
                elif tag == "N":
                    names[rec[1]] = rec[2]
                elif tag == "T":
                    tu = rec[1]
                    num_tus += 1

    # Transitive closure of callers, starting from the minting points.
    dependent = {fid for fid, name in names.items() if name in minting}
    if not dependent:
        print(
            "error: no minting point found in the dumps; expected one of: "
            + ", ".join(sorted(minting)),
            file=sys.stderr,
        )
        return 2
    work = list(dependent)
    while work:
        fid = work.pop()
        for caller in callers.get(fid, ()):
            if caller not in dependent:
                dependent.add(caller)
                work.append(caller)

    if args.write_dependency_list:
        with open(args.write_dependency_list, "w", encoding="utf-8") as out:
            for name in sorted({names[fid] for fid in dependent}):
                out.write(f'"{name}"\n')

    # Report sites with two or more operands calling dependent functions.
    def sort_key(item):
        loc = item[0][0]
        path, line, col = loc.rsplit(":", 2)
        return (path, int(line), int(col))

    if args.write_dependency_ids:
        with open(args.write_dependency_ids, "w", encoding="utf-8") as out:
            for fid in sorted(dependent):
                out.write(fid + "\n")

    num_flagged = 0
    flagged_tus = set()
    for (loc, kind, end), operands in sorted(sites.items(), key=sort_key):
        hits = {
            i: sorted(names.get(fid, fid) for fid in fids if fid in dependent)
            for i, fids in operands.items()
        }
        hits = {i: fns for i, fns in hits.items() if fns}
        if len(hits) < 2:
            continue
        num_flagged += 1
        flagged_tus.add(site_tu[(loc, kind, end)])
        if kind == "mkNode":
            msg = (
                "potential non-deterministic NodeId assignment in mkNode(); "
                "wrap node arguments in braces to enforce left-to-right sequencing"
            )
        else:
            msg = "potential non-deterministic NodeId assignment"
        print(f"{loc}: warning: {msg} [cvc5-node-id-determinism]")
        for i in sorted(hits):
            print(f"{loc}: note: operand {i + 1} calls " + ", ".join(hits[i]))

    if args.write_flagged_files:
        with open(args.write_flagged_files, "w", encoding="utf-8") as out:
            for tu in sorted(flagged_tus):
                out.write(tu + "\n")

    if not args.quiet:
        print(
            f"cvc5-node-id-determinism: {num_tus} translation units, "
            f"{len(names)} functions, {num_edges} call edges, "
            f"{len(dependent)} NodeId-dependent functions, "
            f"{len(sites)} candidate sites, {num_flagged} flagged",
            file=sys.stderr,
        )
    return 1 if num_flagged else 0


if __name__ == "__main__":
    sys.exit(main())
