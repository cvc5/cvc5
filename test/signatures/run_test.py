#!/usr/bin/env python
#####################
## run_test.py
## Top contributors (to current version):
##   Andres Noetzli, Alex Ozdemir
## This file is part of the CVC4 project.
## Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
## in the top-level source directory and their institutional affiliations.
## All rights reserved.  See the file COPYING in the top-level source
## directory for licensing information.
##

import argparse
import re
import os.path
import sys
import subprocess


class TestConfiguration(object):
    """Represents a test to run."""
    def __init__(self):
        """Initialized from program arguments.
        Exists with code 2 and prints usage message on invalid arguments."""
        parser = argparse.ArgumentParser(
            description='Runs `lfscc on a test file.')
        parser.add_argument('lfscc_binary')
        parser.add_argument('input')
        parser.add_argument('include_dirs', nargs='*')
        args = parser.parse_args()

        self.lfscc = args.lfscc_binary
        self.dep_graph = DepGraph(args.input, args.include_dirs)


class DepGraph(object):
    """Represents a dependency graph of LFSC input files"""
    def __init__(self, root_path, include_dirs):
        """Creates a dependency graph rooted a `root_path`.
        Computes a root-last topological sort.
        Exits with exitcode 1 on cyclic dependencies"""

        # Root of the graph
        self._r = root_path

        # Nodes (paths) that have been visited
        self._visited = set()

        # Nodes (paths) that have been ordered
        self._ordered_set = set()

        # The order of nodes (paths). Root is last.
        self._ordered_paths = []

        self.include_dirs = include_dirs

        # Start DFS topo-order
        self._visit(root_path)

    def _visit(self, p):
        """Puts the descendents of p in the order, parent-last"""
        node = TestFile(p, self.include_dirs)
        self._visited.add(p)
        for n in node.dep_paths:
            if n not in self._ordered_set:
                if n in self._visited:
                    # Our child is is an ancestor our ours!?
                    print("{} and {} are in a dependency cycle".format(p, n))
                    sys.exit(1)
                else:
                    self._visit(n)
        self._ordered_paths.append(p)
        self._ordered_set.add(p)

    def getPathsInOrder(self):
        return self._ordered_paths


class TestFile(object):
    """Represents a testable input file to LFSC"""
    def __init__(self, path, include_dirs):
        """Read the file at `path` and determine its immediate dependencies"""
        self.path = path
        self._get_config_map()
        self.deps = self.config_map['deps'].split() if (
            'deps' in self.config_map) else []
        self.dir = os.path.dirname(self.path)
        self.dep_paths = []
        include_paths = include_dirs + [self.dir]
        for dep in self.deps:
            found_dep = False
            for include_path in include_paths:
                dep_path = os.path.join(include_path, dep)
                if os.path.isfile(dep_path):
                    self.dep_paths.append(dep_path)
                    found_dep = True
                    break
            assert found_dep

    def _get_comment_lines(self):
        """Return an iterator over comment lines, ;'s included"""
        with open(self.path, 'r') as test_file:
            return (line for line in test_file.readlines() if \
                    re.match(r'^\s*;.*$', line) is not None)

    def _get_config_map(self):
        """Populate self.config_map.
        Config variables are set using the syntax
        ; Var Name Spaces Okay: space separated values"""
        m = {}
        for l in self._get_comment_lines():
            match = re.match(r'^.*;\s*(\w+(?:\s+\w+)*)\s*:(.*)$', l)
            if match is not None:
                m[match.group(1).replace(' ', '').lower()] = match.group(2)
        self.config_map = m


def main():
    configuration = TestConfiguration()
    cmd = [configuration.lfscc] + configuration.dep_graph.getPathsInOrder()
    result = subprocess.Popen(cmd,
                              stderr=subprocess.STDOUT,
                              stdout=subprocess.PIPE)
    (stdout, _) = result.communicate()
    if 0 != result.returncode:
        if stdout:
            print(stdout.decode())
    return result.returncode


if __name__ == '__main__':
    sys.exit(main())
