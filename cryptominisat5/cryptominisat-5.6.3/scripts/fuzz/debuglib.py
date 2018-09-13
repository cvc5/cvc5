#!/usr/bin/env python3
# -*- coding: utf-8 -*-

# Copyright (C) 2014  Mate Soos
#
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License
# as published by the Free Software Foundation; version 2
# of the License.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.

from __future__ import with_statement  # Required in 2.5
from __future__ import print_function
import random


def get_max_var_from_clause(line):
    maxvar = 0
    # strip leading 'x'
    line2 = line.strip()
    if len(line2) > 0 and line2[0] == 'x':
        line2 = line2[1:]

    for lit in line2.split():
        num = 0
        try:
            num = int(lit)
        except ValueError:
            print("line '%s' contains a non-integer variable" % line2)

        maxvar = max(maxvar, abs(num))

    return maxvar


class debuglib:
    @staticmethod
    def generate_random_assumps(maxvar):
        assumps = ""
        num = 0
        varsInside = set()

        # Half of the time, no assumptions at all
        if random.randint(0, 1) == 1:
            return assumps

        # use a distribution so that few will be in assumps
        while (num < maxvar and random.randint(0, 4) > 0):

            # get a var that is not already inside the assumps
            thisVar = random.randint(1, maxvar)
            tries = 0
            while (thisVar in varsInside):
                thisVar = random.randint(1, maxvar)
                tries += 1

                # too many tries, don't waste time
                if tries > 100:
                    return assumps

            varsInside.add(thisVar)

            # random sign
            num += 1
            if random.randint(0, 1):
                thisVar *= -1

            assumps += "%d " % thisVar

        return assumps

    @staticmethod
    def file_len_no_comment(fname):
        i = 0
        with open(fname) as f:
            for l in f:
                # ignore comments and empty lines and header
                if not l or l[0] == "c" or l[0] == "p":
                    continue
                i += 1

        return i

    @staticmethod
    def main(fname1, fname2):

        # approx number of solve()-s to add
        if random.randint(0, 1) == 1:
            num_to_add = random.randint(0, 10)
        else:
            num_to_add = 0

        # based on length and number of solve()-s to add, intersperse
        # file with ::solve()
        file_len = debuglib.file_len_no_comment(fname1)
        if num_to_add > 0:
            nextToAdd = random.randint(1, int(file_len / num_to_add) + 1)
        else:
            nextToAdd = file_len + 1

        fin = open(fname1, "r")
        fout = open(fname2, "w")
        at = 0
        maxvar = 0
        for line in fin:
            line = line.strip()

            # ignore comments (but write them out)
            if not line or line[0] == "c" or line[0] == 'p':
                fout.write(line + '\n')
                continue

            at += 1
            if at >= nextToAdd:
                assumps = debuglib.generate_random_assumps(maxvar)
                if random.choice([True, False]):
                    fout.write("c Solver::solve( %s )\n" % assumps)
                elif random.choice([True, False]):
                    fout.write("c Solver::simplify( %s )\n" % assumps)
                else:
                    fout.write("c Solver::simplify( %s )\n" % assumps)
                    fout.write("c Solver::solve( %s )\n" % assumps)

                nextToAdd = at + \
                    random.randint(1, int(file_len / num_to_add) + 1)

            # calculate max variable
            maxvar = max(maxvar, get_max_var_from_clause(line))

            # copy line over
            fout.write(line + '\n')
        fout.close()
        fin.close()


def intersperse(fname1, fname2, seed):
    random.seed(int(seed))
    debuglib.main(fname1, fname2)

