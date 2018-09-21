#!/usr/bin/env python
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
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.

from __future__ import print_function
import re


class XorToCNF:
    def __init__(self):
        self.cutsize = 4

    def get_max_var(self, clause):
        maxvar = 0

        tmp = clause.strip()
        if len(tmp) == 0:
            return 0

        assert re.search(r'^x? *-?\d+', tmp)

        if tmp[0] == 'x':
            tmp = tmp[1:]

        for lit in tmp.split():
            var = abs(int(lit))
            maxvar = max(var, maxvar)

        return maxvar

    def convert(self, infilename, outfilename):
        assert isinstance(self.cutsize, int)
        if self.cutsize <= 2:
            print("ERROR: The cut size MUST be larger or equal to 3")
            exit(-1)

        maxvar, numcls, extravars_needed, extracls_needed = self.get_stats(infilename)
        fout = open(outfilename, "w")
        fout.write("p cnf %d %d\n" % (maxvar + extravars_needed, numcls + extracls_needed))
        fin = open(infilename, "r")
        atvar = maxvar
        for line in fin:
            line = line.strip()

            # skip empty line
            if len(line) == 0:
                continue

            # skip header and comments
            if line[0] == 'c' or line[0] == 'p':
                continue

            if line[0] == 'x':
                # convert XOR to normal(s)
                xorclauses, atvar = self.cut_up_xor_to_n(line, atvar)
                for xorcl in xorclauses:
                    cls = self.xor_to_cnf_simple(xorcl)
                    for cl in cls:
                        fout.write(cl + "\n")
            else:
                # simply print normal clause
                fout.write(line + "\n")

        assert atvar == maxvar + extravars_needed
        fout.close()
        fin.close()

    def popcount(self, x):
        return bin(x).count('1')

    def parse_xor(self, xorclause):
        assert re.search(r'^x( *-?\d+ )*0$', xorclause)

        tmp = xorclause[1:]
        lits = [int(elem) for elem in tmp.split()]
        assert lits[len(lits)-1] == 0

        # remove last element, the 0
        lits = lits[:len(lits)-1]

        return lits

    def xor_to_cnf_simple(self, xorclause, equals=True):
        assert equals is True or equals is False
        if equals is True:
            equals = 1
        else:
            equals = 0

        lits = self.parse_xor(xorclause)

        # empty XOR clause is TRUE, so is NOT an empty clause (i.e. UNSAT)
        if len(lits) == 0:
            return []

        ret = []
        for i in range(2**(len(lits))):
            # only the ones we need
            cls = ""
            if self.popcount(i) % 2 == equals:
                continue

            for at in range(len(lits)):
                if ((i >> at) & 1) == 0:
                    cls += "%d " % lits[at]
                else:
                    cls += "%d " % (-1*lits[at])

            cls += "0"
            ret.append(cls)

        return ret

    def cut_up_xor_to_n(self, xorclause, oldmaxvar):
        assert self.cutsize > 2

        lits = self.parse_xor(xorclause)
        xors = []

        # xor clause that doesn't need to be cut up
        if len(lits) <= self.cutsize:
            retcl = "x"
            for lit in lits:
                retcl += "%d " % lit
            retcl += "0"
            return [[retcl], oldmaxvar]

        at = 0
        newmaxvar = oldmaxvar
        while(at < len(lits)):

            # until when should we cut?
            until = min(at + self.cutsize-1, len(lits))

            # if in the middle, don't add so much
            if at > 0 and until < len(lits):
                until -= 1

            thisxor = "x"
            for i2 in range(at, until):
                thisxor += "%d " % lits[i2]

            # add the extra variables
            if at == 0:
                # beginning, add only one
                thisxor += "%d 0" % (newmaxvar+1)
                newmaxvar += 1
            elif until == len(lits):
                # end, only add the one we already made
                thisxor += "-%d 0" % (newmaxvar)
            else:
                thisxor += "-%d %d 0" % (newmaxvar, newmaxvar+1)
                newmaxvar += 1

            xors.append(thisxor)

            # move along where we are at
            at = until

        return [xors, newmaxvar]

    def num_extra_vars_cls_needed(self, numlits):
        def cls_for_plain_xor(numlits):
            return 2**(numlits-1)

        varsneeded = 0
        clsneeded = 0

        at = 0
        while(at < numlits):
            # at the beginning
            if at == 0:
                if numlits > self.cutsize:
                    at += self.cutsize-1
                    varsneeded += 1
                    clsneeded += cls_for_plain_xor(self.cutsize)
                else:
                    at = numlits
                    clsneeded += cls_for_plain_xor(numlits)

            # in the middle
            elif at + (self.cutsize-1) < numlits:
                at += self.cutsize-2
                varsneeded += 1
                clsneeded += cls_for_plain_xor(self.cutsize)
            # at the end
            else:
                clsneeded += cls_for_plain_xor(numlits-at+1)
                at = numlits

        return [varsneeded, clsneeded]

    def get_stats(self, infilename):
        infile = open(infilename, "r")

        maxvar = 0
        numcls = 0
        extravars_needed = 0
        extracls_needed = 0
        for line in infile:
            line = line.strip()

            # empty line, skip
            if len(line) == 0:
                continue

            # header or comment
            if line[0] == 'p' or line[0] == 'c':
                continue

            # get max var
            maxvar = max(self.get_max_var(line), maxvar)

            if line[0] == 'x':
                e_var, e_clause = self.num_extra_vars_cls_needed(len(self.parse_xor(line)))
                extravars_needed += e_var
                extracls_needed += e_clause
            else:
                numcls += 1

        infile.close()

        return [maxvar, numcls, extravars_needed, extracls_needed]
