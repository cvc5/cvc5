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
# Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
# 02110-1301, USA.


from __future__ import print_function
import sys

from optparse import OptionParser
parser = OptionParser()
parser.add_option("-n", "--num",
                  dest="num", type=int,
                  help="Number of reconfs")
parser.add_option("--ignore", "-i",
                  dest="ignore", type=str,
                  help="Ignore these reconfs")

(options, args) = parser.parse_args()

ignore = {}
if options.ignore:
    for r in options.ignore.split(","):
        r = r.strip()
        r = int(r)
        ignore[r] = True

if options.num is None:
    print("ERROR: You must give the number of reconfs")
    exit(-1)

print("""/******************************************
Copyright (c) 2016, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "solvefeatures.h"
#include <iostream>
using std::cout;
using std::endl;

namespace CMSat {
""")

for i in range(options.num):
    if i not in ignore:
        print("double get_score%d(const SolveFeatures& feat, const int verb);" % i)

print("""
int get_reconf_from_features(const SolveFeatures& feat, const int verb)
{
\tdouble best_score = 0.0;
\tint best_val = 0;
\tdouble score;
""")

for i in range(options.num):
    if i in ignore:
        continue

    print("""
\tscore = get_score%d(feat, verb);
\tif (verb >= 2)
\t\tcout << "c Score for reconf %d is " << score << endl;
\tif (best_score < score) {
\t\tbest_score = score;
\t\tbest_val = %d;
\t}
""" % (i, i, i))

print("""
\tif (verb >= 2)
\t\tcout << "c Winning reconf is " << best_val << endl;
\treturn best_val;
}

""")


def read_one_reconf(reconf_num):
    sys.stderr.write("Parsing reconf num %d\n" % reconf_num)
    f = open("outs/out%d.rules" % reconf_num)
    num_conds = 0
    cond_no = 0
    num_rules = 0
    rule_no = 0
    string = ""

    print("""
double get_score%d(const SolveFeatures& feat, const int verb)
{""" % reconf_num)
    for line in f:
        if "id=" in line:
            continue

        line = line.strip()
        line = line.split(" ")
        dat = {}
        for elem in line:
            elems = elem.split("=")
            elems = [e.strip("\"") for e in elems]
            dat[elems[0]] = elems[1]

        if "conds" in dat:
            assert num_conds == cond_no
            num_conds = int(dat["conds"])
            rule_class = dat["class"]
            cond_no = 0
            confidence = float(dat["confidence"])
            continue

        if "entries" in dat:
            continue

        if "rules" in dat:
            num_rules = int(dat["rules"])

        if "default" in dat:
            default = dat["default"]
            if default == "+":
                print("\tdouble default_val = %.2f;\n" % (1.0))
            else:
                print("\tdouble default_val = %.2f;\n" % (0.0))

            print("\tdouble total_plus = 0.0;")
            print("\tdouble total_neg = 0.0;")
            continue

        # process rules
        if cond_no == 0:
            string = "\tif ("
        else:
            string += " &&\n\t\t"

        string += "(feat.%s %s %.5f)" % (dat["att"], dat["result"],
                                         float(dat["cut"]))
        cond_no += 1

        # end rules
        if cond_no == num_conds:
            string += ")\n\t{"
            print(string)

            string = ""
            if rule_class == "+":
                string += "\t\ttotal_plus += %.3f;" % confidence
            else:
                string += "\t\ttotal_neg += %.3f;" % confidence

            print(string)
            print("\t}")
            rule_no += 1

    print("\t// num_rules:", num_rules)
    print("\t// rule_no:", rule_no)
    sys.stderr.write("num rules: %s rule_no: %s\n" % (num_rules, rule_no))
    assert num_rules == rule_no
    print("\t// default is:", default)
    print("""
\tif (total_plus == 0.0 && total_neg == 0.0) {
\t\treturn default_val;
\t}
\tif (verb >= 2) {
\t\t//cout << "c plus: " << total_plus << " , neg: " << total_neg << endl;
\t}
\treturn total_plus - total_neg;
}
""")


for i in range(options.num):
    if i not in ignore:
        read_one_reconf(i)

print("""
} //end namespace""")
