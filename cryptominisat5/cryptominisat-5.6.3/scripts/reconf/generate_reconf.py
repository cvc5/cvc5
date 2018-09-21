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

from __future__ import with_statement  # Required in 2.5
from __future__ import print_function
import sys
import subprocess


def query_yes_no(question, default="no"):
    """Ask a yes/no question via input() and return their answer.

    "question" is a string that is presented to the user.
    "default" is the presumed answer if the user just hits <Enter>.
        It must be "yes" (the default), "no" or None (meaning
        an answer is required of the user).

    The "answer" return value is True for "yes" or False for "no".
    """
    valid = {"yes": True, "y": True, "ye": True,
             "no": False, "n": False}
    if default is None:
        prompt = " [y/n] "
    elif default == "yes":
        prompt = " [Y/n] "
    elif default == "no":
        prompt = " [y/N] "
    else:
        raise ValueError("invalid default answer: '%s'" % default)

    while True:
        sys.stdout.write(question + prompt)
        choice = input().lower()
        if default is not None and choice == '':
            return valid[default]
        elif choice in valid:
            return valid[choice]
        else:
            sys.stdout.write("Please respond with 'yes' or 'no' "
                             "(or 'y' or 'n').\n")


num = 18
ignore = "1,2,8,9,10,11,15,5,14,13,3"
files = "/home/soos/media/sat/out/new/out-reconf-6776906.wlm01-*/*.out"

# for testing
#num = 8
#ignore = "0,1,2,3,5,6"
#files = "/home/soos/media/sat/out/new2/out-reconf-6776906.wlm01-*/*.out"

ignore_elems = {}
for x in ignore.split(","):
    x = x.strip()
    if x == "":
        continue

    x = int(x)
    ignore_elems[x] = True

subprocess.call("rm outs/*", shell=True)
toexec = "./reconf.py -n %d -i %s  -f outs/out  %s" % (num, ignore, files)
f = open("output", "w")
ret = subprocess.call(toexec, shell=True, stdout=f)
f.close()
if ret != 0:
    print("ERROR: reconf call exited non-zero: %s" % toexec)
    exit(-1)

for i in range(num):
    if i in ignore_elems:
        continue

    print("reconf with %d" % i)
    subprocess.call("cp outs/reconf.names outs/out%d.names" % i, shell=True)
    subprocess.call("c5.0 -u 20 -f outs/out%d -r > outs/out%d.c50.out" % (i, i), shell=True)

subprocess.call("./tocpp.py -i %s -n %d > ../../src/features_to_reconf.cpp" % (ignore, num),
                shell=True)

subprocess.call("sed -i 's/red-/red_cl_distrib./g' ../../src/features_to_reconf.cpp",
                shell=True)

upload = query_yes_no("Upload to AWS?")
if upload:
    subprocess.call("aws s3 cp ../../src/features_to_reconf.cpp s3://msoos-solve-data/solvers/", shell=True)
    print("Uploded to AWS")
else:
    print("Not uploaded to AWS")


