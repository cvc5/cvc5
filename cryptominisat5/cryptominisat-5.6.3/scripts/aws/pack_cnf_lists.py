#!/usr/bin/env python
# -*- coding: utf-8 -*-

# Copyright (C) 2018  Mate Soos
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

if len(sys.argv) == 1:
    print("""Usage example:
./{name} satcomp14_updated satcomp16_updated > satcomp1416_updated
""".format(name=sys.argv[0]))
    exit(-1)

files = {}
for a in range(len(sys.argv)-1):
    with open(sys.argv[a+1], "r") as f:
        for l in f:
            l = l.strip()
            fname = l[l.find("/")+1:]
            files[fname] = l

for a,b in files.items():
    print(b)
