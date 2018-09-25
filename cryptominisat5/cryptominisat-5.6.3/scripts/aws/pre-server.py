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

import boto.utils
import os

user_data = boto.utils.get_instance_userdata()

todo = ""
for line in user_data.split("\n"):
    if "DATA" in line:
        todo = line[5:].strip().strip('"')

if todo == "":
    exit(0)

os.chdir("/home/ubuntu/cryptominisat/scripts/aws/")
command = "nohup /home/ubuntu/cryptominisat/scripts/aws/server.py %s &" % todo
os.system(command)
