#!/bin/bash
set -e

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

cd /home/ubuntu/
mkdir -p SWDiA5BY_A26
cd SWDiA5BY_A26
aws s3 cp s3://msoos-solve-data/solvers/SWDiA5BY_A26.zip . --region=us-west-2
unzip SWDiA5BY_A26.zip
./build.sh

mv /home/ubuntu/SWDiA5BY_A26/binary/SWDiA5BY_static /home/ubuntu/SWDiA5BY_A26/binary/SWDiA5BY_static_A26
# binary is now at:
# --solver SWDiA5BY_A26/binary/SWDiA5BY_static_A26

cd /home/ubuntu/
