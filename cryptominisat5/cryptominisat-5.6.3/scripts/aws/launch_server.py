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
import boto.ec2
import os
import subprocess
import server_option_parser


def get_answer():
    yes = set(['yes', 'y', 'ye'])
    no = set(['no', 'n'])

    choice = input().lower()
    if choice in yes:
        return True
    elif choice in no:
        return False
    else:
        sys.stdout.write("Please respond with 'yes' or 'no'\n")
        exit(0)


def push():
    print("First we push, oherwise we'll forget...")
    ret = os.system("git push")
    if ret != 0:
        print("Oops, couldn't push, exiting before executing")
        exit(-1)

    print("")


if __name__ == "__main__":
    options, args = server_option_parser.parse_arguments()
    print("Options are:")
    for a, b in options.__dict__.items():
        print("-- %-30s : %s" % (a, b))
    assert args == []

    if options.mem_limit_in_mb < 10000 and options.drat:
        print("******* WARNING ********")
        print("Beware: your memory is WAY too low for DRAT and learning stuff")

    push()
    data = ""
    opt_is_on = False
    for x in sys.argv[1:]:
        if opt_is_on:
            data += " ".join(x.split(","))
            data += "\" "
            opt_is_on = False
            continue
        if x != "--opt":
            data += x + " "
            continue

        opt_is_on = True
        data += "--opt \""

    if ("--git" not in data):
        revision = subprocess.check_output(['git', 'rev-parse', 'HEAD']).strip().decode("utf-8")
        data += " --git '{revision}'".format(revision=revision)

    if len(sys.argv) > 1:
        print("Launching with data: %s" % data)
    else:
        print("you must give at least one parameter, probably --s3folder")
        exit(-1)

    sys.stdout.write("Is this OK? [y/n]? ")
    if not get_answer():
        print("Aborting")
        exit(0)

    print("Executing!")

    cloud_init = """#!/bin/bash
set -e

apt-get update
apt-get install -y python
apt-get -y install git python-pip
pip install --force-reinstall --upgrade awscli
pip install --force-reinstall --upgrade boto
pip install configparser

# Get AWS log agent
cd /home/ubuntu/

cat > aws-logs-server.conf << EOF
[general]
state_file = /home/ubuntu/cloudwatch.state

[logstream1]
log_group_name = cyrptominisat-perftest
log_stream_name = server
file = /home/ubuntu/*.log

[messages]
log_group_name = cyrptominisat-perftest
log_stream_name = server
file = /var/log/messages
EOF

curl https://s3.amazonaws.com/aws-cloudwatch/downloads/latest/awslogs-agent-setup.py -O
python ./awslogs-agent-setup.py --region {region} -c aws-logs-server.conf -n

sudo -H -u ubuntu bash -c 'ssh-keyscan github.com >> ~/.ssh/known_hosts'
sudo -H -u ubuntu bash -c 'git clone --depth 50 https://github.com/msoos/cryptominisat.git'

# Get credentials
cd /home/ubuntu
sudo -H -u ubuntu bash -c 'aws s3 cp s3://msoos-solve-data/solvers/email.conf . --region={region}'

# Start server
cd /home/ubuntu/cryptominisat
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/pre-server.py > /home/ubuntu/pre_server_log.log  2>&1 &'

DATA="{data}"
    """.format(region=options.region, data=data)

    conn = boto.ec2.connect_to_region(options.region)
    conn.run_instances(
        min_count=1,
        max_count=1,
        image_id=options.ami_id,
        subnet_id=options.subnet_id,
        instance_type='t2.micro',
        instance_profile_arn='arn:aws:iam::907572138573:instance-profile/server',
        user_data=cloud_init,
        key_name=options.key_name,
        security_group_ids=[options.security_group_server],
        instance_initiated_shutdown_behavior='terminate')
