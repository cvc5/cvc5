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
import configparser
from boto.ec2.connection import EC2Connection
from common_aws import *
import logging


class RequestSpotClient:
    def __init__(self, revision, test, noshutdown=False, count=1):
        self.conf = configparser.ConfigParser()
        self.count = count
        if test:
            self.conf.read('ec2-spot-instance-test.cfg')
            self.limit_create = 1
        else:
            self.conf.read('ec2-spot-instance.cfg')
            self.limit_create = 8

        if self.count is None:
            self.count = int(self.conf.get('ec2', 'count'))

        self.ec2conn = self.__create_ec2conn()
        if self.ec2conn is None:
            print('Unable to create EC2 ec2conn')
            sys.exit(0)

        self.user_data = self.__get_user_data(revision, noshutdown)
        self.our_ids = []

    def __get_user_data(self, revision, noshutdown):
        extra_args = ""
        if noshutdown:
            extra_args = " --noshutdown"
        user_data = """#!/bin/bash
set -e

apt-get update -y
apt-get install -y python
apt-get -y install git python-pip
pip install --force-reinstall --upgrade awscli
pip install --force-reinstall --upgrade boto
pip install configparser
apt-get -y install cmake make g++ libboost-all-dev
apt-get -y install libsqlite3-dev awscli unzip
apt-get install zlib1g-dev
# apt-get -y install linux-cloud-tools-generic linux-tools-generic
# apt-get -y install linux-cloud-tools-3.13.0-53-generic linux-tools-3.13.0-53-generic

# Get AWS log agent
cd /home/ubuntu/

cat > "aws-logs-client.conf" << EOF
[general]
state_file = /home/ubuntu/cloudwatch.state

[logstream1]
log_group_name = cyrptominisat-perftest
log_stream_name = client
file = /home/ubuntu/*.log

[messages]
log_group_name = cyrptominisat-perftest
log_stream_name = client
file = /var/log/messages
EOF

curl https://s3.amazonaws.com/aws-cloudwatch/downloads/latest/awslogs-agent-setup.py -O
python ./awslogs-agent-setup.py --region {region} -c aws-logs-client.conf -n

# Get CMS
sudo -H -u ubuntu bash -c 'ssh-keyscan github.com >> ~/.ssh/known_hosts'
sudo -H -u ubuntu bash -c 'git clone --no-single-branch --depth 50 https://github.com/msoos/cryptominisat.git'
cd /home/ubuntu/cryptominisat
sudo -H -u ubuntu bash -c 'git checkout {revision}'
sudo -H -u ubuntu bash -c 'git submodule init'
sudo -H -u ubuntu bash -c 'git submodule update'
cd /home/ubuntu/
# sudo -H -u ubuntu bash -c 'aws s3 cp s3://msoos-solve-data/solvers/features_to_reconf.cpp /home/ubuntu/cryptominisat/src/ --region={region}'

# Get credentials
cd /home/ubuntu/
sudo -H -u ubuntu bash -c 'aws s3 cp s3://msoos-solve-data/solvers/email.conf . --region={region}'

# build solvers
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_maplecomsps_drup.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_swdia5by.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_swdia5by_old.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_lingeling_ayv.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_drat-trim2.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_glucose2016.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_cmsat_satcomp16.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_lingeling_bbc.sh >> /home/ubuntu/build.log'
sudo -H -u ubuntu bash -c '/home/ubuntu/cryptominisat/scripts/aws/build_Maple_LCM_Dist.sh >> /home/ubuntu/build.log'

# Start client
cd /home/ubuntu/cryptominisat
sudo -H -u ubuntu bash -c 'nohup /home/ubuntu/cryptominisat/scripts/aws/client.py {extra_args} > /home/ubuntu/python_log.log 2>&1' &

DATA="{ip}"
""".format(revision=revision, extra_args=extra_args, ip=get_ip_address("eth0"), region=self.conf.get("ec2", "region"))

        return user_data

    def __create_ec2conn(self):
        ec2conn = EC2Connection()
        regions = ec2conn.get_all_regions()
        for r in regions:
            if r.name == self.conf.get('ec2', 'region'):
                ec2conn = EC2Connection(region=r)
                return ec2conn
        return None

    def __provision_instances(self):
        reqs = self.ec2conn.request_spot_instances(
            price=self.conf.get('ec2', 'max_bid'),
            count=self.count,
            image_id=self.conf.get('ec2', 'ami_id'),
            subnet_id=self.conf.get('ec2', 'subnet_id'),
            instance_type=self.conf.get('ec2', 'type'),
            instance_profile_arn=self.conf.get('ec2', 'instance_profile_arn'),
            user_data=self.user_data,
            key_name=self.conf.get('ec2', 'key_name'),
            security_group_ids=[self.conf.get('ec2', 'security_group_client')])

        logging.info("Request created, got back IDs %s" % [r.id for r in reqs])
        return reqs

    def create_spots_if_needed(self):
        # Valid values: open | active | closed | cancelled | failed
        run_wait_spots = self.ec2conn.get_all_spot_instance_requests(filters={'state': 'open'})
        run_wait_spots.extend(self.ec2conn.get_all_spot_instance_requests(filters={'state': 'active'}))

        for spot in run_wait_spots:
            if spot.id in self.our_ids:
                logging.info("ID %s is either waiting or running, not requesting a new one" % spot.id)
                return

        if len(self.our_ids) >= self.limit_create:
            logging.error("Something really wrong has happened, we have reqested 4 spots aready! Not requesting more.")
            return

        self.create_spots()

    def create_spots(self):
        reqs = self.__provision_instances()

        for req in reqs:
            logging.info('New req state: %s ID: %s' % (req.state, req.id))
            self.our_ids.append(req.id)

        return self.our_ids
