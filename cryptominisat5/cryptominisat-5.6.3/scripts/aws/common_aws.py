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
import boto
import traceback
import sys
import subprocess
import socket
import fcntl
import struct
from email.mime.text import MIMEText
from email.mime.application import MIMEApplication
from email.mime.multipart import MIMEMultipart
import smtplib
import ConfigParser
config = ConfigParser.ConfigParser()
config.read("/home/ubuntu/email.conf")


def send_email(subject, text, fname=None):
    msg = MIMEMultipart()
    msg['Subject'] = 'Email from solver: %s' % subject
    msg['From'] = 'msoos@msoos.org'
    msg['To'] = 'soos.mate@gmail.com'

    # That is what you see if you have no email client:
    msg.preamble = 'Multipart massage.\n'

    # Text part
    part = MIMEText(text)
    msg.attach(part)

    # Attachment(s)
    if fname:
        part = MIMEApplication(open(fname, "rb").read())
        part.add_header('Content-Disposition', 'attachment', filename="attachment.txt")
        msg.attach(part)

    # Connect to STMP server
    email_login = config.get("email", "login")
    email_pass = config.get("email", "pass")

    smtp = smtplib.SMTP_SSL("email-smtp.us-west-2.amazonaws.com")
    smtp.login(email_login, email_pass)

    # Send email
    smtp.sendmail(msg['From'], msg['To'], msg.as_string())


def get_ip_address(ifname):
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    return socket.inet_ntoa(fcntl.ioctl(
        s.fileno(),
        0x8915,  # SIOCGIFADDR
        struct.pack('256s', ifname[:15])
    )[20:24])


def get_revision(full_solver_path, base_dir):
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'])
    return revision.strip()


def get_s3_folder(folder, rev, solver, timeout, memout):
    print("folder: %s rev: %s tout: %s memout %s" % (folder, rev, timeout, memout))
    solver_exe = solver[solver.rfind("/")+1:]
    return folder + "-{rev}-{solver}-tout-{tout}-mout-{mout}".format(
        rev=rev[:9], solver=solver_exe, tout=timeout, mout=memout)
