###############################################################################
# Top contributors (to current version):
#   Gereon Kremer
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# ############################################################################
#
# Run configure.sh and make cmake pick up whatever python interpreter this
# script is run with. Additionally, all arguments passed to this script are
# forwarded as well.
##

import subprocess
import sys
import sysconfig

args = [
	'-DPython_INCLUDE_DIR:PATH=' +
			sysconfig.get_path("scripts"),
	'-DPython_LIBRARY:FILEPATH=' +
			sysconfig.get_path("platlib"),
	'-DPYTHON_INCLUDE_DIR:PATH=' +
			sysconfig.get_path("scripts"),
	'-DPYTHON_LIBRARY:FILEPATH=' +
			sysconfig.get_path("platlib"),
]

subprocess.check_call(['./configure.sh', *sys.argv[1:], *args])
