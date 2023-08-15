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
	'-DBUILD_BINDINGS_PYTHON_VERSION:STRING=' + sysconfig.get_python_version(),
	'-DPython_INCLUDE_DIR:PATH=' +
			sysconfig.get_path("include"),
	'-DPython_LIBRARY:FILEPATH=' +
			sysconfig.get_path("libdir"),
	'-DPYTHON_INCLUDE_DIR:PATH=' +
			sysconfig.get_path("include"),
	'-DPYTHON_LIBRARY:FILEPATH=' +
			sysconfig.get_path("libdir"),
]

subprocess.check_call(['./configure.sh', *sys.argv[1:], *args])
