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

from skbuild.cmaker import CMaker

python_version = CMaker.get_python_version()
args = [
	'-DBUILD_BINDINGS_PYTHON_VERSION:STRING=' + python_version,
	'-DPython_INCLUDE_DIR:PATH=' +
			CMaker.get_python_include_dir(python_version),
	'-DPython_LIBRARY:FILEPATH=' +
			CMaker.get_python_library(python_version),
	'-DPYTHON_INCLUDE_DIR:PATH=' +
			CMaker.get_python_include_dir(python_version),
	'-DPYTHON_LIBRARY:FILEPATH=' +
			CMaker.get_python_library(python_version),
]

subprocess.check_call(['./configure.sh', *sys.argv[1:], *args])
