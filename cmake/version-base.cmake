###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# [[ Add one-line brief description here ]]
#
# [[ Add lengthier description here ]]
# \todo document this file
##
# These are updated when making a release
set(CVC5_LAST_RELEASE "0.0.12")
set(CVC5_IS_RELEASE "false")

# These are used in other places in cmake
# If possible, they are updated by version.cmake
set(GIT_BUILD "false")
set(CVC5_VERSION "${CVC5_LAST_RELEASE}")
set(CVC5_FULL_VERSION "${CVC5_LAST_RELEASE}")
set(CVC5_GIT_INFO "")

# Shared library versioning. Increment SOVERSION for every new cvc5 release.
set(CVC5_SOVERSION 1)
