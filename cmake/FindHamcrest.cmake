###############################################################################
# Top contributors (to current version):
#   Mathias Preiner
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find Hamcrest
# Hamcrest_FOUND - system has Hamcrest lib
# Hamcrest_JAR - the Hamcrest jar file
##

find_package(Java REQUIRED)
include(UseJava)

find_jar(Hamcrest_JAR hamcrest-core)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Hamcrest DEFAULT_MSG Hamcrest_JAR)

mark_as_advanced(Hamcrest_JAR)
