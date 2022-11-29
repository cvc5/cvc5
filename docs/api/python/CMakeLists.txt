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
# #############################################################################
#
# Build system configuration for python API documentation.
##

add_custom_target(docs-python)

if (BUILD_BINDINGS_PYTHON)
    add_dependencies(docs-python cvc5_python_api)
endif()
