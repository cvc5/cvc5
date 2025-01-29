###############################################################################
# Top contributors (to current version):
#   Aina Niemetz, Gereon Kremer, Daniel Larraz
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# The build system configuration.
#
add_subdirectory(cpp)
add_subdirectory(c)
add_subdirectory(java)
add_subdirectory(python)

# tell parent scope where to find the output xml
set(CPP_DOXYGEN_XML_DIR
  "${CPP_DOXYGEN_XML_DIR}"
    PARENT_SCOPE
)
set(C_DOXYGEN_XML_DIR
  "${C_DOXYGEN_XML_DIR}"
    PARENT_SCOPE
)
