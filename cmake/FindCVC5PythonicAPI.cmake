###############################################################################
# Top contributors (to current version):
#   Gereon Kremer, Alex Ozdemir
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# Find cvc5 pythonic api. 
# CVC5PythonicAPI_FOUND - found cvc5 pythonic api
# CVC5PythonicAPI_BASEDIR - the base directory of the cvc5 pythonic api
##

include(deps-helper)

check_ep_downloaded("CVC5PythonicAPI")
if(NOT CVC5PythonicAPI_DOWNLOADED)
  check_auto_download("CVC5PythonicAPI" "--no-python-bindings")
endif()

include(ExternalProject)

set(CVC5PythonicAPI_VERSION "db1315dfa7f8d34ac66ef44b13f0e62fbcb6b0b7")
ExternalProject_Add(
  CVC5PythonicAPI
  ${COMMON_EP_CONFIG}
  URL https://github.com/cvc5/cvc5_pythonic_api/archive/${CVC5PythonicAPI_VERSION}.zip
  URL_HASH SHA1=5c7648efc4530ceea21b76495839ca674452efab
  CONFIGURE_COMMAND ""
  BUILD_COMMAND ""
  INSTALL_COMMAND ""
)

set(CVC5PythonicAPI_FOUND TRUE)
ExternalProject_Get_Property(CVC5PythonicAPI SOURCE_DIR)
set(CVC5PythonicAPI_BASEDIR "${SOURCE_DIR}")

mark_as_advanced(CVC5PythonicAPI_FOUND)
mark_as_advanced(CVC5PythonicAPI_BASEDIR)

message(STATUS "Downloading pythonic API: ${CVC5PythonicAPI_BASEDIR}")
