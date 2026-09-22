###############################################################################
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
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


include(ExternalProject)
if(PYTHONIC_PATH)
  ExternalProject_Add(
    CVC5PythonicAPI
    ${COMMON_EP_CONFIG}
    SOURCE_DIR ${PYTHONIC_PATH}
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
  )
else()
  check_ep_downloaded("CVC5PythonicAPI")
  if(NOT CVC5PythonicAPI_DOWNLOADED)
    check_auto_download("CVC5PythonicAPI" "--no-python-bindings")
  endif()

  set(CVC5PythonicAPI_VERSION "a0d6c75bca0dca4a26c0d570e7b969272c9a7de1")
  ExternalProject_Add(
    CVC5PythonicAPI
    ${COMMON_EP_CONFIG}
    URL https://github.com/cvc5/cvc5_pythonic_api/archive/${CVC5PythonicAPI_VERSION}.zip
    URL_HASH SHA256=1fb5b7f0afcd61ddb51a113ce84bdd679c00429c67266339ae5a2b5d4961b5d0
    CONFIGURE_COMMAND ""
    BUILD_COMMAND ""
    INSTALL_COMMAND ""
  )
endif()

set(CVC5PythonicAPI_FOUND TRUE)
ExternalProject_Get_Property(CVC5PythonicAPI SOURCE_DIR)
set(CVC5PythonicAPI_BASEDIR "${SOURCE_DIR}")

mark_as_advanced(CVC5PythonicAPI_FOUND)
mark_as_advanced(CVC5PythonicAPI_BASEDIR)
message(STATUS "Pythonic API: ${CVC5PythonicAPI_BASEDIR}")
