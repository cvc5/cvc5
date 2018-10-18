# Find SymFPU
# SymFPU_FOUND - system has SymFPU lib
# SymFPU_INCLUDE_DIR - the SymFPU include directory


# Check default location of SymFPU built with contrib/get-symfpu.
# If the user provides a directory we will not search the default paths and
# fail if SymFPU was not found in the specified directory.
if(NOT SymFPU_HOME)
  set(SymFPU_HOME ${PROJECT_SOURCE_DIR}/symfpu-CVC4)
  set(CHECK_SYSTEM_VERSION TRUE)
endif()

find_path(SymFPU_INCLUDE_DIR
          NAMES symfpu/core/unpackedFloat.h
          PATHS ${SymFPU_HOME}
          NO_DEFAULT_PATH)

if(CHECK_SYSTEM_VERSION)
  find_path(SymFPU_INCLUDE_DIR NAMES symfpu/core/unpackedFloat.h)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(SymFPU DEFAULT_MSG SymFPU_INCLUDE_DIR)

mark_as_advanced(SymFPU_INCLUDE_DIR)
