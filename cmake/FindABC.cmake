# Find ABC
# ABC_FOUND - system has ABC lib
# ABC_INCLUDE_DIR - the ABC include directory
# ABC_LIBRARIES - Libraries needed to use ABC
# ABC_ARCH_FLAGS - Platform specific compile flags


# Note: We don't check the system version since ABC does not provide a default
# install rule.
find_path(ABC_INCLUDE_DIR NAMES base/abc/abc.h)
find_library(ABC_LIBRARIES NAMES abc)
find_program(ABC_ARCH_FLAGS_PROG NAMES arch_flags)

if(ABC_ARCH_FLAGS_PROG)
  execute_process(COMMAND ${ABC_ARCH_FLAGS_PROG}
                  OUTPUT_VARIABLE ABC_ARCH_FLAGS)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ABC
  DEFAULT_MSG
  ABC_INCLUDE_DIR ABC_LIBRARIES ABC_ARCH_FLAGS)

mark_as_advanced(ABC_INCLUDE_DIR ABC_LIBRARIES ABC_ARCH_FLAGS)
if(ABC_LIBRARIES)
  message(STATUS "Found ABC libs: ${ABC_LIBRARIES}")
endif()
