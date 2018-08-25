# Find ABC
# ABC_FOUND - system has ABC lib
# ABC_INCLUDE_DIR - the ABC include directory
# ABC_LIBRARIES - Libraries needed to use ABC
# ABC_ARCH_FLAGS - Platform specific compile flags

set(ABC_DEFAULT_HOME "${PROJECT_SOURCE_DIR}/abc/alanmi-abc-53f39c11b58d")

find_path(ABC_INCLUDE_DIR
          NAMES base/abc/abc.h
          PATHS ${ABC_DEFAULT_HOME}/src)
find_library(ABC_LIBRARIES
             NAMES abc
             PATHS ${ABC_DEFAULT_HOME})
find_program(ABC_ARCH_FLAGS_PROG
             NAMES arch_flags
             PATHS ${ABC_DEFAULT_HOME})

if(ABC_ARCH_FLAGS_PROG)
  execute_process(COMMAND ${ABC_ARCH_FLAGS_PROG}
                  OUTPUT_VARIABLE ABC_ARCH_FLAGS)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(ABC
  DEFAULT_MSG
  ABC_INCLUDE_DIR ABC_LIBRARIES ABC_ARCH_FLAGS)

mark_as_advanced(ABC_INCLUDE_DIR ABC_LIBRARIES ABC_ARCH_FLAGS)
