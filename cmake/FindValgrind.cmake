# Find Valgrind
# Valgrind_FOUND - system has Valgrind lib
# Valgrind_INCLUDE_DIR - the Valgrind include directory
#
# Note: We only require the valgrind/memcheck.h header, so we don't check if
# the valgrind executable is installed.

find_path(Valgrind_INCLUDE_DIR NAMES valgrind/memcheck.h)

find_package_handle_standard_args(Valgrind REQUIRED_VARS Valgrind_INCLUDE_DIR)
mark_as_advanced(Valgrind_INCLUDE_DIR)
