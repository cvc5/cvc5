# Find Hamcrest
# Hamcrest_FOUND - system has Hamcrest lib
# Hamcrest_JAR - the Hamcrest jar file

find_package(Java REQUIRED)
include(UseJava)

find_jar(Hamcrest_JAR hamcrest-core)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Hamcrest DEFAULT_MSG Hamcrest_JAR)

mark_as_advanced(Hamcrest_JAR)
