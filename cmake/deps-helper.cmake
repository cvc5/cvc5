# where to build dependencies
set(DEPS_PREFIX "${CMAKE_BINARY_DIR}/deps")
# base path to installed dependencies
set(DEPS_BASE "${CMAKE_BINARY_DIR}/deps")
# search path hint for find_X family
list(APPEND CMAKE_PREFIX_PATH "${DEPS_BASE}/deps/")
list(REMOVE_DUPLICATES CMAKE_PREFIX_PATH)
# cmake wants include dirs to exist when a target is created
file(MAKE_DIRECTORY "${DEPS_BASE}/include/")

macro(check_system_version name)
    if (${name}_FIND_VERSION)
        if(${name}_VERSION VERSION_LESS ${name}_FIND_VERSION)
            message(VERBOSE "System version for ${name} has incompatible version: required ${${name}_FIND_VERSION} but found ${${name}_VERSION}")
            set(${name}_FOUND_SYSTEM FALSE)
        endif()
    endif()
endmacro(check_system_version)

# fail if we are cross compiling as indicated by name and processor
# we are cross compiling if
# - CMAKE_SYSTEM_NAME has been changed to ${name}
# - CMAKE_SYSTEM_PROCESSOR has been changed to ${processor}
function(fail_if_cross_compiling name processor target error)
    set(FAIL FALSE)
    if(NOT "${CMAKE_SYSTEM_NAME}" STREQUAL "${CMAKE_HOST_SYSTEM_NAME}")
        if(NOT "${name}" STREQUAL "")
            if("${CMAKE_SYSTEM_NAME}" STREQUAL "${name}")
                set(FAIL TRUE)
            endif()
        endif()
    endif()
    if(NOT "${CMAKE_SYSTEM_PROCESSOR}" STREQUAL "${CMAKE_HOST_SYSTEM_PROCESSOR}")
        if(NOT "${processor}" STREQUAL "")
            if("${CMAKE_SYSTEM_PROCESSOR}" STREQUAL "${processor}")
                set(FAIL TRUE)
            endif()
        endif()
    endif()
    if(FAIL)
        message(SEND_ERROR
            "We are cross compiling from ${CMAKE_HOST_SYSTEM_NAME}-${CMAKE_HOST_SYSTEM_PROCESSOR} to ${CMAKE_SYSTEM_NAME}-${CMAKE_SYSTEM_PROCESSOR}.\n"
            "This is not supported by ${target}:\n"
            "${error}")
    endif()
endfunction(fail_if_cross_compiling)
