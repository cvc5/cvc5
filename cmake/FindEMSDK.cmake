cmake_minimum_required(VERSION 3.9)
include(FetchContent)

set(EMSDK_VERSION "3.1.18")
set(EMSDK_FOUND FALSE)
set(DEP_NAME "emsdk")
set(DEPS_DIR "${ROOT_DIR}/deps/")

file(MAKE_DIRECTORY "${DEPS_DIR}/${DEP_NAME}")


# Try to find EMSDK
if(EXISTS "${DEPS_DIR}")
endif()

if(EMSDK_FOUND)
    # Enforces the version

else()
    # Donwload the emsdk
    file(DOWNLOAD https://codeload.github.com/emscripten-core/emsdk/zip/refs/heads/main ${DEPS_DIR}/${DEP_NAME}.zip)
    file(ARCHIVE_EXTRACT 
        INPUT ${DEPS_DIR}/${DEP_NAME}.zip 
        DESTINATION ${DEPS_DIR})
    add_custom_command(aaa unZip)

    # git pull
    # ./emsdk install latest
    # ./emsdk activate latest
    # source ./emsdk_env.sh
endif()

# Make sure the desired version is activated and installed
# Add the emscripten variables to the PATH