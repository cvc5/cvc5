#!/bin/bash
################################################################################
# Description: This script allows the user to compile CVC5 
#               (https://github.com/cvc5/cvc5) to a WebAssembly version. The 
#               user can select between WASM, JS or HTML extension.
# Author: Vinícius Braga Freire (vinicius.braga.freire@gmail.com)
################################################################################

# Dirs:
BASE_DIR=$(dirname $(realpath $0))/../
CVC5_DIR=${BASE_DIR}
DEP_DIR=${BASE_DIR}deps/
EMSDK_DIR=${DEP_DIR}emsdk/

# Other vars:
CORES_TO_COMPILE=6
BUILD_NAME=production
EXTENSION=JS

echo ""
echo "-------------------------------"
echo "- Downloading deps"
echo "-------------------------------"

echo "   ---EMSDK";
    echo ""
    echo "Downloading Emscripten:"
    echo ""
    cd $DEP_DIR
    git clone https://github.com/emscripten-core/emsdk.git

echo ""
echo "-------------------------------"
echo "- Configuring deps"
echo "-------------------------------"

echo "   ---Emscripten";
    echo ""
    echo "Configuring Emscripten:"
    echo ""
    cd ${EMSDK_DIR}
    git pull
    ./emsdk install latest
    ./emsdk activate latest
    source ./emsdk_env.sh

echo "";
echo "   ---CVC5";
    echo ""
    echo "Configuring CVC5:"
    echo ""

    # The flags used in the link of the final binary. These are the em++ flags.
    EMCC_WASM_FLAGS=(   
                        # -s EXPORTED_FUNCTIONS=_main 
                        -s EXPORTED_RUNTIME_METHODS=ccall,cwrap 
                        -s INCOMING_MODULE_JS_API=arguments 
                        -s INVOKE_RUN=1 
                        -s EXIT_RUNTIME=0
                        -s ENVIRONMENT=web 
                        -s MODULARIZE
                        )

    # This just make sure that the flags will be passed to the link process
    CVC5_CONFIGURE_ENV=(LDFLAGS="${EMCC_WASM_FLAGS[@]}")

    # These are the CVC5 configure flags
    CVC5_CONFIGURE_OPTS=(   
                            --static    # It's obligatory to compile statically
                            --static-binary
                            --no-tracing --no-assertions
                            --no-debug-symbols --no-unit-testing 
                            --name=${BUILD_NAME} --auto-download
                            --wasm=${EXTENSION} # Flag to sign whether will be a 
                                                # WebAssembly compilation and 
                                                # which extension will be used
                                                # (OFF, WASM, JS or HTML).
                        )
                        #  --no-poly)

    # Configure the CVC5
    cd ${CVC5_DIR}
    env "${CVC5_CONFIGURE_ENV[@]}" emconfigure ./configure.sh "${CVC5_CONFIGURE_OPTS[@]}"

echo ""
echo "-------------------------------"
echo "- Building CVC5"
echo "-------------------------------"

echo '   ---CVC5';
    cd ./${BUILD_NAME}
    emmake make -j${CORES_TO_COMPILE}